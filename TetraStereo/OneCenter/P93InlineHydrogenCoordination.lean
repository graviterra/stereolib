import TetraStereo.OneCenter.CIPP93NoncarbonTetrahedralNormalization
import TetraStereo.OneCenter.RawExpandedIntakeConstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace TetraStereo.OneCenter
namespace P93InlineHydrogenCoordination

open RawMolecule
open RawExpandedIntakeConstruction LocalizedRawGraphReadiness
open BlueBookP93.NoncarbonTetrahedra.Production

/-!
# P-93.2 inline/implicit hydrogen coordination: successor to the written-neighbour gate

This module is the honest successor of the predecessor module of the same name.  It targets the
repaired production core (`f76_p93_frozen_coordination_core_repair`, published core hash
`c504ec70…`), in which

```
effectiveOxoCenter? mol center =
  (mol.atomAt? center).any fun spec =>
    oxoCenterElement spec.element &&
      ((mol.writtenNeighbors center).length + spec.explicitHydrogens?.getD 0 == 4)
```

and the production wrapper `normalizeRawMoleculeP93` freezes the exact source hydrogen count
(`freezeSourceHydrogenCounts`) **before** the quotient.  Consequently the predecessor's
"production rejects the frozen fixtures" endpoints are no longer true statements about production:
on the frozen unbracketed fixture `P(=O)(C)(N)` the repaired gate counts `3 + 1 = 4` and accepts,
and the quotient rewrites the `P=O` edge to a single bond (bond order one).

What is preserved from the predecessor module:

* the actual parser images `pUnbracketedSource_parse`, `pInlineHydrogenSource_parse` and every
  executable admission/valence/mass/source-gate check (`decide +kernel` on the actual parser
  outputs);
* the generic coordination count `frozenCoordinationCount` and its freezing equation
  `writtenNeighbors.length + hydrogenCountAt`;
* the no-double-counting theorem on the hydrogen-expanded graph, where materialized source atoms
  store `explicitHydrogens? = some 0` and every hydrogen occurs once as a written vertex;
* the expanded-neighbour rows `[4, 1, 2, 3]` and physical coordination four.

What is replaced:

* `effectiveOxoCenterCalibrated?` (the predecessor's candidate gate) is now **definitionally the
  production gate**.  We do not introduce a second "candidate" gate; the generic count is proved to
  reproduce `Production.effectiveOxoCenter?` exactly.
* All predecessor endpoints asserting that *production* rejects the frozen fixtures are renamed.
  The old written-neighbour-only gate survives only as the explicitly named legacy witness
  `legacyWrittenNeighborGate`; it is not called current production anywhere in this module.
* The production-rejection endpoints become production-acceptance endpoints, `P=O` normalization to
  order one, source-hydrogen preservation through freeze and quotient, and the expanded
  four-coordination facts.

No declaration in this module is assumed.  Every scientific export is audited with
`assert_kernel_only`; the concrete parser and fixture values are computed by `decide +kernel` on
the actual parser images or derived from actual definitions.  No final CIP descriptor value is
claimed: the statements below are confined to parsing, admission, the production gate, the
normalized effective graph, source hydrogen counts, and hydrogen-expanded coordination.
-/

/-! ## The generic coordination count and the production gate -/

/-- Written neighbours plus the atom's stored hydrogen-policy count.

On an unfrozen source graph the stored policy is `some n` only for bracket atoms and `none` for
unbracketed organic-subset atoms, so the count is `written + inline` there.  On
`freezeSourceHydrogenCounts mol` the stored policy is the exact source hydrogen count, so the count
is `written + hydrogenCountAt`.  On `withExplicitHydrogens` the source atoms store `some 0` and the
hydrogens are vertices, so the count is the written-neighbour length alone. -/
def frozenCoordinationCount (mol : RawMolecule) (index : Nat) : Nat :=
  (mol.writtenNeighbors index).length +
    ((mol.atomAt? index).map (fun atom => atom.explicitHydrogens?.getD 0)).getD 0

/-- **The generic count is the production count.**  The repaired production gate is exactly the
element guard applied to `frozenCoordinationCount`.  This is the successor of the predecessor's
separate "candidate" gate: no alternative gate is needed, because the count reads the same
(written neighbours, stored hydrogen policy) pair as the production definition. -/
theorem effectiveOxoCenter?_eq_gate_with_frozenCoordinationCount
    (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? mol center =
      (mol.atomAt? center).any (fun spec =>
        oxoCenterElement spec.element &&
          (frozenCoordinationCount mol center == 4)) := by
  unfold effectiveOxoCenter? frozenCoordinationCount
  cases mol.atomAt? center <;> simp

/-- Independent proposition denoted by the production gate, expressed through the generic count. -/
theorem effectiveOxoCenter?_eq_true_iff_count (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? mol center = true ↔
      ∃ spec, mol.atomAt? center = some spec ∧
        oxoCenterElement spec.element = true ∧ frozenCoordinationCount mol center = 4 := by
  rw [effectiveOxoCenter?_eq_true_iff]
  constructor
  · rintro ⟨spec, lookup, element, count⟩
    exact ⟨spec, lookup, element,
      by simpa [frozenCoordinationCount, lookup] using count⟩
  · rintro ⟨spec, lookup, element, count⟩
    exact ⟨spec, lookup, element,
      by simpa [frozenCoordinationCount, lookup] using count⟩

/-! ## Freezing computes written neighbours plus the source hydrogen count -/

/-- **The calibration equation.**  On the frozen molecule, the coordination count is exactly the
written-neighbour count plus the exact *source* hydrogen count computed by `hydrogenCountAt`.
Freezing writes that source count into every atom's `explicitHydrogens?` policy, so the generic
count reads it back. -/
theorem frozenCoordinationCount_freezeSourceHydrogenCounts
    (mol : RawMolecule) (index : Nat) :
    frozenCoordinationCount (freezeSourceHydrogenCounts mol) index =
      (mol.writtenNeighbors index).length + mol.hydrogenCountAt index := by
  unfold frozenCoordinationCount
  rw [freezeSourceHydrogenCounts_writtenNeighbors, freezeSourceHydrogenCounts_atomAt?]
  cases observed : mol.atomAt? index with
  | none => simp [RawMolecule.hydrogenCountAt, observed]
  | some atom => simp

/-- The production gate on a source-hydrogen-frozen molecule, restated through the generic frozen
coordination count.  This is the direct successor of the predecessor's calibrated-candidate
characterization; it now speaks about the actual production predicate. -/
theorem effectiveOxoCenter?_freezeSourceHydrogenCounts_iff_count
    (mol : RawMolecule) (center : Nat) :
    effectiveOxoCenter? (freezeSourceHydrogenCounts mol) center = true ↔
      ∃ spec, mol.atomAt? center = some spec ∧
        oxoCenterElement spec.element = true ∧
          frozenCoordinationCount (freezeSourceHydrogenCounts mol) center = 4 := by
  rw [effectiveOxoCenter?_freezeSourceHydrogenCounts_iff]
  constructor
  · rintro ⟨spec, lookup, element, count⟩
    exact ⟨spec, lookup, element,
      by rw [frozenCoordinationCount_freezeSourceHydrogenCounts]; exact count⟩
  · rintro ⟨spec, lookup, element, count⟩
    exact ⟨spec, lookup, element,
      by rw [frozenCoordinationCount_freezeSourceHydrogenCounts] at count; exact count⟩

/-- Reusable production-gate acceptance lemma: a three-written-neighbour oxo center with one source
hydrogen is accepted on the frozen molecule because the repair counts `3 + 1 = 4`. -/
theorem effectiveOxoCenter?_freezeSourceHydrogenCounts_eq_true_of_written_three_hydrogen_one
    (mol : RawMolecule) (center : Nat) (spec : AtomSpec)
    (lookup : mol.atomAt? center = some spec)
    (element : oxoCenterElement spec.element = true)
    (written : (mol.writtenNeighbors center).length = 3)
    (hydrogen : mol.hydrogenCountAt center = 1) :
    effectiveOxoCenter? (freezeSourceHydrogenCounts mol) center = true :=
  (effectiveOxoCenter?_freezeSourceHydrogenCounts_iff mol center).mpr
    ⟨spec, lookup, element, by rw [written, hydrogen]⟩

/-- A center with three written neighbours and one *stored* hydrogen policy is accepted directly,
without a separate freezing step.  This is the bracket/inline-hydrogen case. -/
theorem effectiveOxoCenter?_eq_true_of_written_three_stored_one
    (mol : RawMolecule) (center : Nat) (spec : AtomSpec)
    (lookup : mol.atomAt? center = some spec)
    (element : oxoCenterElement spec.element = true)
    (written : (mol.writtenNeighbors center).length = 3)
    (stored : spec.explicitHydrogens? = some 1) :
    effectiveOxoCenter? mol center = true := by
  rw [effectiveOxoCenter?_eq_true_iff]
  refine ⟨spec, lookup, element, ?_⟩
  rw [written, stored]
  rfl

/-! ## Materialized atoms store zero: explicit H vertices are not counted twice -/

/-- A materialized source atom's stored hydrogen policy is `some 0`; its hydrogens are vertices. -/
@[simp] theorem explicitHydrogens?_materializedAtomSpec (atom : AtomSpec) :
    (materializedAtomSpec atom).explicitHydrogens?.getD 0 = 0 := rfl

/-- **No double counting.**  At a real source index of the expanded graph, the generic coordination
count is the written-neighbour length alone.  The inline/implied count has been consumed
(`explicitHydrogens? = some 0`) and each hydrogen now occurs exactly once, as a fresh vertex in
`writtenNeighbors`. -/
theorem frozenCoordinationCount_withExplicitHydrogens_of_lt
    (mol : RawMolecule) (index : Nat) (bound : index < mol.atomCount) :
    frozenCoordinationCount mol.withExplicitHydrogens index =
      (mol.withExplicitHydrogens.writtenNeighbors index).length := by
  unfold frozenCoordinationCount
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt mol.atoms index bound
  have source : mol.atomAt? index = some spec := by
    simpa [RawMolecule.atomAt?] using lookup
  rw [atomAt?_source_prefix mol index spec source]
  simp [RawMolecule.materializedAtomSpec]

/-- On the expanded graph the production gate degenerates to the written-neighbour test: every
materialized source atom stores `some 0`, and each hydrogen appears exactly once as a written
vertex. -/
theorem effectiveOxoCenter?_withExplicitHydrogens_eq_true_iff
    (mol : RawMolecule) (center : Nat) (bound : center < mol.atomCount) :
    effectiveOxoCenter? mol.withExplicitHydrogens center = true ↔
      ∃ spec, mol.withExplicitHydrogens.atomAt? center = some spec ∧
        oxoCenterElement spec.element = true ∧
          (mol.withExplicitHydrogens.writtenNeighbors center).length = 4 := by
  rw [effectiveOxoCenter?_eq_true_iff_count,
    frozenCoordinationCount_withExplicitHydrogens_of_lt mol center bound]















/-- The pre-repair written-neighbour-only center gate.  **Legacy witness, not current
production.** -/
def legacyWrittenNeighborGate (mol : RawMolecule) (center : Nat) : Bool :=
  (mol.atomAt? center).any fun spec =>
    oxoCenterElement spec.element && ((mol.writtenNeighbors center).length == 4)

/-- Characterization of the legacy gate: element guard plus four *written* neighbours. -/
theorem legacyWrittenNeighborGate_eq_true_iff
    (mol : RawMolecule) (center : Nat) :
    legacyWrittenNeighborGate mol center = true ↔
      ∃ spec, mol.atomAt? center = some spec ∧
        oxoCenterElement spec.element = true ∧
          (mol.writtenNeighbors center).length = 4 := by
  cases observed : mol.atomAt? center with
  | none => simp [legacyWrittenNeighborGate, observed]
  | some spec =>
      simp [legacyWrittenNeighborGate, observed, Bool.and_eq_true, beq_iff_eq]

/-! ## Actual parser fixture: unbracketed `P(=O)(C)(N)` -/

/-- Unbracketed OpenSMILES candidate whose phosphorus has three written neighbours and one implied
hydrogen. -/
def pUnbracketedSource : String := "P(=O)(C)(N)"

/-- Exact parser image of `pUnbracketedSource`: phosphorus at index `0` with an oxo double bond to
oxygen `1` and single bonds to carbon `2` and nitrogen `3`. -/
def pUnbracketedParsed : RawMolecule :=
  { atoms := [AtomSpec.aliphatic .P, AtomSpec.aliphatic .O,
      AtomSpec.aliphatic .C, AtomSpec.aliphatic .N]
    bonds := [{ source := 0, target := 1, kind := .double },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single }]
    neighborOrder := [[1, 2, 3], [0], [0], [0]]
    introductionPredecessors := [none, some 0, some 0, some 0] }

/-- Kernel-checked actual parse: the production parser returns exactly `pUnbracketedParsed`. -/
theorem pUnbracketedSource_parse :
    parseOpenSMILES pUnbracketedSource = .ok pUnbracketedParsed := by rfl

/-- All executable admission, valence, mass, and provenance checks of the actual parser image. -/
theorem pUnbracketedSource_checks :
    pUnbracketedParsed.admissible? = true ∧
      pUnbracketedParsed.stereochemicalAdmissible? = true ∧
        pUnbracketedParsed.valenceOK? = true ∧
          pUnbracketedParsed.rule2MassesKnown? = true ∧
            pUnbracketedParsed.introductionPredecessorsValid? = true ∧
              pUnbracketedParsed.parserIntroductionValid? = true := by
  decide +kernel

/-- Structural admission of the actual fixture, derived from the executable admission check. -/
theorem pUnbracketedSource_admissible : pUnbracketedParsed.Admissible :=
  (RawMolecule.admissible?_eq_true_iff _).mp pUnbracketedSource_checks.1

/-- Well-formedness of the actual fixture, derived from admission. -/
theorem pUnbracketedSource_wellFormed : pUnbracketedParsed.WellFormed :=
  pUnbracketedSource_admissible.1

/-- Stereochemical admission of the actual fixture, derived from the executable check. -/
theorem pUnbracketedSource_stereochemicalAdmissible :
    pUnbracketedParsed.StereochemicalAdmissible :=
  (RawMolecule.stereochemicalAdmissible?_eq_true_iff _).mp pUnbracketedSource_checks.2.1

/-- The actual fixture passes the production valence table, derived from the executable check. -/
theorem pUnbracketedSource_valenceOK : pUnbracketedParsed.ValenceOK :=
  (RawMolecule.valenceOK?_eq_true_iff _).mp pUnbracketedSource_checks.2.2.1

/-- The actual fixture has source-backed Rule-2 masses, derived from the executable check. -/
theorem pUnbracketedSource_rule2MassesKnown : pUnbracketedParsed.Rule2MassesKnown :=
  (RawMolecule.rule2MassesKnown?_eq_true_iff _).mp pUnbracketedSource_checks.2.2.2.1

/-- The actual fixture passes the localized source gate used by the expanded-intake construction. -/
theorem pUnbracketedSource_rawReady :
    RawLocalizedGraphSourceReady pUnbracketedParsed :=
  (rawLocalizedGraphSourceReady?_eq_true_iff pUnbracketedParsed).mp (by decide +kernel)

/-! ### Coordination counts and the repaired production gate -/

/-- Phosphorus has exactly three written neighbours. -/
theorem pUnbracketedSource_writtenNeighbors :
    pUnbracketedParsed.writtenNeighbors 0 = [1, 2, 3] := by decide +kernel

/-- The unbracketed phosphorus stores no explicit policy; its single hydrogen is implied. -/
theorem pUnbracketedSource_hydrogenCount :
    pUnbracketedParsed.hydrogenCountAt 0 = 1 := by decide +kernel

/-- On the *unfrozen* parsed graph the generic count sees only the three written neighbours: the
implied hydrogen is not yet stored in `explicitHydrogens?`. -/
theorem pUnbracketedSource_unfrozenCoordination :
    frozenCoordinationCount pUnbracketedParsed 0 = 3 := by decide +kernel

/-- The repaired production gate rejects the unfrozen source: `3 + 0 = 3`.  This is the genuine
calibration boundary of the repair, not a production-pipeline claim, because the production wrapper
freezes first. -/
theorem pUnbracketedSource_unfrozenProductionGate :
    effectiveOxoCenter? pUnbracketedParsed 0 = false := by decide +kernel

/-- Production's valence accounting at unbracketed phosphorus: bond-order sum four with no stored
hydrogens. -/
theorem pUnbracketedSource_usedValence :
    pUnbracketedParsed.usedValenceAt 0 = 4 := by decide +kernel

/-- Freezing stores the source hydrogen count `1` at phosphorus. -/
theorem pUnbracketedSource_frozenStoredHydrogen :
    ((freezeSourceHydrogenCounts pUnbracketedParsed).atomAt? 0).bind
      AtomSpec.explicitHydrogens? = some 1 := by
  decide +kernel

/-- Freezing preserves the source hydrogen count. -/
theorem pUnbracketedSource_frozenHydrogenCount :
    (freezeSourceHydrogenCounts pUnbracketedParsed).hydrogenCountAt 0 = 1 := by
  rw [freezeSourceHydrogenCounts_hydrogenCountAt, pUnbracketedSource_hydrogenCount]

/-- After freezing, the generic coordination count at phosphorus is `3 + 1 = 4`. -/
theorem pUnbracketedSource_frozenCoordination :
    frozenCoordinationCount (freezeSourceHydrogenCounts pUnbracketedParsed) 0 = 4 := by
  rw [frozenCoordinationCount_freezeSourceHydrogenCounts]
  rw [pUnbracketedSource_writtenNeighbors, pUnbracketedSource_hydrogenCount]
  rfl

/-- **Actual production gate acceptance.**  On the frozen molecule that the production wrapper
consumes, the repaired production gate accepts the actual unbracketed fixture. -/
theorem pUnbracketedSource_productionGate_frozen :
    effectiveOxoCenter? (freezeSourceHydrogenCounts pUnbracketedParsed) 0 = true :=
  effectiveOxoCenter?_freezeSourceHydrogenCounts_eq_true_of_written_three_hydrogen_one
    pUnbracketedParsed 0 (AtomSpec.aliphatic .P) rfl rfl
    (by decide +kernel) (by decide +kernel)

/-- The source-frozen gate is governed by the generic frozen coordination count. -/
theorem pUnbracketedSource_frozenGate_iff_coordination :
    effectiveOxoCenter? (freezeSourceHydrogenCounts pUnbracketedParsed) 0 = true ↔
      frozenCoordinationCount (freezeSourceHydrogenCounts pUnbracketedParsed) 0 = 4 := by
  rw [effectiveOxoCenter?_freezeSourceHydrogenCounts_iff_count]
  constructor
  · rintro ⟨_spec, _lookup, _element, count⟩
    exact count
  · intro count
    exact ⟨AtomSpec.aliphatic .P, rfl, rfl, count⟩

/-! ### The `P=O` edge is normalized to bond order one -/

/-- On the frozen fixture the `0 = 1` edge is an effective P-93.2 oxo edge under the repaired
production gate. -/
theorem pUnbracketedSource_effectiveOxoBond :
    effectiveOxoBond? (freezeSourceHydrogenCounts pUnbracketedParsed)
      { source := 0, target := 1, kind := .double } = true := by
  decide +kernel

/-- The production quotient rewrites the `P=O` edge kind to single. -/
theorem pUnbracketedSource_normalizeBond_kind :
    (normalizeBond (freezeSourceHydrogenCounts pUnbracketedParsed)
      { source := 0, target := 1, kind := .double }).kind = .single :=
  normalizeBond_kind_eq_single_of_effective
    (freezeSourceHydrogenCounts pUnbracketedParsed)
    { source := 0, target := 1, kind := .double }
    ((effectiveOxoBond?_eq_true_iff
      (freezeSourceHydrogenCounts pUnbracketedParsed)
      { source := 0, target := 1, kind := .double }).mp
      pUnbracketedSource_effectiveOxoBond)

/-- **Observable production quotient.**  The normalized effective graph now has bond order one on
the phosphorus--oxygen edge, the successor of the predecessor's (now false) order-two claim. -/
theorem pUnbracketedSource_productionQuotient_bondOrder :
    (normalize (freezeSourceHydrogenCounts pUnbracketedParsed)).bondOrder 0 1 = 1 := by
  decide +kernel

/-! ### Source hydrogen preservation through freeze and quotient -/

/-- The normalized frozen quotient keeps the exact source hydrogen count at phosphorus. -/
theorem pUnbracketedSource_normalizedHydrogenCount :
    (normalize (freezeSourceHydrogenCounts pUnbracketedParsed)).hydrogenCountAt 0 = 1 := by
  rw [normalize_freezeSourceHydrogenCounts_hydrogenCountAt,
    pUnbracketedSource_hydrogenCount]

/-- The normalized quotient also stores the frozen source policy unchanged. -/
theorem pUnbracketedSource_normalizedStoredHydrogen :
    ((normalize (freezeSourceHydrogenCounts pUnbracketedParsed)).atomAt? 0).bind
      AtomSpec.explicitHydrogens? = some 1 := by
  decide +kernel

/-! ### Expanded physical coordination -/

/-- The expanded graph puts the materialized hydrogen first in phosphorus's written row, exactly
the OpenSMILES convention for a component-initial atom. -/
theorem pUnbracketedSource_expandedRow :
    pUnbracketedParsed.withExplicitHydrogens.writtenNeighbors 0 = [4, 1, 2, 3] := by
  decide +kernel

/-- Physical coordination of phosphorus on the expanded graph is four: three written heavy
neighbours plus the materialized hydrogen vertex. -/
theorem pUnbracketedSource_expandedCoordination :
    (pUnbracketedParsed.withExplicitHydrogens.writtenNeighbors 0).length = 4 := by
  rw [pUnbracketedSource_expandedRow]
  rfl

/-- The expanded graph's written-neighbour view is exact, so the row length is the physical
coordination count. -/
theorem pUnbracketedSource_expandedExact :
    pUnbracketedParsed.withExplicitHydrogens.WrittenNeighborExact :=
  withExplicitHydrogens_writtenNeighborExact pUnbracketedParsed

/-- On the expanded graph the generic count equals the expanded written-neighbour length: the
inline/implied count is consumed and the hydrogen vertex is counted once. -/
theorem pUnbracketedSource_expandedCoordinationCount :
    frozenCoordinationCount pUnbracketedParsed.withExplicitHydrogens 0 = 4 := by
  rw [frozenCoordinationCount_withExplicitHydrogens_of_lt pUnbracketedParsed 0
    (by decide +kernel)]
  exact pUnbracketedSource_expandedCoordination

/-- The repaired production gate also accepts the fully hydrogen-expanded graph: four written
neighbours, all hydrogens materialized, no residual stored count. -/
theorem pUnbracketedSource_expandedProductionGate :
    effectiveOxoCenter? pUnbracketedParsed.withExplicitHydrogens 0 = true :=
  (effectiveOxoCenter?_withExplicitHydrogens_eq_true_iff pUnbracketedParsed 0
    (by decide +kernel)).mpr
    ⟨materializedAtomSpec (AtomSpec.aliphatic .P),
      atomAt?_source_prefix pUnbracketedParsed 0 (AtomSpec.aliphatic .P) rfl,
      rfl,
      by rw [pUnbracketedSource_expandedRow]; rfl⟩

/-! ### Legacy bug witness on the frozen fixture

These statements describe the pre-repair written-neighbour-only gate.  They are **not** current
production facts. -/

/-- The legacy written-neighbour gate rejects the frozen unbracketed fixture (three written
neighbours). -/
theorem pUnbracketedSource_legacyGate_frozen :
    legacyWrittenNeighborGate (freezeSourceHydrogenCounts pUnbracketedParsed) 0 = false := by
  decide +kernel

/-! ## Actual parser fixture: stereochemical inline `[P@H](=O)(C)N` -/

/-- OpenSMILES candidate with the same one hydrogen written as a bracket (inline) count and an
explicit tetrahedral annotation. -/
def pInlineHydrogenSource : String := "[P@H](=O)(C)N"

/-- The inline phosphorus atom of the actual fixture: one bracket hydrogen and the parsed `@`
annotation. -/
def inlinePhosphorusSpec : AtomSpec :=
  { element := .P, explicitHydrogens? := some 1,
      tetrahedral? := some .anticlockwise }

/-- Exact parser image of `pInlineHydrogenSource`.  `[P@H]` is a bracket atom: the hydrogen is an
inline count `some 1`, not a vertex, and `@` records anticlockwise input parity. -/
def pInlineHydrogenParsed : RawMolecule :=
  { atoms := [inlinePhosphorusSpec,
              AtomSpec.aliphatic .O, AtomSpec.aliphatic .C, AtomSpec.aliphatic .N]
    bonds := [{ source := 0, target := 1, kind := .double },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single }]
    neighborOrder := [[1, 2, 3], [0], [0], [0]]
    introductionPredecessors := [none, some 0, some 0, some 0] }

/-- Kernel-checked actual parse of the inline-hydrogen candidate. -/
theorem pInlineHydrogenSource_parse :
    parseOpenSMILES pInlineHydrogenSource = .ok pInlineHydrogenParsed := by rfl

/-- All executable admission, valence, mass, and provenance checks of the actual inline fixture.
In particular `valenceOK? = true`: the parser's permitted phosphorus valence five covers the
four bond orders plus the one written hydrogen. -/
theorem pInlineHydrogenSource_checks :
    pInlineHydrogenParsed.admissible? = true ∧
      pInlineHydrogenParsed.stereochemicalAdmissible? = true ∧
        pInlineHydrogenParsed.valenceOK? = true ∧
          pInlineHydrogenParsed.rule2MassesKnown? = true ∧
            pInlineHydrogenParsed.introductionPredecessorsValid? = true ∧
              pInlineHydrogenParsed.parserIntroductionValid? = true := by
  decide +kernel

/-- Structural admission of the inline fixture, derived from the executable admission check. -/
theorem pInlineHydrogenSource_admissible : pInlineHydrogenParsed.Admissible :=
  (RawMolecule.admissible?_eq_true_iff _).mp pInlineHydrogenSource_checks.1

/-- Well-formedness of the inline fixture, derived from admission. -/
theorem pInlineHydrogenSource_wellFormed : pInlineHydrogenParsed.WellFormed :=
  pInlineHydrogenSource_admissible.1

/-- Stereochemical admission of the inline fixture. -/
theorem pInlineHydrogenSource_stereochemicalAdmissible :
    pInlineHydrogenParsed.StereochemicalAdmissible :=
  (RawMolecule.stereochemicalAdmissible?_eq_true_iff _).mp pInlineHydrogenSource_checks.2.1

/-- The inline fixture passes the production valence table. -/
theorem pInlineHydrogenSource_valenceOK : pInlineHydrogenParsed.ValenceOK :=
  (RawMolecule.valenceOK?_eq_true_iff _).mp pInlineHydrogenSource_checks.2.2.1

/-- The inline fixture's Rule-2 masses are source-backed. -/
theorem pInlineHydrogenSource_rule2MassesKnown :
    pInlineHydrogenParsed.Rule2MassesKnown :=
  (RawMolecule.rule2MassesKnown?_eq_true_iff _).mp pInlineHydrogenSource_checks.2.2.2.1

/-- The inline fixture passes the localized source gate. -/
theorem pInlineHydrogenSource_rawReady :
    RawLocalizedGraphSourceReady pInlineHydrogenParsed :=
  (rawLocalizedGraphSourceReady?_eq_true_iff pInlineHydrogenParsed).mp (by decide +kernel)

/-- The inline atom stores exactly one hydrogen in its bracket policy. -/
theorem pInlineHydrogenSource_storedHydrogen :
    (pInlineHydrogenParsed.atomAt? 0).bind AtomSpec.explicitHydrogens? = some 1 := by
  decide +kernel

/-- Phosphorus has three written neighbours in the inline fixture as well. -/
theorem pInlineHydrogenSource_writtenNeighbors :
    pInlineHydrogenParsed.writtenNeighbors 0 = [1, 2, 3] := by decide +kernel

/-- The inline source hydrogen count is one. -/
theorem pInlineHydrogenSource_hydrogenCount :
    pInlineHydrogenParsed.hydrogenCountAt 0 = 1 := by decide +kernel

/-- Production's valence accounting at inline phosphorus: one stored hydrogen plus bond-order sum
four. -/
theorem pInlineHydrogenSource_usedValence :
    pInlineHydrogenParsed.usedValenceAt 0 = 5 := by decide +kernel

/-- On the unfrozen inline fixture the generic count is already four: `3 + 1`. -/
theorem pInlineHydrogenSource_unfrozenCoordination :
    frozenCoordinationCount pInlineHydrogenParsed 0 = 4 := by decide +kernel

/-- **Actual production gate acceptance without freezing.**  The bracket hydrogen is stored in the
parser output, so the repaired gate accepts the inline fixture directly.  This replaces the
predecessor's now-false inline rejection endpoint. -/
theorem pInlineHydrogenSource_productionGate_unfrozen :
    effectiveOxoCenter? pInlineHydrogenParsed 0 = true :=
  effectiveOxoCenter?_eq_true_of_written_three_stored_one
    pInlineHydrogenParsed 0 inlinePhosphorusSpec rfl rfl
    (by decide +kernel) rfl

/-- Freezing stores the same source hydrogen count `1`. -/
theorem pInlineHydrogenSource_frozenStoredHydrogen :
    ((freezeSourceHydrogenCounts pInlineHydrogenParsed).atomAt? 0).bind
      AtomSpec.explicitHydrogens? = some 1 := by
  decide +kernel

/-- Freezing preserves the inline source hydrogen count. -/
theorem pInlineHydrogenSource_frozenHydrogenCount :
    (freezeSourceHydrogenCounts pInlineHydrogenParsed).hydrogenCountAt 0 = 1 := by
  rw [freezeSourceHydrogenCounts_hydrogenCountAt, pInlineHydrogenSource_hydrogenCount]

/-- On the frozen inline fixture the generic coordination count is four. -/
theorem pInlineHydrogenSource_frozenCoordination :
    frozenCoordinationCount (freezeSourceHydrogenCounts pInlineHydrogenParsed) 0 = 4 := by
  rw [frozenCoordinationCount_freezeSourceHydrogenCounts]
  rw [pInlineHydrogenSource_writtenNeighbors, pInlineHydrogenSource_hydrogenCount]
  rfl

/-- **Actual production gate acceptance on the frozen inline fixture.** -/
theorem pInlineHydrogenSource_productionGate_frozen :
    effectiveOxoCenter? (freezeSourceHydrogenCounts pInlineHydrogenParsed) 0 = true :=
  effectiveOxoCenter?_freezeSourceHydrogenCounts_eq_true_of_written_three_hydrogen_one
    pInlineHydrogenParsed 0 inlinePhosphorusSpec rfl rfl
    (by decide +kernel) (by decide +kernel)

/-- On the frozen inline fixture the gate is governed by the generic frozen count. -/
theorem pInlineHydrogenSource_frozenGate_iff_coordination :
    effectiveOxoCenter? (freezeSourceHydrogenCounts pInlineHydrogenParsed) 0 = true ↔
      frozenCoordinationCount (freezeSourceHydrogenCounts pInlineHydrogenParsed) 0 = 4 := by
  rw [effectiveOxoCenter?_freezeSourceHydrogenCounts_iff_count]
  constructor
  · rintro ⟨_spec, _lookup, _element, count⟩
    exact count
  · intro count
    exact ⟨inlinePhosphorusSpec, rfl, rfl, count⟩

/-! ### The inline `P=O` edge is normalized to bond order one -/

/-- On the frozen inline fixture the `0 = 1` edge is an effective P-93.2 oxo edge under the
repaired production gate. -/
theorem pInlineHydrogenSource_effectiveOxoBond :
    effectiveOxoBond? (freezeSourceHydrogenCounts pInlineHydrogenParsed)
      { source := 0, target := 1, kind := .double } = true := by
  decide +kernel

/-- The production quotient rewrites the inline `P=O` edge kind to single. -/
theorem pInlineHydrogenSource_normalizeBond_kind :
    (normalizeBond (freezeSourceHydrogenCounts pInlineHydrogenParsed)
      { source := 0, target := 1, kind := .double }).kind = .single :=
  normalizeBond_kind_eq_single_of_effective
    (freezeSourceHydrogenCounts pInlineHydrogenParsed)
    { source := 0, target := 1, kind := .double }
    ((effectiveOxoBond?_eq_true_iff
      (freezeSourceHydrogenCounts pInlineHydrogenParsed)
      { source := 0, target := 1, kind := .double }).mp
      pInlineHydrogenSource_effectiveOxoBond)

/-- The normalized inline effective graph has bond order one on the phosphorus--oxygen edge. -/
theorem pInlineHydrogenSource_productionQuotient_bondOrder :
    (normalize (freezeSourceHydrogenCounts pInlineHydrogenParsed)).bondOrder 0 1 = 1 := by
  decide +kernel

/-! ### Source hydrogen preservation and no double counting for the inline fixture -/

/-- The normalized frozen quotient keeps the inline source hydrogen count. -/
theorem pInlineHydrogenSource_normalizedHydrogenCount :
    (normalize (freezeSourceHydrogenCounts pInlineHydrogenParsed)).hydrogenCountAt 0 = 1 := by
  rw [normalize_freezeSourceHydrogenCounts_hydrogenCountAt,
    pInlineHydrogenSource_hydrogenCount]

/-- The normalized quotient stores the frozen inline policy unchanged. -/
theorem pInlineHydrogenSource_normalizedStoredHydrogen :
    ((normalize (freezeSourceHydrogenCounts pInlineHydrogenParsed)).atomAt? 0).bind
      AtomSpec.explicitHydrogens? = some 1 := by
  decide +kernel

/-- The inline hydrogen is materialized as a vertex at index `4`. -/
theorem pInlineHydrogenSource_expandedRow :
    pInlineHydrogenParsed.withExplicitHydrogens.writtenNeighbors 0 = [4, 1, 2, 3] := by
  decide +kernel

/-- Physical coordination on the expanded inline graph is four. -/
theorem pInlineHydrogenSource_expandedCoordination :
    (pInlineHydrogenParsed.withExplicitHydrogens.writtenNeighbors 0).length = 4 := by
  rw [pInlineHydrogenSource_expandedRow]
  rfl

/-- The expanded inline source atom stores `some 0`: the inline count has been consumed and is now
represented by the hydrogen vertex. -/
theorem pInlineHydrogenSource_expandedFieldZero :
    (pInlineHydrogenParsed.withExplicitHydrogens.atomAt? 0).bind
      AtomSpec.explicitHydrogens? = some 0 := by
  decide +kernel

/-- **No double counting, concretely.**  The inline source stores one hydrogen and has three
written neighbours (`1 + 3 = 4`); after expansion the source atom stores zero and the same hydrogen
is a fourth written neighbour (`0 + 4 = 4`). -/
theorem pInlineHydrogenSource_noDoubleCounting :
    (pInlineHydrogenParsed.atomAt? 0).bind AtomSpec.explicitHydrogens? = some 1 ∧
      (pInlineHydrogenParsed.withExplicitHydrogens.atomAt? 0).bind
        AtomSpec.explicitHydrogens? = some 0 ∧
        (pInlineHydrogenParsed.withExplicitHydrogens.writtenNeighbors 0).length = 4 :=
  ⟨pInlineHydrogenSource_storedHydrogen, pInlineHydrogenSource_expandedFieldZero,
    pInlineHydrogenSource_expandedCoordination⟩

/-- The expanded inline graph's written-neighbour view is exact. -/
theorem pInlineHydrogenSource_expandedExact :
    pInlineHydrogenParsed.withExplicitHydrogens.WrittenNeighborExact :=
  withExplicitHydrogens_writtenNeighborExact pInlineHydrogenParsed

/-- On the expanded inline graph the generic count is the expanded written-neighbour length. -/
theorem pInlineHydrogenSource_expandedCoordinationCount :
    frozenCoordinationCount pInlineHydrogenParsed.withExplicitHydrogens 0 = 4 := by
  rw [frozenCoordinationCount_withExplicitHydrogens_of_lt pInlineHydrogenParsed 0
    (by decide +kernel)]
  exact pInlineHydrogenSource_expandedCoordination

/-- The repaired production gate accepts the fully expanded inline graph. -/
theorem pInlineHydrogenSource_expandedProductionGate :
    effectiveOxoCenter? pInlineHydrogenParsed.withExplicitHydrogens 0 = true :=
  (effectiveOxoCenter?_withExplicitHydrogens_eq_true_iff pInlineHydrogenParsed 0
    (by decide +kernel)).mpr
    ⟨materializedAtomSpec inlinePhosphorusSpec,
      atomAt?_source_prefix pInlineHydrogenParsed 0 inlinePhosphorusSpec rfl,
      rfl,
      by rw [pInlineHydrogenSource_expandedRow]; rfl⟩

/-! ### Legacy bug witness on the inline fixture

The pre-repair written-neighbour-only gate rejected both the unfrozen and the frozen inline
fixture.  These are legacy-witness facts, not current production facts. -/

/-- The legacy written-neighbour gate rejects the unfrozen inline fixture (three written
neighbours). -/
theorem pInlineHydrogenSource_legacyGate_unfrozen :
    legacyWrittenNeighborGate pInlineHydrogenParsed 0 = false := by
  decide +kernel

/-- The legacy written-neighbour gate rejects the frozen inline fixture as well. -/
theorem pInlineHydrogenSource_legacyGate_frozen :
    legacyWrittenNeighborGate (freezeSourceHydrogenCounts pInlineHydrogenParsed) 0 = false := by
  decide +kernel

/-! ## Summary theorem -/

/-- Production-semantics summary for both actual parser fixtures under the repaired core:
the production wrapper freezes the source hydrogen count; the frozen gate accepts both;
the quotient lowers `P=O` to bond order one; the source hydrogen count is preserved; and the
expanded graph has four physical coordination atoms at phosphorus.  No final descriptor value is
asserted. -/
theorem actual_fixtures_production_semantics :
    (pUnbracketedParsed.hydrogenCountAt 0 = 1 ∧
      effectiveOxoCenter? pUnbracketedParsed 0 = false ∧
        effectiveOxoCenter? (freezeSourceHydrogenCounts pUnbracketedParsed) 0 = true ∧
          (normalize (freezeSourceHydrogenCounts pUnbracketedParsed)).bondOrder 0 1 = 1 ∧
            (normalize (freezeSourceHydrogenCounts pUnbracketedParsed)).hydrogenCountAt 0 = 1 ∧
              (pUnbracketedParsed.withExplicitHydrogens.writtenNeighbors 0).length = 4) ∧
      (pInlineHydrogenParsed.hydrogenCountAt 0 = 1 ∧
        effectiveOxoCenter? pInlineHydrogenParsed 0 = true ∧
          effectiveOxoCenter? (freezeSourceHydrogenCounts pInlineHydrogenParsed) 0 = true ∧
            (normalize (freezeSourceHydrogenCounts pInlineHydrogenParsed)).bondOrder 0 1 = 1 ∧
              (normalize (freezeSourceHydrogenCounts pInlineHydrogenParsed)).hydrogenCountAt 0 = 1 ∧
                (pInlineHydrogenParsed.withExplicitHydrogens.writtenNeighbors 0).length = 4) :=
  ⟨⟨pUnbracketedSource_hydrogenCount, pUnbracketedSource_unfrozenProductionGate,
      pUnbracketedSource_productionGate_frozen,
      pUnbracketedSource_productionQuotient_bondOrder,
      pUnbracketedSource_normalizedHydrogenCount,
      pUnbracketedSource_expandedCoordination⟩,
    ⟨pInlineHydrogenSource_hydrogenCount, pInlineHydrogenSource_productionGate_unfrozen,
      pInlineHydrogenSource_productionGate_frozen,
      pInlineHydrogenSource_productionQuotient_bondOrder,
      pInlineHydrogenSource_normalizedHydrogenCount,
      pInlineHydrogenSource_expandedCoordination⟩⟩

/-! ## Kernel-authority guards -/

assert_kernel_only effectiveOxoCenter?_eq_gate_with_frozenCoordinationCount
assert_kernel_only effectiveOxoCenter?_eq_true_iff_count
assert_kernel_only frozenCoordinationCount_freezeSourceHydrogenCounts
assert_kernel_only effectiveOxoCenter?_freezeSourceHydrogenCounts_iff_count
assert_kernel_only effectiveOxoCenter?_freezeSourceHydrogenCounts_eq_true_of_written_three_hydrogen_one
assert_kernel_only effectiveOxoCenter?_eq_true_of_written_three_stored_one
assert_kernel_only explicitHydrogens?_materializedAtomSpec
assert_kernel_only frozenCoordinationCount_withExplicitHydrogens_of_lt
assert_kernel_only effectiveOxoCenter?_withExplicitHydrogens_eq_true_iff
assert_kernel_only legacyWrittenNeighborGate_eq_true_iff
assert_kernel_only pUnbracketedSource_parse
assert_kernel_only pUnbracketedSource_checks
assert_kernel_only pUnbracketedSource_admissible
assert_kernel_only pUnbracketedSource_wellFormed
assert_kernel_only pUnbracketedSource_stereochemicalAdmissible
assert_kernel_only pUnbracketedSource_valenceOK
assert_kernel_only pUnbracketedSource_rule2MassesKnown
assert_kernel_only pUnbracketedSource_rawReady
assert_kernel_only pUnbracketedSource_writtenNeighbors
assert_kernel_only pUnbracketedSource_hydrogenCount
assert_kernel_only pUnbracketedSource_unfrozenCoordination
assert_kernel_only pUnbracketedSource_unfrozenProductionGate
assert_kernel_only pUnbracketedSource_usedValence
assert_kernel_only pUnbracketedSource_frozenStoredHydrogen
assert_kernel_only pUnbracketedSource_frozenHydrogenCount
assert_kernel_only pUnbracketedSource_frozenCoordination
assert_kernel_only pUnbracketedSource_productionGate_frozen
assert_kernel_only pUnbracketedSource_frozenGate_iff_coordination
assert_kernel_only pUnbracketedSource_effectiveOxoBond
assert_kernel_only pUnbracketedSource_normalizeBond_kind
assert_kernel_only pUnbracketedSource_productionQuotient_bondOrder
assert_kernel_only pUnbracketedSource_normalizedHydrogenCount
assert_kernel_only pUnbracketedSource_normalizedStoredHydrogen
assert_kernel_only pUnbracketedSource_expandedRow
assert_kernel_only pUnbracketedSource_expandedCoordination
assert_kernel_only pUnbracketedSource_expandedExact
assert_kernel_only pUnbracketedSource_expandedCoordinationCount
assert_kernel_only pUnbracketedSource_expandedProductionGate
assert_kernel_only pUnbracketedSource_legacyGate_frozen
assert_kernel_only pInlineHydrogenSource_parse
assert_kernel_only pInlineHydrogenSource_checks
assert_kernel_only pInlineHydrogenSource_admissible
assert_kernel_only pInlineHydrogenSource_wellFormed
assert_kernel_only pInlineHydrogenSource_stereochemicalAdmissible
assert_kernel_only pInlineHydrogenSource_valenceOK
assert_kernel_only pInlineHydrogenSource_rule2MassesKnown
assert_kernel_only pInlineHydrogenSource_rawReady
assert_kernel_only pInlineHydrogenSource_storedHydrogen
assert_kernel_only pInlineHydrogenSource_writtenNeighbors
assert_kernel_only pInlineHydrogenSource_hydrogenCount
assert_kernel_only pInlineHydrogenSource_usedValence
assert_kernel_only pInlineHydrogenSource_unfrozenCoordination
assert_kernel_only pInlineHydrogenSource_productionGate_unfrozen
assert_kernel_only pInlineHydrogenSource_frozenStoredHydrogen
assert_kernel_only pInlineHydrogenSource_frozenHydrogenCount
assert_kernel_only pInlineHydrogenSource_frozenCoordination
assert_kernel_only pInlineHydrogenSource_productionGate_frozen
assert_kernel_only pInlineHydrogenSource_frozenGate_iff_coordination
assert_kernel_only pInlineHydrogenSource_effectiveOxoBond
assert_kernel_only pInlineHydrogenSource_normalizeBond_kind
assert_kernel_only pInlineHydrogenSource_productionQuotient_bondOrder
assert_kernel_only pInlineHydrogenSource_normalizedHydrogenCount
assert_kernel_only pInlineHydrogenSource_normalizedStoredHydrogen
assert_kernel_only pInlineHydrogenSource_expandedRow
assert_kernel_only pInlineHydrogenSource_expandedCoordination
assert_kernel_only pInlineHydrogenSource_expandedFieldZero
assert_kernel_only pInlineHydrogenSource_noDoubleCounting
assert_kernel_only pInlineHydrogenSource_expandedExact
assert_kernel_only pInlineHydrogenSource_expandedCoordinationCount
assert_kernel_only pInlineHydrogenSource_expandedProductionGate
assert_kernel_only pInlineHydrogenSource_legacyGate_unfrozen
assert_kernel_only pInlineHydrogenSource_legacyGate_frozen
assert_kernel_only actual_fixtures_production_semantics

end P93InlineHydrogenCoordination
end TetraStereo.OneCenter
