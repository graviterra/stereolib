/-
  ActualEligibleParentParityVariant

  The actual finite eligible auxiliary-center parity variant proposed in
  `tmp/chemical-fidelity-20261020/discovery-exports/f111_eligible_parent_source_fidelity_discovery`.

  The existing compiled fixture (`ConstitutionalRootStageAvailability`, also consumed by
  `RawAuxiliaryAvailabilitySemantics`) is the actual homochiral molecule

      C[C@@H](Cl)[C@@H]([C@H](Cl)C)Br

  whose central carbon C0 (parser atom 3) is eligible, has a Rule-1a tie between its two real
  carbon arms, and receives different original-root/framed auxiliary labels, but whose two arm
  descriptors are equal.  This module constructs the *indexed* one-parity variant: exactly atom 4
  of the existing `sourceAtoms` changes from `anticlockwise` to `clockwise`; every bond,
  written-neighbour row and introduction predecessor is unchanged.  The explicit atom list is
  used, not a supplied cut or a hand-chosen key.

  Everything below is computed by the repository's actual parser/materialization/occurrence
  pipeline.  Parser success, production eligibility, the generated official frame, the actual
  Rule-1a arm tie, the actual discovered auxiliary states, and the C2- and C0-rooted outputs are
  all kernel-checked equations (`rfl`/`decide`).  No R/S label or uppercase flag is assumed; each
  fact definition is the value returned by the executable pipeline.

  A true full-parity-reflected control flips all three tetrahedral markers.  Its actual computed
  outputs are proved separately; only *after* both successful C0-rooted computations do we state
  the mirror invariance of the computed (descriptor, uppercase) pair.  The module does not emit a
  lowercase `r`/`s` letter: the pipeline returns a base `RS` descriptor plus the `uppercase` flag,
  and the report keeps that distinction explicit.

  No production declaration is modified.  Every export is guarded by `assert_kernel_only`.
-/

import TetraStereo.OneCenter.ConstitutionalRootStageAvailability
import TetraStereo.OneCenter.Pseudoasymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace ActualEligibleParentParityVariant

open RawMolecule
open ConstitutionalRootStageAvailability

/-! ## 1. Explicit indexed source A and its parser success -/

/-- Variant A: the existing fixture string with atom 4's bracket marker flipped (`@` to `@@`).
Under this repository's convention (`@@ ↦ clockwise`, `@ ↦ anticlockwise`) atom 4 changes from
`anticlockwise` to `clockwise`; atoms 0--3 and 5--7 are textually unchanged. -/
def smilesA : String := "C[C@@H](Cl)[C@@H]([C@@H](Cl)C)Br"

/-- The explicit indexed source A: the existing actual fixture atoms with index 4 changed from
`stereoC anticlockwise` to `stereoC clockwise`.  Bonds, written-neighbour order and introduction
predecessors are taken from the existing fixture unchanged (there is no new atom or bond). -/
def sourceA : RawMolecule :=
  { atoms :=
      [ methylC
      , stereoC TetrahedralInputParity.clockwise
      , plainCl
      , stereoC TetrahedralInputParity.clockwise
      , stereoC TetrahedralInputParity.clockwise
      , plainCl
      , methylC
      , plainBr ]
    bonds := sourceBonds
    neighborOrder := sourceNeighborOrder
    introductionPredecessors := sourceIntro }

/-- The production materialization actually consumed by the occurrence pipeline. -/
def molA : RawMolecule := sourceA.withExplicitHydrogens

/-- The same fuel as the existing fixture. -/
def fuelA : ℕ := 8

/-- The parser accepts the variant string and returns exactly the indexed source A. -/
theorem sourceA_parse : parseOpenSMILES smilesA = Except.ok sourceA := by
  rfl

/-- The source is the existing indexed atom list with only position 4 replaced; all structural
source data are the existing fixture's, unchanged. -/
theorem sourceA_indexed_change :
    sourceA.atoms =
        sourceAtoms.take 4 ++ [stereoC TetrahedralInputParity.clockwise] ++ sourceAtoms.drop 5 ∧
      sourceA.bonds = sourceBonds ∧
      sourceA.neighborOrder = sourceNeighborOrder ∧
      sourceA.introductionPredecessors = sourceIntro ∧
      sourceAtoms[4]? = some (stereoC TetrahedralInputParity.anticlockwise) ∧
      sourceA.atoms[4]? = some (stereoC TetrahedralInputParity.clockwise) := by
  decide

/-- The materialized molecule has the same 17 atoms, 16 bonds and written-neighbour rows as the
existing fixture; only atom 4's tetrahedral marker differs. -/
theorem sourceA_materialization :
    molA.atomCount = 17 ∧
      molA.bonds.length = 16 ∧
      molA.writtenNeighbors c2Atom = [0, 11, 2, 3] ∧
      molA.writtenNeighbors middleAtom = [1, 12, 4, 7] ∧
      molA.writtenNeighbors c3Atom = [3, 13, 5, 6] ∧
      molA.atomAt? c2HAtom = some (AtomSpec.aliphatic Element.H) ∧
      molA.atomAt? c0HAtom = some (AtomSpec.aliphatic Element.H) ∧
      molA.atomAt? c3HAtom = some (AtomSpec.aliphatic Element.H) ∧
      sourceA.atomAt? c2Atom = some (stereoC TetrahedralInputParity.clockwise) ∧
      sourceA.atomAt? middleAtom = some (stereoC TetrahedralInputParity.clockwise) ∧
      sourceA.atomAt? c3Atom = some (stereoC TetrahedralInputParity.clockwise) := by
  decide

/-! ## 2. Actual canonical nodes, cursors and generated official frames -/

/-- The original root C2 (parser atom 1). -/
def c2RootA : CanonicalBranchNode := canonicalCenterRoot c2Atom

/-- The new root C0 (parser atom 3), used only for the middle-center run. -/
def c0RootA : CanonicalBranchNode := canonicalCenterRoot middleAtom

/-- C0 as the auxiliary occurrence under the original root C2. -/
def c0NodeA : CanonicalBranchNode := canonicalRoot c2Atom middleAtom

/-- C3 as the outward occurrence under the original root C2. -/
def c3NodeA : CanonicalBranchNode :=
  { atom := c3Atom, parent := middleAtom, history := [c3Atom, middleAtom, c2Atom],
    provenance := CanonicalNodeProvenance.realAtom }

/-- The parent (C2) arm cursor of the C0 comparison. -/
def c2ArmCursorA : CanonicalRerootCursor :=
  { node := c2RootA, previous? := some c0NodeA }

/-- The outward (C3) arm cursor of the C0 comparison. -/
def c3ArmCursorA : CanonicalRerootCursor :=
  { node := c3NodeA, previous? := some c0NodeA }

/-- The official generated profile at the original root C2. -/
def c2ProfileA : FrameRuntime.Profile :=
  (FrameRuntime.profile? molA c2RootA).getD ⟨c2RootA, ⟨[]⟩, []⟩

/-- The official generated profile at the original-root C0 occurrence. -/
def c0ProfileA : FrameRuntime.Profile :=
  (FrameRuntime.profile? molA c0NodeA).getD ⟨c0NodeA, ⟨[]⟩, []⟩

/-- The official generated profile at the new C0 root. -/
def c0RootProfileA : FrameRuntime.Profile :=
  (FrameRuntime.profile? molA c0RootA).getD ⟨c0RootA, ⟨[]⟩, []⟩

/-- The parser pipeline generates an official frame at all three nodes used below. -/
theorem profiles_resolve_A :
    FrameRuntime.profile? molA c2RootA = some c2ProfileA ∧
      FrameRuntime.profile? molA c0NodeA = some c0ProfileA ∧
      FrameRuntime.profile? molA c0RootA = some c0RootProfileA := by
  decide

/-- The old anchoring uses history `[3, 1]` (C0 seen from the original root C2); the new
anchoring uses history `[3]` (C0 itself is the root).  In the old frame both carbon arms observe
distance 1 from the evaluated occurrence. -/
theorem c0_profile_anchoring_A :
    c0ProfileA.center.history = [middleAtom, c2Atom] ∧
      c0RootProfileA.center.history = [middleAtom] ∧
      c0ProfileA.frame.originHistory = [middleAtom, c2Atom] ∧
      c0RootProfileA.frame.originHistory = [middleAtom] ∧
      CanonicalComparisonFrame.observeNode c0ProfileA.frame c2RootA = some 1 ∧
      CanonicalComparisonFrame.observeNode c0ProfileA.frame c3NodeA = some 1 := by
  decide

/-! ## 3. Actual eligible occurrence and actual frames -/

/-- The production auxiliary filter at the original root selects C0 (atom 3) and C3 (atom 4),
exactly as in the existing actual fixture.  No supplied cut or hand-chosen occurrence key is used. -/
theorem eligible_occurrence_original_root_A :
    (((collectCanonicalTreeAuthoritative molA fuelA [c2RootA]).getD []).filter
        (fun node => node.provenance == CanonicalNodeProvenance.realAtom &&
          node.atom != c2Atom &&
          (molA.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome))).map
        (fun node => node.atom) = [middleAtom, c3Atom] := by
  decide

/-- At the new C0 root the same production filter selects the two real tetrahedral occurrences
C2 (atom 1) and C3 (atom 4); C0 itself is excluded as the center under evaluation. -/
theorem eligible_occurrence_new_root_A :
    (((collectCanonicalTreeAuthoritative molA fuelA [c0RootA]).getD []).filter
        (fun node => node.provenance == CanonicalNodeProvenance.realAtom &&
          node.atom != middleAtom &&
          (molA.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome))).map
        (fun node => node.atom) = [c2Atom, c3Atom] := by
  decide

/-- The two arm cursors are actual members of C0's generated occurrence frame, not arbitrary
keys. -/
theorem c0_arm_frame_membership_A :
    c2ArmCursorA ∈ occurrenceLigandCursors molA c0NodeA ∧
      c3ArmCursorA ∈ occurrenceLigandCursors molA c0NodeA ∧
      occurrenceLigandFrame? molA c0NodeA = some (occurrenceLigandCursors molA c0NodeA) := by
  decide

/-! ## 4. Actual Rule-1a arm tie and the original-root Rule-1b separation -/

/-- The actual cursor comparator ties the parent C2 arm and the outward C3 arm at Rule 1a; the
implemented original-root total Rule 1b separates them by stored root distance 0 versus 2; the
framed runtime ties both at Rule 1a and Rule 2 because both observe frame distance 1. -/
theorem c0_arm_rule1a_tie_A :
    c2ArmCursorA.node.provenance = CanonicalNodeProvenance.realAtom ∧
      c3ArmCursorA.node.provenance = CanonicalNodeProvenance.realAtom ∧
      compareCursorBranchAtAuthoritative? molA fuelA CanonicalRuleStage.rule1a
          c2ArmCursorA c3ArmCursorA = some Ordering.eq ∧
      compareCursorBranchAtAuthoritative? molA fuelA CanonicalRuleStage.rule1b
          c2ArmCursorA c3ArmCursorA = some Ordering.gt ∧
      c2ArmCursorA.node.rule1bRootDistance = 0 ∧
      c3ArmCursorA.node.rule1bRootDistance = 2 ∧
      FrameRuntime.compareBranch? molA c0ProfileA true fuelA CanonicalRuleStage.rule1a
          (FrameRuntime.Cursor.actual c2ArmCursorA)
          (FrameRuntime.Cursor.actual c3ArmCursorA) = some Ordering.eq ∧
      FrameRuntime.compareBranch? molA c0ProfileA true fuelA CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual c2ArmCursorA)
          (FrameRuntime.Cursor.actual c3ArmCursorA) = some Ordering.eq := by
  decide

/-! ## 5. Actual discovered auxiliary facts and states

The facts below are the exact records returned by the executable pipeline; they are defined so
that the state equalities can be stated, but no output is assumed. -/

/-- C3's occurrence-local auxiliary fact under the original root C2 (`S`, uppercase). -/
def c3FactA : OccurrenceAuxFact :=
  { key := { history := [c3Atom, middleAtom, c2Atom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c3Atom
    descriptor := RS.S
    uppercase := true
    priorityPositions := [2, 0, 3, 1] }

/-- C0's occurrence-local auxiliary fact under the original root C2 in the actual deeper batch
state (`S`, uppercase; Rule-4a availability ordering, not the Rule-1a/1b original-root label). -/
def c0AuxFactA : OccurrenceAuxFact :=
  { key := { history := [middleAtom, c2Atom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := middleAtom
    descriptor := RS.S
    uppercase := true
    priorityPositions := [3, 2, 0, 1] }

/-- The original-root (unframed) C0 occurrence label with the empty state (`R`, uppercase). -/
def legacyC0FactA : OccurrenceAuxFact :=
  { key := { history := [middleAtom, c2Atom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := middleAtom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [3, 0, 2, 1] }

/-- C2's occurrence-local auxiliary fact under the new C0 root (history `[1, 3]`). -/
def c2AuxRootC0A : OccurrenceAuxFact :=
  { key := { history := [c2Atom, middleAtom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c2Atom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [2, 3, 0, 1] }

/-- C3's occurrence-local auxiliary fact under the new C0 root (history `[4, 3]`). -/
def c3AuxRootC0A : OccurrenceAuxFact :=
  { key := { history := [c3Atom, middleAtom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c3Atom
    descriptor := RS.S
    uppercase := true
    priorityPositions := [2, 0, 3, 1] }

/-- The actual auxiliary state produced for the original root C2. -/
theorem c2_root_aux_state_A :
    buildOccurrenceAuxStateFullyAuthoritative? molA fuelA c2Atom =
      some [c3FactA, c0AuxFactA] := by
  decide

/-- The actual auxiliary state produced for the new C0 root. -/
theorem c0_root_aux_state_A :
    buildOccurrenceAuxStateFullyAuthoritative? molA fuelA middleAtom =
      some [c2AuxRootC0A, c3AuxRootC0A] := by
  decide

/-- Both arm keys in the new-root discovered state are occupied by the actual discovered facts;
their descriptors are distinct (`R` parent versus `S` outward). -/
theorem c0_root_discovered_arm_facts_A :
    OccurrenceAuxState.factAt? [c2AuxRootC0A, c3AuxRootC0A]
        (canonicalRoot middleAtom c2Atom) = some c2AuxRootC0A ∧
      OccurrenceAuxState.factAt? [c2AuxRootC0A, c3AuxRootC0A]
        (canonicalRoot middleAtom c3Atom) = some c3AuxRootC0A ∧
      c2AuxRootC0A.descriptor = RS.R ∧
      c3AuxRootC0A.descriptor = RS.S ∧
      c2AuxRootC0A.descriptor ≠ c3AuxRootC0A.descriptor := by
  decide

/-! ## 6. Actual C2-rooted final output

The entry point `tetrahedralOccurrenceFactAuthoritative?` builds the complete discovered auxiliary
state and evaluates the root.  Its value is computed, not assumed. -/

/-- The actual final production record at the original root C2. -/
def c2ProductionFactA : RawDescriptorFact :=
  { atom := c2Atom
    descriptor := RS.R
    uppercase := true
    evidenceSize := 2
    decisiveRule? := none
    descriptorDependentPairs := 2
    priorityPositions := [2, 3, 0, 1] }

/-- The actual pipeline returns the C2 record with descriptor `R`. -/
theorem c2_production_fact_A :
    tetrahedralOccurrenceFactAuthoritative? molA fuelA c2Atom = some c2ProductionFactA := by
  decide

/-- The computed C2 output pair is `(R, true)`. -/
theorem c2_output_A :
    (tetrahedralOccurrenceFactAuthoritative? molA fuelA c2Atom).map
        (fun fact => (fact.descriptor, fact.uppercase)) = some (RS.R, true) := by
  rw [c2_production_fact_A]
  rfl

/-! ## 7. Old anchoring: original-root versus framed auxiliary labels at C0

These are the two occurrence-local observers on the same discovered graph under the original root
C2: the unframed/original-root evaluator with the empty deeper state, and the selected framed
evaluator.  The framed batch state `[c3FactA]` is the actual deeper-first prefix of the discovered
state `[c3FactA, c0AuxFactA]`; `c3FactA` is itself produced by the pipeline
(`c2_root_aux_state_A`). -/

/-- The original-root (unframed) observer labels the C0 occurrence `R`. -/
theorem legacy_observer_c0_A :
    legacyOccurrenceFactAuthoritative? molA fuelA [] c0NodeA = some legacyC0FactA := by
  decide

/-- The framed observer refuses the C0 occurrence from the empty state. -/
theorem framed_observer_empty_c0_A :
    occurrenceFactAuthoritative? molA fuelA [] c0NodeA = none := by
  decide

/-- The framed observer labels the same C0 occurrence `S` in the actual deeper batch state
`[c3FactA]`. -/
theorem framed_observer_batch_c0_A :
    occurrenceFactAuthoritative? molA fuelA [c3FactA] c0NodeA = some c0AuxFactA := by
  decide

/-- The two actual auxiliary observers differ at C0 (`R` versus `S`). -/
theorem aux_observer_labels_differ_A :
    legacyC0FactA.descriptor = RS.R ∧
      c0AuxFactA.descriptor = RS.S ∧
      legacyC0FactA.descriptor ≠ c0AuxFactA.descriptor := by
  decide

/-- The difference is an ordering difference, not a parity difference: both labels are uppercase
records over the same written-neighbour frame, with swapped parent/outward priorities. -/
theorem aux_observer_priority_positions_A :
    legacyC0FactA.priorityPositions = [3, 0, 2, 1] ∧
      c0AuxFactA.priorityPositions = [3, 2, 0, 1] := by
  decide

/-! ## 8. New anchoring: actual C0-rooted output

With C0 itself as the root, the pipeline discovers both arm facts under histories `[1, 3]` and
`[4, 3]`, then evaluates the root from that discovered state. -/

/-- The occurrence fact returned by the framed root evaluation with the actually discovered
two-arm state. -/
def c0RootOccurrenceFactA : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey c0RootA
    atom := middleAtom
    descriptor := RS.R
    uppercase := false
    priorityPositions := [3, 0, 2, 1] }

/-- The actual final production record at the new C0 root. -/
def c0ProductionFactA : RawDescriptorFact :=
  { atom := middleAtom
    descriptor := RS.R
    uppercase := false
    evidenceSize := 2
    decisiveRule? := none
    descriptorDependentPairs := 2
    priorityPositions := [3, 0, 2, 1] }

/-- Without discovered auxiliary labels the C0-rooted framed evaluation refuses.  Success therefore
depends on the actual discovered arm facts, not on a supplied label. -/
theorem c0_root_empty_refuses_A :
    occurrenceFactAuthoritative? molA fuelA [] c0RootA = none := by
  decide

/-- With the actually discovered arm facts the framed root evaluation succeeds and returns base
descriptor `R` with `uppercase = false`. -/
theorem c0_root_framed_discovered_state_A :
    occurrenceFactAuthoritative? molA fuelA [c2AuxRootC0A, c3AuxRootC0A] c0RootA =
      some c0RootOccurrenceFactA := by
  decide

/-- The actual production entry point at the middle center C0 returns the computed record. -/
theorem c0_production_fact_A :
    tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom = some c0ProductionFactA := by
  decide

/-- The actually computed middle-center output pair is `(R, false)`. -/
theorem c0_output_A :
    (tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom).map
        (fun fact => (fact.descriptor, fact.uppercase)) = some (RS.R, false) := by
  rw [c0_production_fact_A]
  rfl

/-- The middle center is actually assigned by the production entry point (no refusal). -/
theorem c0_successfully_assigned_A :
    (tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom).isSome = true := by
  rw [c0_production_fact_A]
  rfl

/-- The computed `uppercase` flag of the C0-rooted output is `false`.  This is the raw pipeline's
pseudo marker, not an independently counted source-pair descriptor. -/
theorem c0_output_uppercase_flag :
    (tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom).map
        (fun fact => fact.uppercase) = some false := by
  rw [c0_production_fact_A]
  rfl

/-- Boundary of the final record's numeric fields.  `descriptorDependentPairs` is exactly the
discovered auxiliary-state length (2 here), not a count of pseudo comparisons; `evidenceSize` is
`max 1 state.length`.  The `uppercase` flag is the classifier's parity of *final adjacent* pseudo
decisions, not a localized insertion-count-equals-one criterion.  No independent source-pair count
is proved in this module. -/
theorem c0_production_fact_state_length_boundary :
    c0ProductionFactA.descriptorDependentPairs = 2 ∧
      c0ProductionFactA.evidenceSize = 2 ∧
      ([c2AuxRootC0A, c3AuxRootC0A] : OccurrenceAuxState).length = 2 ∧
      c2ProductionFactA.descriptorDependentPairs = 2 ∧
      c2ProductionFactA.evidenceSize = 2 ∧
      ([c3FactA, c0AuxFactA] : OccurrenceAuxState).length = 2 := by
  decide

/-! ## 9. The existing fixture at the same new anchoring is refused

The existing homochiral fixture has the same eligibility, the same Rule-1a tie and its own
old-anchoring auxiliary labels, but at the new anchoring its two discovered arm facts are both
`R`.  The actual pipeline then refuses the middle center.  This is the concrete old/new contrast:
variant A changes the potential center into an actually assigned center; it is not assumed. -/

/-- Existing-fixture C2 occurrence fact under the C0 root (history `[1, 3]`). -/
def c2AuxRootC0Existing : OccurrenceAuxFact :=
  { key := { history := [c2Atom, middleAtom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c2Atom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [2, 3, 0, 1] }

/-- Existing-fixture C3 occurrence fact under the C0 root (history `[4, 3]`). -/
def c3AuxRootC0Existing : OccurrenceAuxFact :=
  { key := { history := [c3Atom, middleAtom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c3Atom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [2, 0, 3, 1] }

/-- The existing fixture's actual discovered state at the new C0 root. -/
theorem existing_c0_root_aux_state :
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel middleAtom =
      some [c2AuxRootC0Existing, c3AuxRootC0Existing] := by
  decide

/-- Both discovered arms of the existing fixture are `R` at the new root. -/
theorem existing_c0_root_arm_descriptors_equal :
    c2AuxRootC0Existing.descriptor = RS.R ∧
      c3AuxRootC0Existing.descriptor = RS.R ∧
      c2AuxRootC0Existing.descriptor = c3AuxRootC0Existing.descriptor := by
  decide

/-- The existing fixture's C0-rooted production entry point is an actual refusal (`none`). -/
theorem existing_c0_root_refused :
    tetrahedralOccurrenceFactAuthoritative? mol fuel middleAtom = none := by
  decide

/-- The refusal is already visible in the framed root evaluation over the existing fixture's
actually discovered state. -/
theorem existing_c0_root_framed_discovered_state_refuses :
    occurrenceFactAuthoritative? mol fuel [c2AuxRootC0Existing, c3AuxRootC0Existing]
      (canonicalCenterRoot middleAtom) = none := by
  decide

/-- Actual old/new contrast: the existing fixture is not assigned at the new C0 root while the
one-parity variant is.  Both statements are computed by the same production entry point. -/
theorem new_assignable_center_contrast :
    (tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom).isSome = true ∧
      (tetrahedralOccurrenceFactAuthoritative? mol fuel middleAtom).isSome = false := by
  rw [c0_production_fact_A, existing_c0_root_refused]
  exact ⟨rfl, rfl⟩

/-- On the actually discovered arm descriptors, the repository's Rule-5 pair ordering is a strict
`gt` for variant A (`R` before `S`) and a tie for the existing fixture (`R` against `R`).  This is
a semantic reading of the computed descriptors; the pipeline outputs themselves are the theorems
above. -/
theorem discovered_arm_rule5_ordering :
    rule5PairOrdering c2AuxRootC0A.descriptor c3AuxRootC0A.descriptor = Ordering.gt ∧
      rule5PairOrdering c2AuxRootC0Existing.descriptor
        c3AuxRootC0Existing.descriptor = Ordering.eq ∧
      rule5PairSign c2AuxRootC0A.descriptor c3AuxRootC0A.descriptor = 1 ∧
      rule5PairSign c2AuxRootC0Existing.descriptor
        c3AuxRootC0Existing.descriptor = 0 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simp [c2AuxRootC0A, c3AuxRootC0A, rule5PairSign]
  · simp [c2AuxRootC0Existing, c3AuxRootC0Existing, rule5PairSign]

/-! ## 10. True full-parity-reflected control

Every tetrahedral marker of variant A is inverted: a full syntactic tetrahedral-parity reflection.
The two arm labels swap (`R ↦ S`, `S ↦ R`) and the C2 root descriptor swaps, so the control is not an
identical copy.  This establishes parity reflection of the source markers, not non-superposability
of the whole molecule.  Only after the actual C0-rooted outputs of both molecules have been computed
do we state the invariance of the computed `(descriptor, uppercase)` pair; no lowercase `r`/`s`
letter is emitted. -/

/-- Invert one tetrahedral input parity. -/
def flipTetrahedralParity : TetrahedralInputParity → TetrahedralInputParity
  | TetrahedralInputParity.clockwise => TetrahedralInputParity.anticlockwise
  | TetrahedralInputParity.anticlockwise => TetrahedralInputParity.clockwise

/-- The string with every bracket marker inverted. -/
def smilesMirror : String := "C[C@H](Cl)[C@H]([C@H](Cl)C)Br"

/-- The full-parity-reflected source: all three tetrahedral atoms of variant A are inverted. -/
def sourceMirror : RawMolecule :=
  { atoms :=
      [ methylC
      , stereoC TetrahedralInputParity.anticlockwise
      , plainCl
      , stereoC TetrahedralInputParity.anticlockwise
      , stereoC TetrahedralInputParity.anticlockwise
      , plainCl
      , methylC
      , plainBr ]
    bonds := sourceBonds
    neighborOrder := sourceNeighborOrder
    introductionPredecessors := sourceIntro }

/-- The production materialization of the mirror control. -/
def molMirror : RawMolecule := sourceMirror.withExplicitHydrogens

/-- The parser accepts the mirror string and returns exactly the full reflection of source A. -/
theorem sourceMirror_parse : parseOpenSMILES smilesMirror = Except.ok sourceMirror := by
  rfl

/-- The control is a true full parity reflection: every atom's tetrahedral marker is inverted,
and all structural source data are unchanged. -/
theorem sourceMirror_full_parity_reflection :
    sourceMirror.atoms =
        sourceA.atoms.map
          (fun spec => { spec with tetrahedral? := spec.tetrahedral?.map flipTetrahedralParity }) ∧
      sourceMirror.bonds = sourceA.bonds ∧
      sourceMirror.neighborOrder = sourceA.neighborOrder ∧
      sourceMirror.introductionPredecessors = sourceA.introductionPredecessors := by
  decide

/-- All three reflected centers are anticlockwise in the parsed mirror source. -/
theorem sourceMirror_parities :
    sourceMirror.atomAt? c2Atom = some (stereoC TetrahedralInputParity.anticlockwise) ∧
      sourceMirror.atomAt? middleAtom =
        some (stereoC TetrahedralInputParity.anticlockwise) ∧
      sourceMirror.atomAt? c3Atom = some (stereoC TetrahedralInputParity.anticlockwise) := by
  decide

/-- The mirror materialization has the same 17 atoms and written-neighbour rows. -/
theorem mirror_materialization :
    molMirror.atomCount = 17 ∧
      molMirror.bonds.length = 16 ∧
      molMirror.writtenNeighbors middleAtom = [1, 12, 4, 7] ∧
      molMirror.writtenNeighbors c3Atom = [3, 13, 5, 6] := by
  decide

/-- Mirror canonical nodes and cursors, in the same indexing as variant A. -/
def c2RootM : CanonicalBranchNode := canonicalCenterRoot c2Atom

def c0RootM : CanonicalBranchNode := canonicalCenterRoot middleAtom

def c0NodeM : CanonicalBranchNode := canonicalRoot c2Atom middleAtom

def c3NodeM : CanonicalBranchNode :=
  { atom := c3Atom, parent := middleAtom, history := [c3Atom, middleAtom, c2Atom],
    provenance := CanonicalNodeProvenance.realAtom }

def c2ArmCursorM : CanonicalRerootCursor :=
  { node := c2RootM, previous? := some c0NodeM }

def c3ArmCursorM : CanonicalRerootCursor :=
  { node := c3NodeM, previous? := some c0NodeM }

def c2ProfileM : FrameRuntime.Profile :=
  (FrameRuntime.profile? molMirror c2RootM).getD ⟨c2RootM, ⟨[]⟩, []⟩

def c0ProfileM : FrameRuntime.Profile :=
  (FrameRuntime.profile? molMirror c0NodeM).getD ⟨c0NodeM, ⟨[]⟩, []⟩

def c0RootProfileM : FrameRuntime.Profile :=
  (FrameRuntime.profile? molMirror c0RootM).getD ⟨c0RootM, ⟨[]⟩, []⟩

/-- The mirror generates the same three official frames. -/
theorem mirror_profiles_resolve :
    FrameRuntime.profile? molMirror c2RootM = some c2ProfileM ∧
      FrameRuntime.profile? molMirror c0NodeM = some c0ProfileM ∧
      FrameRuntime.profile? molMirror c0RootM = some c0RootProfileM := by
  decide

/-- The mirror has the same actual eligible occurrences and the same Rule-1a arm tie. -/
theorem mirror_eligibility_and_rule1a_tie :
    (((collectCanonicalTreeAuthoritative molMirror fuelA [c2RootM]).getD []).filter
        (fun node => node.provenance == CanonicalNodeProvenance.realAtom &&
          node.atom != c2Atom &&
          (molMirror.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome))).map
        (fun node => node.atom) = [middleAtom, c3Atom] ∧
      compareCursorBranchAtAuthoritative? molMirror fuelA CanonicalRuleStage.rule1a
          c2ArmCursorM c3ArmCursorM = some Ordering.eq ∧
      compareCursorBranchAtAuthoritative? molMirror fuelA CanonicalRuleStage.rule1b
          c2ArmCursorM c3ArmCursorM = some Ordering.gt := by
  decide

/-- Mirror auxiliary fact at C3 under the original root C2. -/
def c3FactM : OccurrenceAuxFact :=
  { key := { history := [c3Atom, middleAtom, c2Atom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c3Atom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [2, 0, 3, 1] }

/-- Mirror auxiliary fact at C0 under the original root C2 in the actual deeper batch state. -/
def c0AuxFactM : OccurrenceAuxFact :=
  { key := { history := [middleAtom, c2Atom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := middleAtom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [3, 2, 0, 1] }

/-- Mirror original-root (unframed) C0 occurrence label. -/
def legacyC0FactM : OccurrenceAuxFact :=
  { key := { history := [middleAtom, c2Atom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := middleAtom
    descriptor := RS.S
    uppercase := true
    priorityPositions := [3, 0, 2, 1] }

/-- Mirror C2 occurrence fact under the C0 root. -/
def c2AuxRootC0M : OccurrenceAuxFact :=
  { key := { history := [c2Atom, middleAtom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c2Atom
    descriptor := RS.S
    uppercase := true
    priorityPositions := [2, 3, 0, 1] }

/-- Mirror C3 occurrence fact under the C0 root. -/
def c3AuxRootC0M : OccurrenceAuxFact :=
  { key := { history := [c3Atom, middleAtom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c3Atom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [2, 0, 3, 1] }

/-- Mirror final production record at the original root C2. -/
def c2ProductionFactM : RawDescriptorFact :=
  { atom := c2Atom
    descriptor := RS.S
    uppercase := true
    evidenceSize := 2
    decisiveRule? := none
    descriptorDependentPairs := 2
    priorityPositions := [2, 3, 0, 1] }

/-- Mirror final production record at the C0 root. -/
def c0ProductionFactM : RawDescriptorFact :=
  { atom := middleAtom
    descriptor := RS.R
    uppercase := false
    evidenceSize := 2
    decisiveRule? := none
    descriptorDependentPairs := 2
    priorityPositions := [3, 2, 0, 1] }

/-- The mirror's actual discovered states. -/
theorem mirror_aux_states :
    buildOccurrenceAuxStateFullyAuthoritative? molMirror fuelA c2Atom =
        some [c3FactM, c0AuxFactM] ∧
      buildOccurrenceAuxStateFullyAuthoritative? molMirror fuelA middleAtom =
        some [c2AuxRootC0M, c3AuxRootC0M] := by
  decide

/-- The mirror's actual old-anchoring observer labels: original-root `S`, framed batch `R`. -/
theorem mirror_legacy_and_framed_observers :
    legacyOccurrenceFactAuthoritative? molMirror fuelA [] c0NodeM = some legacyC0FactM ∧
      occurrenceFactAuthoritative? molMirror fuelA [c3FactM] c0NodeM = some c0AuxFactM ∧
      occurrenceFactAuthoritative? molMirror fuelA [] c0NodeM = none := by
  decide

/-- The mirror's actual C2-rooted output is `(S, true)`. -/
theorem mirror_c2_production_fact :
    tetrahedralOccurrenceFactAuthoritative? molMirror fuelA c2Atom = some c2ProductionFactM := by
  decide

/-- The mirror's actual C0-rooted output is `(R, false)`. -/
theorem mirror_c0_production_fact :
    tetrahedralOccurrenceFactAuthoritative? molMirror fuelA middleAtom =
      some c0ProductionFactM := by
  decide

/-- The C2 and C3 arm labels swap under the full tetrahedral-parity reflection, so the control is a
syntactic parity reflection rather than an identical copy.  No claim of molecular
non-superposability is made. -/
theorem arm_descriptors_swap_under_mirror :
    c2ProductionFactA.descriptor = RS.swap c2ProductionFactM.descriptor ∧
      c3AuxRootC0A.descriptor = RS.swap c3AuxRootC0M.descriptor ∧
      c2AuxRootC0A.descriptor = RS.swap c2AuxRootC0M.descriptor := by
  decide

/-- Both molecules are actually assigned at the new C0 root. -/
theorem both_c0_roots_assigned :
    (tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom).isSome = true ∧
      (tetrahedralOccurrenceFactAuthoritative? molMirror fuelA middleAtom).isSome = true := by
  rw [c0_production_fact_A, mirror_c0_production_fact]
  exact ⟨rfl, rfl⟩

/-- **Computed mirror invariance of the C0-rooted output pair.**  This statement is derived from the
two actual successful production outputs (variant A and its full parity reflection); it is not
asserted before those computations.  The base `RS` letter and the `uppercase` flag are invariant,
while the priority positions differ. -/
theorem c0_root_computed_output_mirror_invariant :
    (tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom).map
        (fun fact => (fact.descriptor, fact.uppercase)) =
      (tetrahedralOccurrenceFactAuthoritative? molMirror fuelA middleAtom).map
        (fun fact => (fact.descriptor, fact.uppercase)) := by
  rw [c0_production_fact_A, mirror_c0_production_fact]
  rfl

/-- Value-level reading of the computed mirror invariance: both successful C0 outputs are
`(R, false)`. -/
theorem c0_root_output_pair_value_mirror_invariant :
    c0ProductionFactA.descriptor = RS.R ∧
      c0ProductionFactA.uppercase = false ∧
      c0ProductionFactM.descriptor = RS.R ∧
      c0ProductionFactM.uppercase = false := by
  decide

/-- The priority positions are not identical under reflection; the invariance claim is about the
computed descriptor/uppercase pair only. -/
theorem c0_root_priority_positions_differ_under_mirror :
    c0ProductionFactA.priorityPositions = [3, 0, 2, 1] ∧
      c0ProductionFactM.priorityPositions = [3, 2, 0, 1] := by
  decide

end ActualEligibleParentParityVariant
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.smilesA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.molA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.fuelA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceA_parse
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceA_indexed_change
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceA_materialization
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2RootA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0RootA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0NodeA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3NodeA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2ArmCursorA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3ArmCursorA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2ProfileA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0ProfileA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0RootProfileA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.profiles_resolve_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_profile_anchoring_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.eligible_occurrence_original_root_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.eligible_occurrence_new_root_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_arm_frame_membership_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_arm_rule1a_tie_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3FactA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0AuxFactA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.legacyC0FactA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2AuxRootC0A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3AuxRootC0A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2_root_aux_state_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_root_aux_state_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_root_discovered_arm_facts_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2ProductionFactA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2_production_fact_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2_output_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.legacy_observer_c0_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.framed_observer_empty_c0_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.framed_observer_batch_c0_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.aux_observer_labels_differ_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.aux_observer_priority_positions_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0RootOccurrenceFactA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0ProductionFactA
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_root_empty_refuses_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_root_framed_discovered_state_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_production_fact_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_output_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_successfully_assigned_A
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_output_uppercase_flag
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_production_fact_state_length_boundary
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2AuxRootC0Existing
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3AuxRootC0Existing
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.existing_c0_root_aux_state
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.existing_c0_root_arm_descriptors_equal
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.existing_c0_root_refused
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.existing_c0_root_framed_discovered_state_refuses
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.new_assignable_center_contrast
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.discovered_arm_rule5_ordering
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.flipTetrahedralParity
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.smilesMirror
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceMirror
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.molMirror
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceMirror_parse
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceMirror_full_parity_reflection
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.sourceMirror_parities
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.mirror_materialization
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2RootM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0RootM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0NodeM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3NodeM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2ArmCursorM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3ArmCursorM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2ProfileM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0ProfileM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0RootProfileM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.mirror_profiles_resolve
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.mirror_eligibility_and_rule1a_tie
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3FactM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0AuxFactM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.legacyC0FactM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2AuxRootC0M
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c3AuxRootC0M
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c2ProductionFactM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0ProductionFactM
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.mirror_aux_states
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.mirror_legacy_and_framed_observers
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.mirror_c2_production_fact
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.mirror_c0_production_fact
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.arm_descriptors_swap_under_mirror
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.both_c0_roots_assigned
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_root_computed_output_mirror_invariant
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_root_output_pair_value_mirror_invariant
assert_kernel_only TetraStereo.OneCenter.ActualEligibleParentParityVariant.c0_root_priority_positions_differ_under_mirror
