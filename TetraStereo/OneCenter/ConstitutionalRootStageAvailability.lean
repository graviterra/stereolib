import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

/-
  ConstitutionalRootStageAvailability

  Feasibility certificate for the actual production occurrence pipeline over the concrete molecule

      C[C@@H](Cl)[C@@H]([C@H](Cl)C)Br

  The actual parser (`ChemistrySemantics.takeBracketParity`) maps `@@` to `clockwise`
  and `@` to `anticlockwise`. The source atoms are: 0 methyl C, 1 C2 (clockwise),
  2 Cl, 3 C0 (clockwise), 4 C3 (anticlockwise), 5 Cl, 6 methyl C, and 7 Br.
  The kernel-checked `source_parse` theorem below binds this exact string to the fixture.

  ## A. Rule-1a early availability at the original root C2 (strong result)

  At C2 the four ligands are Cl (Z 17), the bracket H (Z 1), the methyl carbon (Z 6, sphere
  `[H,H,H]`), and the middle carbon C0 (Z 6, sphere `[Br,C,H,...]`).  Each of the six ordered
  comparisons is decided by Rule 1a alone, in both comparison paths:

  * the width-unbounded cursor protocol `compareCursorBranchAtAuthoritative?` (proved at
    `CanonicalRuleStage.rule1a`, hence also at the full constitutional stage), and
  * the framed production runtime `FrameRuntime.compareBranch?` used by
    `occurrenceFactAuthoritative?` (proved at `.rule1a` with the actual resolved profile).

  The Rules-4a--5 auxiliary machinery is therefore never consulted for C2's own comparison set.
  The source bracket parity (clockwise at C2 under this repository's convention) and the priority
  permutation `[Cl, C0, methyl, H]` (written positions `[2,3,0,1]`, even) give the final descriptor
  `RS.R`; this is independent of every auxiliary state.  The source string parse is validated at
  kernel level (`source_parse`), and
  `source.withExplicitHydrogens` is the 17-atom molecule used throughout.

  ## B. Implemented total-2018 Rule-1b profile at C0 (scoped, not a 2013 claim)

  The width-unbounded cursor comparator assigns `rule1bRootDistance` to every real node (0 for the
  C2 arm, 2 for the C3 arm), so through that path the two C0 arms tie at Rule 1a and separate at
  Rule 1b; that is why `compareOccurrenceBranchesAuthoritative?` and
  `legacyOccurrenceFactAuthoritative?` never read descriptor state in this comparison.  This is a
  fact about the *implemented total profile*, not a justification from IUPAC 2013 Rule 1b, whose
  duplicate-atom priority applies only to duplicate nodes.  No conclusion is drawn here about a
  source-2013 global dependency claim.

  ## C. Actual selected runtime at C0 (framed profile)

  `occurrenceFactAuthoritative?` selects the framed evaluator whenever `FrameRuntime.profile?`
  exists, and it does exist here (proved).  In that runtime Rule 1b compares frame distances from
  the evaluated occurrence, not stored history depths.  From C0's frame both arms observe
  distance 1, so the two constitutionally identical `C(H)(Cl)(CH3)` arms tie at the constitutional
  stage.  Consequently:

  * with the empty state the C0 occurrence is refused (`= none`);
  * at the actual batch state `[c3Fact]` produced immediately before labelling C0, C0 evaluates to
    the occurrence-local auxiliary label `RS.S` with positions `[3,2,0,1]`, because Rule 4a reads
    the C3 auxiliary fact (priority 2) against the absent C2 fact (priority 0);
  * the complete production auxiliary state for center C2 is exactly `[c3Fact, c0AuxFact]`, and
    the centre C2 evaluation returns `RS.R` with positions `[2,3,0,1]`.

  That state contains no fact keyed at C2 (`c2Root`): the auxiliary-occurrence filter excludes the
  centre under evaluation.  Hence the actual C0 comparison reads the C3 occurrence label (and the
  absence of a C2 label), never "C2's earlier-stage configuration"; C2's own final `R` is
  nevertheless state-independent because its six comparisons never reach descriptor rules.

  **No conflation.**  `c2Fact.descriptor = RS.R` is the final descriptor at the original root C2;
  `c3Fact` and `c0AuxFact` are occurrence-local auxiliary labels (C3 and C0 respectively), not
  final root descriptors.  In particular `c0AuxFact.descriptor = RS.S` is not the C0 source-parity
  descriptor, and the legacy/unframed `c0LegacyFact` (an occurrence-local `R` under the implemented
  total profile) is likewise not C0's final descriptor.

  The states used are exactly the empty state and the states actually produced by
  `buildOccurrenceAuxStateFullyAuthoritative?`; no synthetic perturbation is asserted to be
  chemically required.  No production function, stored distance, comparator, parser, or filter is
  modified.  Every scientific export is guarded by `assert_kernel_only`.
-/

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace ConstitutionalRootStageAvailability

open RawMolecule

/-! ## Source parse and explicit-hydrogen materialization -/

/-- Source atom indices. -/
def methyl0 : ℕ := 0
def c2Atom : ℕ := 1
def clAtom : ℕ := 2
def middleAtom : ℕ := 3
def c3Atom : ℕ := 4
def cl2Atom : ℕ := 5
def methyl6 : ℕ := 6
def brAtom : ℕ := 7

/-- Materialized bracket/implied hydrogen indices (see `withExplicitHydrogens`). -/
def c2HAtom : ℕ := 11
def c0HAtom : ℕ := 12
def c3HAtom : ℕ := 13

/-- The actual source string.  Under `takeBracketParity` (`@@` ↦ clockwise, `@` ↦
anticlockwise) this parses to the `sourceAtoms` below: C2 and C0 clockwise, C3 anticlockwise. -/
def smiles : String := "C[C@@H](Cl)[C@@H]([C@H](Cl)C)Br"

/-- An unbracketed organic-subset carbon: OpenSMILES leaves its hydrogen count implicit. -/
def methylC : AtomSpec := { element := Element.C }

/-- Unbracketed terminal halogens. -/
def plainCl : AtomSpec := { element := Element.Cl }
def plainBr : AtomSpec := { element := Element.Br }

/-- A bracket tetrahedral carbon `[C@H]` / `[C@@H]` with one bracket hydrogen. -/
def stereoC (parity : TetrahedralInputParity) : AtomSpec :=
  { element := Element.C, explicitHydrogens? := some 1, tetrahedral? := some parity }

/-- The eight source atoms of `smiles` (`C[C@@H](Cl)[C@@H]([C@H](Cl)C)Br` under this
repository's token convention), confirmed against the parser by `source_parse`. -/
def sourceAtoms : List AtomSpec :=
  [ methylC
  , stereoC TetrahedralInputParity.clockwise
  , plainCl
  , stereoC TetrahedralInputParity.clockwise
  , stereoC TetrahedralInputParity.anticlockwise
  , plainCl
  , methylC
  , plainBr ]

/-- The seven source single bonds, in source order. -/
def sourceBonds : List RawBond :=
  [ { source := 0, target := 1, kind := ParsedBondKind.single }
  , { source := 1, target := 2, kind := ParsedBondKind.single }
  , { source := 1, target := 3, kind := ParsedBondKind.single }
  , { source := 3, target := 4, kind := ParsedBondKind.single }
  , { source := 4, target := 5, kind := ParsedBondKind.single }
  , { source := 4, target := 6, kind := ParsedBondKind.single }
  , { source := 3, target := 7, kind := ParsedBondKind.single } ]

/-- OpenSMILES written-neighbour rows, in source order. -/
def sourceNeighborOrder : List (List ℕ) :=
  [[1], [0, 2, 3], [1], [1, 4, 7], [3, 5, 6], [4], [4], [3]]

/-- Source-token introduction predecessors: atom 0 opens the component; each later atom records
the atom from which it was introduced.  `hydrogenHasPreceding` uses this to place each
bracket/implied hydrogen in the OpenSMILES written-neighbour position. -/
def sourceIntro : List (Option ℕ) :=
  [ none, some 0, some 1, some 1, some 3, some 4, some 4, some 3 ]

/-- The concrete source molecule. -/
def source : RawMolecule :=
  { atoms := sourceAtoms, bonds := sourceBonds,
    neighborOrder := sourceNeighborOrder, introductionPredecessors := sourceIntro }

/-- The source string parses to exactly this concrete raw molecule (kernel-checked parse). -/
theorem source_parse : parseOpenSMILES smiles = Except.ok source := by
  rfl

/-- The explicit-hydrogen materialization the production pipeline actually consumes. -/
def mol : RawMolecule := source.withExplicitHydrogens

/-- Fuel beyond the branch depth (≤ 4) and the sphere-2 discriminations actually needed. -/
def fuel : ℕ := 8

/-- Parse fidelity plus the 17-atom materialization and the source/written-neighbour facts. -/
theorem materialization_validation :
    mol.atomCount = 17 ∧
      mol.bonds.length = 16 ∧
      mol.writtenNeighbors c2Atom = [0, 11, 2, 3] ∧
      mol.writtenNeighbors middleAtom = [1, 12, 4, 7] ∧
      mol.writtenNeighbors c3Atom = [3, 13, 5, 6] ∧
      mol.atomAt? c2HAtom = some (AtomSpec.aliphatic Element.H) ∧
      (mol.atomAt? c2Atom).any (fun spec => spec.tetrahedral?.isSome) = true ∧
      source.atomAt? c2Atom = some (stereoC TetrahedralInputParity.clockwise) ∧
      source.atomAt? middleAtom = some (stereoC TetrahedralInputParity.clockwise) ∧
      source.atomAt? c3Atom = some (stereoC TetrahedralInputParity.anticlockwise) := by
  decide

/-! ## Occurrence nodes, cursors, facts, and resolved profiles -/

def c2Root : CanonicalBranchNode := canonicalCenterRoot c2Atom

def c0Node : CanonicalBranchNode := canonicalRoot c2Atom middleAtom

def c3Node : CanonicalBranchNode :=
  { atom := c3Atom, parent := middleAtom, history := [c3Atom, middleAtom, c2Atom],
    provenance := CanonicalNodeProvenance.realAtom }

def ligandCursor (atom : ℕ) : CanonicalRerootCursor :=
  { node := canonicalRoot c2Atom atom, previous? := some c2Root }

def clCursor : CanonicalRerootCursor := ligandCursor clAtom
def middleCursor : CanonicalRerootCursor := ligandCursor middleAtom
def methylCursor : CanonicalRerootCursor := ligandCursor methyl0
def hCursor : CanonicalRerootCursor := ligandCursor c2HAtom

def c2ArmCursor : CanonicalRerootCursor :=
  { node := c2Root, previous? := some c0Node }

def c3ArmCursor : CanonicalRerootCursor :=
  { node := c3Node, previous? := some c0Node }

/-- The concrete C2 fact; `descriptor = RS.R` is the *final* descriptor at the original root. -/
def c2Fact : OccurrenceAuxFact :=
  { key := { history := [c2Atom], provenance := CanonicalNodeProvenance.realAtom }
    atom := c2Atom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [2, 3, 0, 1] }

/-- The occurrence-local auxiliary fact for C3 (framed profile, empty deeper state). -/
def c3Fact : OccurrenceAuxFact :=
  { key := { history := [c3Atom, middleAtom, c2Atom],
             provenance := CanonicalNodeProvenance.realAtom }
    atom := c3Atom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [2, 0, 3, 1] }

/-- The occurrence-local auxiliary fact for C0 in the actual batch state `[c3Fact]`.
An auxiliary label, not a final root descriptor. -/
def c0AuxFact : OccurrenceAuxFact :=
  { key := { history := [middleAtom, c2Atom], provenance := CanonicalNodeProvenance.realAtom }
    atom := middleAtom
    descriptor := RS.S
    uppercase := true
    priorityPositions := [3, 2, 0, 1] }

/-- The legacy (unframed) evaluator's C0 fact with empty state; retained only for the implemented
total-profile comparison in section B.  It is *not* the selected production result. -/
def c0LegacyFact : OccurrenceAuxFact :=
  { key := { history := [middleAtom, c2Atom], provenance := CanonicalNodeProvenance.realAtom }
    atom := middleAtom
    descriptor := RS.R
    uppercase := true
    priorityPositions := [3, 0, 2, 1] }

/-- The final production descriptor record for the original root C2. -/
def c2ProductionFact : RawDescriptorFact :=
  { atom := c2Atom
    descriptor := RS.R
    uppercase := true
    evidenceSize := 2
    decisiveRule? := none
    descriptorDependentPairs := 2
    priorityPositions := [2, 3, 0, 1] }

/-- The resolved framed profile at the C2 root. -/
def c2Profile : FrameRuntime.Profile :=
  (FrameRuntime.profile? mol c2Root).getD ⟨c2Root, ⟨[]⟩, []⟩

/-- The resolved framed profile at C0. -/
def c0Profile : FrameRuntime.Profile :=
  (FrameRuntime.profile? mol c0Node).getD ⟨c0Node, ⟨[]⟩, []⟩

/-- Framed profiles exist at both centres, so `occurrenceFactAuthoritative?` selects the framed
evaluator there. -/
theorem profiles_resolve :
    FrameRuntime.profile? mol c2Root = some c2Profile ∧
      FrameRuntime.profile? mol c0Node = some c0Profile := by
  decide

/-- The actual C2 occurrence frame is exactly methyl, bracket H, Cl, C0 (in that order, no
duplicates, no phantom padding); the hand-written cursors are its members, and the C0 arm cursors
are members of C0's frame. -/
theorem frame_membership :
    (occurrenceLigandCursors mol c2Root).length = 4 ∧
      (occurrenceLigandCursors mol c2Root).Nodup ∧
      (occurrenceLigandCursors mol c2Root).map (fun cursor => cursor.node.atom) =
        [0, 11, 2, 3] ∧
      occurrenceLigandFrame? mol c2Root = some (occurrenceLigandCursors mol c2Root) ∧
      clCursor ∈ occurrenceLigandCursors mol c2Root ∧
      middleCursor ∈ occurrenceLigandCursors mol c2Root ∧
      methylCursor ∈ occurrenceLigandCursors mol c2Root ∧
      hCursor ∈ occurrenceLigandCursors mol c2Root ∧
      c2ArmCursor ∈ occurrenceLigandCursors mol c0Node ∧
      c3ArmCursor ∈ occurrenceLigandCursors mol c0Node := by
  decide

/-! ## A. C2: six Rule-1a strict comparisons and the final descriptor -/

theorem c2_rule1a_strict :
    compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1a clCursor middleCursor =
        some Ordering.gt ∧
      compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1a clCursor methylCursor =
        some Ordering.gt ∧
      compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1a clCursor hCursor =
        some Ordering.gt ∧
      compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1a middleCursor methylCursor =
        some Ordering.gt ∧
      compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1a middleCursor hCursor =
        some Ordering.gt ∧
      compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1a methylCursor hCursor =
        some Ordering.gt := by
  decide

theorem c2_constitutional_strict :
    certifiedConstitutionalStageAuthoritative? mol fuel clCursor middleCursor = some Ordering.gt ∧
      certifiedConstitutionalStageAuthoritative? mol fuel clCursor methylCursor = some Ordering.gt ∧
      certifiedConstitutionalStageAuthoritative? mol fuel clCursor hCursor = some Ordering.gt ∧
      certifiedConstitutionalStageAuthoritative? mol fuel middleCursor methylCursor = some Ordering.gt ∧
      certifiedConstitutionalStageAuthoritative? mol fuel middleCursor hCursor = some Ordering.gt ∧
      certifiedConstitutionalStageAuthoritative? mol fuel methylCursor hCursor = some Ordering.gt := by
  decide

theorem c2_framed_rule1a_strict :
    FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule1a
        (FrameRuntime.Cursor.actual clCursor) (FrameRuntime.Cursor.actual middleCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule1a
        (FrameRuntime.Cursor.actual clCursor) (FrameRuntime.Cursor.actual methylCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule1a
        (FrameRuntime.Cursor.actual clCursor) (FrameRuntime.Cursor.actual hCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule1a
        (FrameRuntime.Cursor.actual middleCursor) (FrameRuntime.Cursor.actual methylCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule1a
        (FrameRuntime.Cursor.actual middleCursor) (FrameRuntime.Cursor.actual hCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule1a
        (FrameRuntime.Cursor.actual methylCursor) (FrameRuntime.Cursor.actual hCursor) =
        some Ordering.gt := by
  decide

theorem c2_framed_constitutional_strict :
    FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual clCursor) (FrameRuntime.Cursor.actual middleCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual clCursor) (FrameRuntime.Cursor.actual methylCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual clCursor) (FrameRuntime.Cursor.actual hCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual middleCursor) (FrameRuntime.Cursor.actual methylCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual middleCursor) (FrameRuntime.Cursor.actual hCursor) =
        some Ordering.gt ∧
      FrameRuntime.compareBranch? mol c2Profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual methylCursor) (FrameRuntime.Cursor.actual hCursor) =
        some Ordering.gt := by
  decide

/-- The strict ranking forces `[Cl, middle, methyl, H]` (written positions `[2,3,0,1]`); that
permutation is even, and the source bracket parity (clockwise, from the repository's `@@`
convention) therefore yields `R`. -/
theorem c2_descriptor_from_parity :
    RawMolecule.descriptorOfParity TetrahedralInputParity.clockwise
        (RawMolecule.permutationIsEven [2, 3, 0, 1]) = RS.R := by
  decide

/-- A strict constitutional decision short-circuits the full Rules-1a--5 cursor comparison before
any descriptor rule can read the auxiliary state. -/
theorem c2_pair_state_independent (state : OccurrenceAuxState)
    (left right : CanonicalRerootCursor)
    (hc : certifiedConstitutionalStageAuthoritative? mol fuel left right = some Ordering.gt) :
    compareOccurrenceBranchesAuthoritative? mol state fuel left right =
      some { ordering := Ordering.gt } := by
  unfold compareOccurrenceBranchesAuthoritative?
  rw [hc]
  rfl

/-- The same short-circuit in the framed runtime used by `occurrenceFactAuthoritative?`. -/
theorem framed_decision_state_independent (profile : FrameRuntime.Profile)
    (state : OccurrenceAuxState) (left right : CanonicalRerootCursor) (order : Ordering)
    (hc : FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
        (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order)
    (hne : order ≠ Ordering.eq) :
    FrameRuntime.decisionComplete? mol profile true state fuel left right =
      some { ordering := order } := by
  unfold FrameRuntime.decisionComplete?
  rw [hc]
  cases order with
  | lt => rfl
  | gt => rfl
  | eq => exact absurd rfl hne

theorem c2_pairs_unframed_state_independent (state : OccurrenceAuxState) :
    compareOccurrenceBranchesAuthoritative? mol state fuel clCursor middleCursor =
        some { ordering := Ordering.gt } ∧
      compareOccurrenceBranchesAuthoritative? mol state fuel clCursor methylCursor =
        some { ordering := Ordering.gt } ∧
      compareOccurrenceBranchesAuthoritative? mol state fuel clCursor hCursor =
        some { ordering := Ordering.gt } ∧
      compareOccurrenceBranchesAuthoritative? mol state fuel middleCursor methylCursor =
        some { ordering := Ordering.gt } ∧
      compareOccurrenceBranchesAuthoritative? mol state fuel middleCursor hCursor =
        some { ordering := Ordering.gt } ∧
      compareOccurrenceBranchesAuthoritative? mol state fuel methylCursor hCursor =
        some { ordering := Ordering.gt } :=
  ⟨c2_pair_state_independent state clCursor middleCursor (by decide),
   c2_pair_state_independent state clCursor methylCursor (by decide),
   c2_pair_state_independent state clCursor hCursor (by decide),
   c2_pair_state_independent state middleCursor methylCursor (by decide),
   c2_pair_state_independent state middleCursor hCursor (by decide),
   c2_pair_state_independent state methylCursor hCursor (by decide)⟩

theorem c2_pairs_framed_state_independent (state : OccurrenceAuxState) :
    FrameRuntime.decisionComplete? mol c2Profile true state fuel clCursor middleCursor =
        some { ordering := Ordering.gt } ∧
      FrameRuntime.decisionComplete? mol c2Profile true state fuel clCursor methylCursor =
        some { ordering := Ordering.gt } ∧
      FrameRuntime.decisionComplete? mol c2Profile true state fuel clCursor hCursor =
        some { ordering := Ordering.gt } ∧
      FrameRuntime.decisionComplete? mol c2Profile true state fuel middleCursor methylCursor =
        some { ordering := Ordering.gt } ∧
      FrameRuntime.decisionComplete? mol c2Profile true state fuel middleCursor hCursor =
        some { ordering := Ordering.gt } ∧
      FrameRuntime.decisionComplete? mol c2Profile true state fuel methylCursor hCursor =
        some { ordering := Ordering.gt } :=
  ⟨framed_decision_state_independent c2Profile state clCursor middleCursor Ordering.gt
      (by decide) (by decide),
   framed_decision_state_independent c2Profile state clCursor methylCursor Ordering.gt
      (by decide) (by decide),
   framed_decision_state_independent c2Profile state clCursor hCursor Ordering.gt
      (by decide) (by decide),
   framed_decision_state_independent c2Profile state middleCursor methylCursor Ordering.gt
      (by decide) (by decide),
   framed_decision_state_independent c2Profile state middleCursor hCursor Ordering.gt
      (by decide) (by decide),
   framed_decision_state_independent c2Profile state methylCursor hCursor Ordering.gt
      (by decide) (by decide)⟩

/-- The legacy and production empty-state evaluations agree, and the real production state
`[c3Fact, c0AuxFact]` leaves C2's fact unchanged. -/
theorem c2_empty_state_facts :
    legacyOccurrenceFactAuthoritative? mol fuel [] c2Root = some c2Fact ∧
      occurrenceFactAuthoritative? mol fuel [] c2Root = some c2Fact ∧
      occurrenceFactAuthoritative? mol fuel [c3Fact, c0AuxFact] c2Root = some c2Fact := by
  decide

/-! ## Auxiliary eligibility and the actual production state for center C2 -/

/-- The auxiliary filter selects exactly C0 (atom 3) and C3 (atom 4), and the production builder
returns the deepest-first state `[c3Fact, c0AuxFact]`. -/
theorem aux_state_production :
    (((collectCanonicalTreeAuthoritative mol fuel [c2Root]).getD []).filter
        (fun node => node.provenance == CanonicalNodeProvenance.realAtom &&
          node.atom != c2Atom &&
          (mol.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome))).map
        (fun node => node.atom) = [middleAtom, c3Atom] ∧
      buildOccurrenceAuxStateFullyAuthoritative? mol fuel c2Atom =
        some [c3Fact, c0AuxFact] := by
  decide

/-- The production state carries labels at atoms 4 and 3 only; it contains no C2 label and does
contain the C3 occurrence label. -/
theorem aux_state_properties :
    ([c3Fact, c0AuxFact] : OccurrenceAuxState).map (fun fact => fact.atom) =
        [c3Atom, middleAtom] ∧
      OccurrenceAuxState.factAt? [c3Fact, c0AuxFact] c2Root = none ∧
      OccurrenceAuxState.factAt? [c3Fact, c0AuxFact] c3Node = some c3Fact := by
  decide

/-- C3 is labelled first from the empty state; with the empty state the actual framed C0
comparison ties constitutionally and is refused; with the real batch state `[c3Fact]` C0 receives
its occurrence-local `S` label. -/
theorem occurrence_production_facts :
    occurrenceFactAuthoritative? mol fuel [] c3Node = some c3Fact ∧
      occurrenceFactAuthoritative? mol fuel [] c0Node = none ∧
      occurrenceFactAuthoritative? mol fuel [c3Fact] c0Node = some c0AuxFact := by
  decide

/-- The full production entry point returns the final C2 descriptor `R`, with two descriptor-
dependent pairs recorded from the actual state. -/
theorem production_fact_c2 :
    tetrahedralOccurrenceFactAuthoritative? mol fuel c2Atom = some c2ProductionFact := by
  decide

/-- Consequently the production descriptor at C2 is `R`. -/
theorem c2_final_descriptor_R :
    (tetrahedralOccurrenceFactAuthoritative? mol fuel c2Atom).map
        (fun fact => fact.descriptor) = some RS.R := by
  rw [production_fact_c2]
  rfl

/-! ## B. Implemented total-2018 Rule-1b profile at C0 (unframed cursor protocol) -/

/-- Both C0 arms are real-atom nodes (no duplicate/placeholder node, so 2013 duplicate-only
Rule 1b has nothing to act on); Rule 1a ties; the implemented total profile separates them by
stored root distance 0 vs 2; the full unframed constitutional stage is strict; the legacy empty-
state C0 label is the occurrence-local `c0LegacyFact`; and the original root has no incoming
parent.  This is a statement about the current runtime profile. -/
theorem c0_unframed_profile :
    c2ArmCursor.node.provenance = CanonicalNodeProvenance.realAtom ∧
      c3ArmCursor.node.provenance = CanonicalNodeProvenance.realAtom ∧
      compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1a
          c2ArmCursor c3ArmCursor = some Ordering.eq ∧
      compareCursorBranchAtAuthoritative? mol fuel CanonicalRuleStage.rule1b
          c2ArmCursor c3ArmCursor = some Ordering.gt ∧
      certifiedConstitutionalStageAuthoritative? mol fuel c2ArmCursor c3ArmCursor =
        some Ordering.gt ∧
      (c2ArmCursor.node).rule1bRootDistance = 0 ∧
      (c3ArmCursor.node).rule1bRootDistance = 2 ∧
      legacyOccurrenceFactAuthoritative? mol fuel [] c0Node = some c0LegacyFact ∧
      canonicalOriginalParent? c2Root = none := by
  decide

/-- Under the implemented total profile the unframed C0-arm decision is state-independent. -/
theorem c0_unframed_state_independent (state : OccurrenceAuxState) :
    compareOccurrenceBranchesAuthoritative? mol state fuel c2ArmCursor c3ArmCursor =
      some { ordering := Ordering.gt } :=
  c2_pair_state_independent state c2ArmCursor c3ArmCursor (by decide)

/-- Every node of the C2-rooted canonical tree is either non-tetrahedral or one of the three
source stereocenters C2, C0, C3. -/
theorem tetrahedral_nodes_are_center_c0_or_c3 :
    ((collectCanonicalTreeAuthoritative mol fuel [c2Root]).getD []).all
      (fun node =>
        decide (!(mol.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome) ∨
          node.atom = c2Atom ∨ node.atom = middleAtom ∨ node.atom = c3Atom)) = true := by
  decide

/-! ## C. The selected framed runtime at C0 reads auxiliary state -/

/-- Both C0 arms observe frame distance 1, tie at Rule 1a and tie at the framed constitutional
stage: they are constitutionally identical `C(H)(Cl)(CH3)` arms. -/
theorem c0_framed_constitutional_tie :
    CanonicalComparisonFrame.observeNode c0Profile.frame c2Root = some 1 ∧
      CanonicalComparisonFrame.observeNode c0Profile.frame c3Node = some 1 ∧
      FrameRuntime.compareBranch? mol c0Profile true fuel CanonicalRuleStage.rule1a
          (FrameRuntime.Cursor.actual c2ArmCursor) (FrameRuntime.Cursor.actual c3ArmCursor) =
        some Ordering.eq ∧
      FrameRuntime.compareBranch? mol c0Profile true fuel CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual c2ArmCursor) (FrameRuntime.Cursor.actual c3ArmCursor) =
        some Ordering.eq := by
  decide

/-- The actual framed C0 decision is state-sensitive: the empty state ties, the real batch state
`[c3Fact]` separates (`lt`) by Rule 4a priorities 0 (C2 arm, no fact) vs 2 (C3 arm, uppercase
fact).  In the production state the C2 arm has no fact and the C3 arm has `c3Fact`.  Both states
are actually produced by the machinery, not synthetic perturbations. -/
theorem c0_framed_state_sensitivity :
    FrameRuntime.decisionComplete? mol c0Profile true [] fuel c2ArmCursor c3ArmCursor =
        some { ordering := Ordering.eq } ∧
      FrameRuntime.decisionComplete? mol c0Profile true [c3Fact] fuel c2ArmCursor c3ArmCursor =
        some { ordering := Ordering.lt } ∧
      OccurrenceAuxState.factAt? [c3Fact, c0AuxFact] c2ArmCursor.node = none ∧
      OccurrenceAuxState.factAt? [c3Fact, c0AuxFact] c3ArmCursor.node = some c3Fact ∧
      occurrenceNodePriority [c3Fact] RawDescriptorRuleStage.rule4a true c2ArmCursor = 0 ∧
      occurrenceNodePriority [c3Fact] RawDescriptorRuleStage.rule4a false c3ArmCursor = 2 := by
  decide

end ConstitutionalRootStageAvailability
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.source_parse
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.materialization_validation
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.profiles_resolve
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.frame_membership
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_rule1a_strict
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_constitutional_strict
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_framed_rule1a_strict
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_framed_constitutional_strict
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_descriptor_from_parity
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_pair_state_independent
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.framed_decision_state_independent
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_pairs_unframed_state_independent
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_pairs_framed_state_independent
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_empty_state_facts
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.aux_state_production
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.aux_state_properties
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.occurrence_production_facts
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.production_fact_c2
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c2_final_descriptor_R
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c0_unframed_profile
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c0_unframed_state_independent
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.tetrahedral_nodes_are_center_c0_or_c3
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c0_framed_constitutional_tie
assert_kernel_only TetraStereo.OneCenter.ConstitutionalRootStageAvailability.c0_framed_state_sensitivity
