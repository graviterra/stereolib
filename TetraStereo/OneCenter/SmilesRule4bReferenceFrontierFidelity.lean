import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.OneCenter.LocalizedPseudoasymmetricClassification

/-!
# Live Rule-4b reference frontier fidelity

`SmilesTetrahedral.occurrenceRule4bReferences` collects uppercase descriptor facts from the whole
first descriptor-bearing breadth-first frontier of a ligand occurrence and applies the
P-92.5.2.1(b)/(c) majority rule to that entire frontier.  P-92.5.2.1(a), however, first restricts
the reading to the highest-rank chiral node(s) of the ligand hierarchy; nodes at a lower rank must
not enter the population at all.

This module builds one concrete acyclic molecule on which the two readings genuinely disagree at a
ranked frontier, and records, by kernel evaluation (`decide`),:

* the live references and the source-faithful ranked references for the same two ligand
  occurrences,
* the live public branch comparisons and the corresponding comparisons with the source reference
  selection,
* the resulting public descriptor fact at the centre, and the descriptor obtained with the ranked
  selection,

together with structural admission and the exact Rule-4a precedence and two-reference ranking that
must be preserved.

The source reading is expressed through the existing ranked machinery
`localizedFirstChiralRankPopulationInLayer` / `localizedRule4bReferencesFromRankedLabels` applied to
the canonical branch key's `sourceNodes` layers, so the repair route uses existing ranked reference
machinery only.

## Geometry of the witness

Atom `0` is a `clockwise` carbon carrying H (`1`), formyl carbon (`2`, double-bonded to `3`), and
two constitutionally identical nitrogen ligands (`5`, `24`).  The formyl group keeps the centre
outside the generated real-tree profile, so the public evaluator uses the legacy occurrence path
that contains `occurrenceRule4bReferences`.  Each nitrogen ligand has two nitrogen children
(`6`,`15` and `25`,`34`); each of those carries two chiral halocarbons.  The left ligand's four
chiral halocarbons have descriptors `R,R,R,S`; the right ligand's have `S,S,R,R`.

Consequently the live whole-frontier majority yields `[R]` on the left and the exact tie `[R,S]`
on the right, while the ranked source reading selects only the highest-rank chiral path in each
sphere (`[S]` on the left and `[R]` on the right).  The differing reference populations change the
Rule-4b comparison from `gt` to `lt`, and the emitted centre descriptor from `S` to `R`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace TetraStereo.OneCenter

open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## A concrete admissible molecule -/

private def tetra (parity : TetrahedralInputParity) : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some parity }

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C
private def nitrogen : AtomSpec := AtomSpec.aliphatic Element.N
private def oxygen : AtomSpec := AtomSpec.aliphatic Element.O
private def hydrogen : AtomSpec := AtomSpec.aliphatic Element.H
private def fluorine : AtomSpec := AtomSpec.aliphatic Element.F
private def chlorine : AtomSpec := AtomSpec.aliphatic Element.Cl
private def bromine : AtomSpec := AtomSpec.aliphatic Element.Br
private def iodine : AtomSpec := AtomSpec.aliphatic Element.I

/-- Atom indices used by the witness.

Centre 0 has ligands H (1), formyl carbon (2), and two constitutionally identical nitrogen
ligands (5 and 24).  Each nitrogen ligand has two nitrogen children; each of those carries two
chiral halocarbon nodes.  The formyl C=O double bond keeps every centre outside the generated
real-tree profile, so the public evaluator uses the legacy occurrence path containing
`occurrenceRule4bReferences`. -/
def witnessMolecule : RawMolecule where
  atoms :=
    [ tetra .clockwise,            -- 0  centre M
      hydrogen,                    -- 1  H
      carbon,                      -- 2  formyl carbon V
      oxygen,                      -- 3  O (double bond)
      hydrogen,                    -- 4  formyl H
      nitrogen,                    -- 5  L
      nitrogen,                    -- 6  X
      tetra .clockwise,            -- 7  C1
      fluorine,                    -- 8
      chlorine,                    -- 9
      bromine,                     -- 10
      tetra .clockwise,            -- 11 C2
      fluorine,                    -- 12
      chlorine,                    -- 13
      iodine,                      -- 14
      nitrogen,                    -- 15 Y
      tetra .clockwise,            -- 16 C3
      fluorine,                    -- 17
      bromine,                     -- 18
      iodine,                      -- 19
      tetra .anticlockwise,        -- 20 C4
      chlorine,                    -- 21
      bromine,                     -- 22
      iodine,                      -- 23
      nitrogen,                    -- 24 R
      nitrogen,                    -- 25 X'
      tetra .anticlockwise,        -- 26 C1'
      fluorine,                    -- 27
      chlorine,                    -- 28
      bromine,                     -- 29
      tetra .anticlockwise,        -- 30 C2'
      fluorine,                    -- 31
      chlorine,                    -- 32
      iodine,                      -- 33
      nitrogen,                    -- 34 Y'
      tetra .clockwise,            -- 35 C3'
      fluorine,                    -- 36
      bromine,                     -- 37
      iodine,                      -- 38
      tetra .clockwise,            -- 39 C4'
      chlorine,                    -- 40
      bromine,                     -- 41
      iodine ]                     -- 42
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 5, kind := .single },
      { source := 0, target := 24, kind := .single },
      { source := 2, target := 3, kind := .double },
      { source := 2, target := 4, kind := .single },
      { source := 5, target := 6, kind := .single },
      { source := 5, target := 15, kind := .single },
      { source := 6, target := 7, kind := .single },
      { source := 6, target := 11, kind := .single },
      { source := 7, target := 8, kind := .single },
      { source := 7, target := 9, kind := .single },
      { source := 7, target := 10, kind := .single },
      { source := 11, target := 12, kind := .single },
      { source := 11, target := 13, kind := .single },
      { source := 11, target := 14, kind := .single },
      { source := 15, target := 16, kind := .single },
      { source := 15, target := 20, kind := .single },
      { source := 16, target := 17, kind := .single },
      { source := 16, target := 18, kind := .single },
      { source := 16, target := 19, kind := .single },
      { source := 20, target := 21, kind := .single },
      { source := 20, target := 22, kind := .single },
      { source := 20, target := 23, kind := .single },
      { source := 24, target := 25, kind := .single },
      { source := 24, target := 34, kind := .single },
      { source := 25, target := 26, kind := .single },
      { source := 25, target := 30, kind := .single },
      { source := 26, target := 27, kind := .single },
      { source := 26, target := 28, kind := .single },
      { source := 26, target := 29, kind := .single },
      { source := 30, target := 31, kind := .single },
      { source := 30, target := 32, kind := .single },
      { source := 30, target := 33, kind := .single },
      { source := 34, target := 35, kind := .single },
      { source := 34, target := 39, kind := .single },
      { source := 35, target := 36, kind := .single },
      { source := 35, target := 37, kind := .single },
      { source := 35, target := 38, kind := .single },
      { source := 39, target := 40, kind := .single },
      { source := 39, target := 41, kind := .single },
      { source := 39, target := 42, kind := .single } ]

def centerNode : RawMolecule.CanonicalBranchNode := canonicalCenterRoot 0

def leftCursor : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 5, previous? := some centerNode }

def rightCursor : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 24, previous? := some centerNode }

/-! ## The actual auxiliary environment

`buildOccurrenceAuxStateFullyAuthoritative?` is the live builder used by the public evaluator.
The list below is *not* a fallback: `witnessAuxState_build` proves that the builder returns exactly
this list.  Every deeper label is one of the eight chiral halocarbon nodes, with the exact
occurrence history of the centre-rooted canonical tree. -/

def witnessAuxState : OccurrenceAuxState :=
  [ { key := { history := [7, 6, 5, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 7, descriptor := RS.R, uppercase := true,
      priorityPositions := [3, 2, 1, 0] },
    { key := { history := [11, 6, 5, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 11, descriptor := RS.R, uppercase := true,
      priorityPositions := [3, 2, 1, 0] },
    { key := { history := [16, 15, 5, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 16, descriptor := RS.R, uppercase := true,
      priorityPositions := [3, 2, 1, 0] },
    { key := { history := [20, 15, 5, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 20, descriptor := RS.S, uppercase := true,
      priorityPositions := [3, 2, 1, 0] },
    { key := { history := [26, 25, 24, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 26, descriptor := RS.S, uppercase := true,
      priorityPositions := [3, 2, 1, 0] },
    { key := { history := [30, 25, 24, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 30, descriptor := RS.S, uppercase := true,
      priorityPositions := [3, 2, 1, 0] },
    { key := { history := [35, 34, 24, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 35, descriptor := RS.R, uppercase := true,
      priorityPositions := [3, 2, 1, 0] },
    { key := { history := [39, 34, 24, 0],
               provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
      atom := 39, descriptor := RS.R, uppercase := true,
      priorityPositions := [3, 2, 1, 0] } ]

/-! ## Source-faithful ranked reference selection -/

/-- Label one occurrence for the ranked source reading.  Uppercase facts become chiral labels,
lowercase facts become pseudoasymmetric labels (which P-92.5.2.1(a) does not use as Rule-4b
references), and occurrences without a real-atom factorial label are unlabelled. -/
def occurrenceSourceLabel? (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) :
    Option LocalizedAuxiliaryLabel :=
  match node.provenance, state.factAt? node with
  | RawMolecule.CanonicalNodeProvenance.realAtom, some fact =>
      if fact.uppercase then
        some (.chiral fact.descriptor)
      else
        some (.pseudoasymmetric (pseudoRSOfRS fact.descriptor))
  | _, _ => none

/-- The exact hierarchy-rank-addressed source layers of one ligand occurrence.  `sourceNodes`
already orders each sphere by the ranked sibling slots assigned by `buildCanonicalBranchKey`, and
the positional path is the P-92.5.2.1 hierarchy rank. -/
def occurrenceSourceRankedLayers (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (node : RawMolecule.CanonicalBranchNode) :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :=
  match mol.buildCanonicalBranchKey (mol.atomCount + fuel) fuel node with
  | none => []
  | some key =>
      key.sourceNodes.map fun layer =>
        layer.map fun entry => (entry.1, occurrenceSourceLabel? state entry.2)

/-- P-92.5.2.1(a)-(c) reference selection: first uppercase chiral rank class, majority within the
equivalent class, both descriptors on an exact tie. -/
def occurrenceSourceRule4bReferences (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (cursor : CanonicalRerootCursor) : List RS :=
  localizedRule4bReferencesFromRankedLabels
    (occurrenceSourceRankedLayers mol state fuel cursor.node)

/-- The live Rule-4b comparator with only the selected-reference computation replaced by the
ranked source reading.  Every case, including the two-reference ranking, is retained. -/
def compareOccurrenceRule4bSource? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  let leftReferences := occurrenceSourceRule4bReferences mol state fuel left
  let rightReferences := occurrenceSourceRule4bReferences mol state fuel right
  match leftReferences, rightReferences with
  | [], [] => some Ordering.eq
  | [_], [_, _] => some Ordering.gt
  | [_, _], [_] => some Ordering.lt
  | [leftReference], [rightReference] =>
      compareOccurrenceDescriptorAtTiedRoot? mol state fuel
        (.rule4b leftReference rightReference) left right
  | [_, _], [_, _] => do
      let rankedLeft ← rankOccurrenceRule4bReferences? mol state fuel left leftReferences
      let rankedRight ← rankOccurrenceRule4bReferences? mol state fuel right rightReferences
      let first ← compareOccurrenceDescriptorAtTiedRoot? mol state fuel
        (.rule4b (rankedLeft.getD 0 RS.R) (rankedRight.getD 0 RS.R)) left right
      if first != Ordering.eq then some first else
        compareOccurrenceDescriptorAtTiedRoot? mol state fuel
          (.rule4b (rankedLeft.getD 1 RS.S) (rankedRight.getD 1 RS.S)) left right
  | _, _ => none

/-- The live branch comparator with only Rule 4b's reference selection replaced.  Constitutional
tie handling, exact Rule-4a precedence, Rule 4c and Rule 5 are unchanged. -/
def compareOccurrenceBranchesSource? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option OccurrenceComparison := do
  let constitutional ← certifiedConstitutionalStage? mol fuel left right
  if constitutional != Ordering.eq then return { ordering := constitutional }
  let rule4a ← compareOccurrenceDescriptorAtTiedRoot? mol state fuel .rule4a left right
  if rule4a != Ordering.eq then return { ordering := rule4a }
  let rule4b ← compareOccurrenceRule4bSource? mol state fuel left right
  if rule4b != Ordering.eq then return { ordering := rule4b }
  let rule4c ←
    if state.any fun fact => !fact.uppercase then
      let before := compareOccurrenceDescriptorBranchAt mol state fuel .rule4c
      compareOccurrenceRule4cWithWitness mol state before before fuel [(left, right)]
    else some { ordering := Ordering.eq }
  if rule4c.ordering != Ordering.eq then
    return { ordering := rule4c.ordering, rule4cCarrier? := rule4c.carrier? }
  let rule5 ← compareOccurrenceRule5? mol state fuel left right
  some { ordering := rule5.ordering, pseudo := rule5.pseudo }

def insertOccurrenceTrackedSource? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ)
    (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor × ℕ)
  | [] => some ([candidate], 0)
  | head :: tail => do
      let decision ← compareOccurrenceBranchesSource? mol state fuel candidate head
      let observed := if decision.pseudo then 1 else 0
      if decision.ordering == Ordering.lt then
        let inserted ← insertOccurrenceTrackedSource? mol state fuel candidate tail
        some (head :: inserted.1, observed + inserted.2)
      else
        some (candidate :: head :: tail, observed)

def sortOccurrencesTrackedSource? (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : ℕ) :
    List CanonicalRerootCursor → Option (List CanonicalRerootCursor × ℕ)
  | [] => some ([], 0)
  | cursor :: cursors => do
      let sorted ← sortOccurrencesTrackedSource? mol state fuel cursors
      let inserted ← insertOccurrenceTrackedSource? mol state fuel cursor sorted.1
      some (inserted.1, sorted.2 + inserted.2)

def compareOccurrenceAdjacentPairsSource? (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) :
    List CanonicalRerootCursor → Option (List (OccurrenceComparedPair mol state fuel))
  | [] | [_] => some []
  | left :: right :: remaining => do
      let decision ← compareOccurrenceBranchesSource? mol state fuel left right
      let deeper ← compareOccurrenceAdjacentPairsSource? mol state fuel (right :: remaining)
      some ({ left := left, right := right, decision := decision } :: deeper)

/-- The actual legacy public evaluator with the ranked Rule-4b reference selection. -/
def legacyOccurrenceFactSource? (mol : RawMolecule) (fuel : ℕ) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) : Option OccurrenceAuxFact := do
  let spec ← mol.atomAt? node.atom
  let parity ← spec.tetrahedral?
  let ligands := mol.ligandsWithLonePair node.atom
  let roots ← occurrenceLigandFrame? mol node
  let sorted ← sortOccurrencesTrackedSource? mol state fuel roots
  let positions ← sorted.1.mapM fun cursor =>
    (ligands.zipIdx.find? fun entry => entry.1 == cursor.node.atom).map Prod.snd
  let compared ← compareOccurrenceAdjacentPairsSource? mol state fuel sorted.1
  let finalDecisions := compared.map fun comparison => comparison.decision
  let strict := finalDecisions.all fun decision => decision.ordering != Ordering.eq
  let pseudoPairCount := (finalDecisions.filter fun decision => decision.pseudo).length
  if !strict then none else
    let rawDescriptor := RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven positions)
    some { key := canonicalOccurrenceKey node
           atom := node.atom
           descriptor := rawDescriptor
           uppercase := pseudoPairCount % 2 == 0
           priorityPositions := positions }

/-- Source-faithful counterpart of `tetrahedralOccurrenceFact?`, using the same actual auxiliary
state builder and the same public fact record. -/
def tetrahedralOccurrenceFactSource? (mol : RawMolecule) (fuel center : ℕ) :
    Option RawDescriptorFact := do
  let state ← buildOccurrenceAuxStateFullyAuthoritative? mol fuel center
  let fact ← legacyOccurrenceFactSource? mol fuel state (canonicalCenterRoot center)
  some { atom := center
         descriptor := fact.descriptor
         uppercase := fact.uppercase
         evidenceSize := max 1 state.length
         decisiveRule? := none
         descriptorDependentPairs := state.length
         priorityPositions := fact.priorityPositions }

/-! ## Kernel guards

All claims below are closed kernel computations (`decide`); no native evaluation or axioms are
used.  The first group establishes that the witness is a genuinely admissible input and that the
live builder actually succeeds with the pinned state. -/

theorem witness_atomCount : witnessMolecule.atomCount = 43 := by
  decide

theorem witness_admissible : witnessMolecule.admissible? = true := by
  decide

theorem witness_stereochemicalAdmissible :
    witnessMolecule.stereochemicalAdmissible? = true := by
  decide

/-- The centre is outside the generated real-tree profile, so the public evaluator really uses the
legacy occurrence path whose Rule-4b reference selection is `occurrenceRule4bReferences`. -/
theorem witness_profile_unavailable :
    FrameRuntime.profile? witnessMolecule centerNode = none := by
  decide

/-- The live fully authoritative builder succeeds and returns exactly the pinned state: no
`getD`/silent-empty fallback is involved. -/
theorem witnessAuxState_build :
    buildOccurrenceAuxStateFullyAuthoritative? witnessMolecule 8 0 =
      some witnessAuxState := by
  decide

theorem witnessAuxState_length : witnessAuxState.length = 8 := by
  decide

/-- The eight pinned facts, in builder order, with their exact live descriptors. -/
theorem witnessAuxState_chiral_facts :
    witnessAuxState.map (fun fact => (fact.atom, fact.descriptor, fact.uppercase)) =
      [(7, RS.R, true), (11, RS.R, true), (16, RS.R, true), (20, RS.S, true),
       (26, RS.S, true), (30, RS.S, true), (35, RS.R, true), (39, RS.R, true)] := by
  decide

/-! ## Live versus ranked reference populations -/

/-- Whole-frontier majority on the left ligand: three `R` and one `S`. -/
theorem live_left_references :
    occurrenceRule4bReferences witnessMolecule witnessAuxState 8 [leftCursor] = [RS.R] := by
  decide

/-- Whole-frontier majority on the right ligand is an exact `R/S` tie. -/
theorem live_right_references :
    occurrenceRule4bReferences witnessMolecule witnessAuxState 8 [rightCursor] =
      [RS.R, RS.S] := by
  decide

/-- Ranked source reading on the left ligand: the highest-rank chiral path `[0,0]` is atom 20,
whose descriptor is `S`; no lower-rank `R` enters the population. -/
theorem source_left_references :
    occurrenceSourceRule4bReferences witnessMolecule witnessAuxState 8 leftCursor = [RS.S] := by
  decide

/-- Ranked source reading on the right ligand: the highest-rank chiral path `[0,0]` is atom 39,
whose descriptor is `R`. -/
theorem source_right_references :
    occurrenceSourceRule4bReferences witnessMolecule witnessAuxState 8 rightCursor = [RS.R] := by
  decide

theorem left_reference_discrepancy :
    occurrenceRule4bReferences witnessMolecule witnessAuxState 8 [leftCursor] ≠
      occurrenceSourceRule4bReferences witnessMolecule witnessAuxState 8 leftCursor := by
  rw [live_left_references, source_left_references]
  decide

theorem right_reference_discrepancy :
    occurrenceRule4bReferences witnessMolecule witnessAuxState 8 [rightCursor] ≠
      occurrenceSourceRule4bReferences witnessMolecule witnessAuxState 8 rightCursor := by
  rw [live_right_references, source_right_references]
  decide

/-! ## Applicability: constitutional tie, Rule 4a tie, and the differing Rule-4b result -/

/-- Rules 1a--2 do not distinguish the two ligand occurrences. -/
theorem constitutional_tie :
    certifiedConstitutionalStage? witnessMolecule 8 leftCursor rightCursor =
      some Ordering.eq := by
  decide

/-- Rule 4a does not distinguish the two ligand occurrences.  Since the live and source branch
comparators differ only in their Rule-4b reference selection, the observed `gt`/`lt` split below
also forces this tie: a non-tied Rule 4a result would have been returned identically by both
comparators. -/
theorem rule4a_tie :
    compareOccurrenceDescriptorAtTiedRoot? witnessMolecule witnessAuxState 8 .rule4a
      leftCursor rightCursor = some Ordering.eq := by
  decide

theorem live_rule4b_comparison :
    compareOccurrenceRule4b? witnessMolecule witnessAuxState 8 leftCursor rightCursor =
      some Ordering.gt := by
  decide

theorem source_rule4b_comparison :
    compareOccurrenceRule4bSource? witnessMolecule witnessAuxState 8 leftCursor rightCursor =
      some Ordering.lt := by
  decide

theorem rule4b_comparison_discrepancy :
    compareOccurrenceRule4b? witnessMolecule witnessAuxState 8 leftCursor rightCursor ≠
      compareOccurrenceRule4bSource? witnessMolecule witnessAuxState 8 leftCursor rightCursor := by
  rw [live_rule4b_comparison, source_rule4b_comparison]
  decide

theorem live_branch_comparison :
    compareOccurrenceBranches? witnessMolecule witnessAuxState 8 leftCursor rightCursor =
      some { ordering := Ordering.gt, pseudo := false, rule4cCarrier? := none } := by
  decide

theorem source_branch_comparison :
    compareOccurrenceBranchesSource? witnessMolecule witnessAuxState 8 leftCursor rightCursor =
      some { ordering := Ordering.lt, pseudo := false, rule4cCarrier? := none } := by
  decide

/-- Replacing only the ranked reference selection reverses the public branch order. -/
theorem branch_order_reversed :
    (compareOccurrenceBranches? witnessMolecule witnessAuxState 8 leftCursor rightCursor).map
        (fun comparison => comparison.ordering) =
      some Ordering.gt ∧
    (compareOccurrenceBranchesSource? witnessMolecule witnessAuxState 8 leftCursor rightCursor).map
        (fun comparison => comparison.ordering) =
      some Ordering.lt := by
  constructor
  · rw [live_branch_comparison]; rfl
  · rw [source_branch_comparison]; rfl

/-! ## The emitted public centre fact differs -/

/-- Public centre fact obtained by the live whole-frontier reading: descriptor `S`. -/
theorem live_center_fact :
    tetrahedralOccurrenceFact? witnessMolecule 8 0 =
      some { atom := 0
             descriptor := RS.S
             uppercase := true
             evidenceSize := 8
             decisiveRule? := none
             descriptorDependentPairs := 8
             priorityPositions := [2, 3, 1, 0] } := by
  unfold tetrahedralOccurrenceFact? tetrahedralOccurrenceFactAuthoritative?
  rw [witnessAuxState_build]
  decide

/-- Centre fact obtained with the same builder and the same public record but the ranked source
reference selection: descriptor `R`. -/
theorem source_center_fact :
    tetrahedralOccurrenceFactSource? witnessMolecule 8 0 =
      some { atom := 0
             descriptor := RS.R
             uppercase := true
             evidenceSize := 8
             decisiveRule? := none
             descriptorDependentPairs := 8
             priorityPositions := [3, 2, 1, 0] } := by
  unfold tetrahedralOccurrenceFactSource?
  rw [witnessAuxState_build]
  decide

/-- The live public emitted fact is not the source-faithful ranked fact: the descriptor differs
(`S` versus `R`). -/
theorem public_fact_discrepancy :
    tetrahedralOccurrenceFact? witnessMolecule 8 0 ≠
      tetrahedralOccurrenceFactSource? witnessMolecule 8 0 := by
  rw [live_center_fact, source_center_fact]
  decide

end TetraStereo.OneCenter
