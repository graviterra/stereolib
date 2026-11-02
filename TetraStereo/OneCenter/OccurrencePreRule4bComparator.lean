


















































































import TetraStereo.OneCenter.Rule4bOccurrenceClassification
import TetraStereo.OneCenter.Rule4bFinitePoolOrderLaws

set_option autoImplicit false

namespace TetraStereo.OneCenter.OccurrencePreRule4b

open TetraStereo.OneCenter
open TetraStereo.Rule4bInheritedRankFrontier
open TetraStereo.Rule4bInheritedRankFrontier.FinitePool

universe u

/-! ## Cursor source data -/

/-- The original ligand atom of a cursor.

A cursor history starts at the current occurrence atom and ends at the stereogenic-unit root.
Reading one position before the last entry recovers the ligand through which the branch was
entered from the centre.  The value is invariant under every cursor move, because moving only
prepends or reconstructs one history entry. -/
def cursorLigand? (cursor : CanonicalRerootCursor) : Option ℕ :=
  match cursor.node.history.reverse with
  | _center :: ligand :: _ => some ligand
  | _ => none

/-- The actual children relation used by the pre-Rule-4b key and by the frontier adapter.

This is the zipper children relation (which includes the original-parent direction when the
cursor was entered from a child), with re-entry into the stereogenic centre cut in exactly the
same way as the corrected `rule3BranchChildren`.

The extra real-atom filter excludes only the reconstructed original parent when that parent is the
centre.  The root-attached reference erases exactly that real parent copy while retaining
multiple-bond and ring duplicates of the same atom; those carry non-`realAtom` provenance and are
therefore kept here. -/
def occurrenceBranchChildren (mol : RawMolecule) (center : ℕ)
    (cursor : CanonicalRerootCursor) : List CanonicalRerootCursor :=
  if cursor.node.atom == center then [] else
    (cursor.children mol).filter fun child =>
      child.node.atom != center ||
        child.node.provenance != RawMolecule.CanonicalNodeProvenance.realAtom

/-! ## Directed Rule-3 source observer (repair 2) -/

/-- A cursor whose stored predecessor is the historical parent: the `previous?` edge agrees with
the downward canonical tree, so the historical `rule3SourceUnitOfNode?` and the directed
`cursorRule3SourceUnitOfNode?` read the same physical Rule-3 unit. -/
def IsDirectedSourceCursor (cursor : CanonicalRerootCursor) : Prop :=
  ∃ previous : RawMolecule.CanonicalBranchNode, cursor.previous? = some previous ∧
    previous.atom = cursor.node.parent ∧ previous.history = cursor.node.history.drop 1

/-- Computable decision of `IsDirectedSourceCursor`.

A predecessor exists and is the historical parent in both atom and history.  This is the exact
structural condition under which the `previous?` edge is a downward canonical edge whose entry
substituent is recorded in the predecessor's history. -/
def isDirectedSourceCursor (cursor : CanonicalRerootCursor) : Bool :=
  match cursor.previous? with
  | none => false
  | some previous =>
      previous.atom == cursor.node.parent &&
        previous.history == cursor.node.history.drop 1

/-- The computable guard decides exactly the directedness proposition. -/
theorem isDirectedSourceCursor_eq_true_iff (cursor : CanonicalRerootCursor) :
    isDirectedSourceCursor cursor = true ↔ IsDirectedSourceCursor cursor := by
  unfold isDirectedSourceCursor IsDirectedSourceCursor
  cases h : cursor.previous? with
  | none => simp
  | some previous =>
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨atomAligned, historyAligned⟩
        exact ⟨previous, rfl, atomAligned, historyAligned⟩
      · rintro ⟨candidate, candidateEq, atomAligned, historyAligned⟩
        cases candidateEq
        exact ⟨atomAligned, historyAligned⟩

/-- The source-bound Rule-3 unit of one cursor, read from the actual incoming edge
`cursor.previous?` rather than the historical `node.parent`.

Only real nodes carry a physical observation.  `near` is the actual incoming atom, `far` the node
atom, and `entry?` the predecessor recorded in the incoming node's history.  The root cursor has
no incoming edge and is therefore never a source. -/
def cursorRule3SourceUnitOfNode? (mol : RawMolecule) (center : ℕ)
    (cursor : CanonicalRerootCursor) :
    Option ChemistryNormalizationResult.Rule3SourceUnit :=
  match cursor.previous? with
  | none => none
  | some previous =>
      if cursor.node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom &&
          cursor.node.atom != center && previous.atom != center &&
          mol.bondOrder previous.atom cursor.node.atom == 2 then
        some { near := previous.atom, far := cursor.node.atom,
               entry? := (previous.history.drop 1).head? }
      else none

/-- On a downward-directed cursor the directed reader agrees with the historical reader. -/
theorem cursorRule3SourceUnitOfNode?_eq_rule3SourceUnitOfNode?_of_directed
    {mol : RawMolecule} {center : ℕ} {cursor : CanonicalRerootCursor}
    (directed : IsDirectedSourceCursor cursor) :
    cursorRule3SourceUnitOfNode? mol center cursor =
      ChemistryNormalizationResult.rule3SourceUnitOfNode? mol center cursor.node := by
  rcases directed with ⟨previous, hPrev, hAtom, hHistory⟩
  have hEntry : previous.history.drop 1 = cursor.node.history.drop 2 := by
    rw [hHistory, List.drop_drop]
  unfold cursorRule3SourceUnitOfNode? ChemistryNormalizationResult.rule3SourceUnitOfNode?
  rw [hPrev]
  dsimp
  rw [hAtom, hEntry]

/-- The guarded source-bound Rule-3 observer at the cursor node.

The whole source read is gated on `isDirectedSourceCursor`.  For an unsupported cursor the result
is the outer `none` (unavailable evidence that refuses the whole key), never `some none`; the
source reader above is not silently treated as a determinate absence.

On a supported downward-directed cursor, `some none` is a determinate absence (a non-source node,
an excluded occurrence, or a double bond proved structurally unable to carry `E/Z`); the outer
`none` is unknown evidence for an applicable unit and must propagate as a refusal. -/
def cursorRule3Observer (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (center : ℕ) (policy : ChemistryNormalizationResult.Rule3CenterPolicy) (ligand : ℕ)
    (cursor : CanonicalRerootCursor) :
    Option (Option RawMolecule.CanonicalRule3Observation) :=
  if isDirectedSourceCursor cursor then
    match cursorRule3SourceUnitOfNode? mol center cursor with
    | none => some none
    | some unit =>
        if policy.excluded.contains (unit.addressedKey ligand) then some none
        else if ChemistryNormalizationResult.rule3UnitStructurallyInapplicable mol unit then
          some none
        else
          let tetrahedral := ChemistryNormalizationResult.rule3CenterTetrahedral mol center
          match ChemistryNormalizationResult.rule3CenterGeometry? result mol center tetrahedral
              policy.cyclic unit with
          | some geometry =>
              let geometry :=
                if policy.flipped.contains ligand && !policy.cyclic then
                  ChemistryNormalizationResult.flipRule3Geometry geometry
                else geometry
              some (some { unit := unit.key, near := unit.near, far := unit.far,
                           entry? := unit.entry?, geometry := geometry })
          | none => none
  else none

/-- On a downward-directed cursor the guarded observer is the historical branch observer. -/
theorem cursorRule3Observer_eq_rule3BranchObserver_of_directed
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {center : ℕ}
    {policy : ChemistryNormalizationResult.Rule3CenterPolicy} {ligand : ℕ}
    {cursor : CanonicalRerootCursor} (directed : IsDirectedSourceCursor cursor) :
    cursorRule3Observer result mol center policy ligand cursor =
      ChemistryNormalizationResult.rule3BranchObserver result mol center policy ligand cursor.node := by
  have guard : isDirectedSourceCursor cursor = true :=
    (isDirectedSourceCursor_eq_true_iff cursor).mpr directed
  unfold cursorRule3Observer ChemistryNormalizationResult.rule3BranchObserver
  rw [if_pos guard]
  rw [cursorRule3SourceUnitOfNode?_eq_rule3SourceUnitOfNode?_of_directed directed]
  rfl

/-- General unsupported-source refusal: a cursor that is not downward-directed yields the outer
`none`, not a determinate absence. -/
theorem cursorRule3Observer_eq_none_of_not_directed
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (center : ℕ)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy) (ligand : ℕ)
    (cursor : CanonicalRerootCursor)
    (undirected : isDirectedSourceCursor cursor = false) :
    cursorRule3Observer result mol center policy ligand cursor = none := by
  unfold cursorRule3Observer
  rw [if_neg (by simp [undirected])]

/-! ## Generic cursor-rooted Rules-1a--3 compilation

The existing `RawMolecule.buildCanonicalRule3Key?` is parameterised by a
`CanonicalBranchNode → List CanonicalBranchNode` child enumerator, which cannot express the
zipper's `previous?` cut.  The recursion below is the cursor analogue; it reuses the proved leaf
key (`canonicalRootKeyAuthoritative?`), assembly (`assembleCanonicalRule3Key`), descending sort
(`sortCanonicalRule3Keys`) and all their laws.  It is preserved as a standalone, generically
correct Rules-1a--3 cursor builder. -/

/-- Compile every cursor child once, failing if any child fails. -/
def compileCursorRule3Children
    (compile : CanonicalRerootCursor → Option RawMolecule.CanonicalRule3Key) :
    List CanonicalRerootCursor → Option (List RawMolecule.CanonicalRule3Key)
  | [] => some []
  | cursor :: rest => do
      let key ← compile cursor
      let keys ← compileCursorRule3Children compile rest
      some (key :: keys)

/-- Compile one cursor-rooted Rules-1a--3 hierarchy.

`observe cursor = none` is unavailable required evidence and refuses.  `some none` is a justified
determinate absence.  Zero fuel succeeds exactly at a cursor with no children. -/
def buildCursorRule3Key? (mol : RawMolecule)
    (children : CanonicalRerootCursor → List CanonicalRerootCursor)
    (observe : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation)) :
    ℕ → CanonicalRerootCursor → Option RawMolecule.CanonicalRule3Key
  | 0, cursor =>
      match observe cursor with
      | none => none
      | some rootObservation =>
          match children cursor with
          | [] =>
              match mol.canonicalRootKeyAuthoritative? cursor.node true with
              | none => none
              | some root =>
                  some (RawMolecule.assembleCanonicalRule3Key root rootObservation [])
          | _ => none
  | fuel + 1, cursor =>
      match observe cursor with
      | none => none
      | some rootObservation =>
          match children cursor with
          | [] =>
              match mol.canonicalRootKeyAuthoritative? cursor.node true with
              | none => none
              | some root =>
                  some (RawMolecule.assembleCanonicalRule3Key root rootObservation [])
          | child :: rest =>
              match compileCursorRule3Children
                  (fun childCursor =>
                    buildCursorRule3Key? mol children observe fuel childCursor)
                  (child :: rest) with
              | none => none
              | some childKeys =>
                  match mol.canonicalRootKeyAuthoritative? cursor.node true with
                  | none => none
                  | some root =>
                      some (RawMolecule.assembleCanonicalRule3Key root rootObservation
                        (RawMolecule.sortCanonicalRule3Keys childKeys))

/-- An unresolved required observation refuses at every fuel. -/
theorem buildCursorRule3Key?_observe_none
    {mol : RawMolecule}
    {children : CanonicalRerootCursor → List CanonicalRerootCursor}
    {observe : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation)}
    {cursor : CanonicalRerootCursor} (unresolved : observe cursor = none) (fuel : ℕ) :
    buildCursorRule3Key? mol children observe fuel cursor = none := by
  cases fuel with
  | zero =>
      unfold buildCursorRule3Key?
      simp [unresolved]
  | succ fuel =>
      unfold buildCursorRule3Key?
      simp [unresolved]

/-- Every key produced by `compileCursorRule3Children` comes from an enumerated cursor. -/
theorem compileCursorRule3Children_member
    {compile : CanonicalRerootCursor → Option RawMolecule.CanonicalRule3Key}
    {cursors : List CanonicalRerootCursor} :
    ∀ {keys : List RawMolecule.CanonicalRule3Key},
      compileCursorRule3Children compile cursors = some keys →
      ∀ {key : RawMolecule.CanonicalRule3Key}, key ∈ keys →
        ∃ cursor ∈ cursors, compile cursor = some key := by
  induction cursors with
  | nil =>
      intro keys computed key member
      unfold compileCursorRule3Children at computed
      simp only [Option.some.injEq] at computed
      cases computed
      simp at member
  | cons cursor cursors inductionHypothesis =>
      intro keys computed key member
      unfold compileCursorRule3Children at computed
      cases cursorComputed : compile cursor with
      | none =>
          rw [cursorComputed] at computed
          dsimp at computed
          cases computed
      | some cursorKey =>
          rw [cursorComputed] at computed
          dsimp at computed
          cases restComputed : compileCursorRule3Children compile cursors with
          | none =>
              rw [restComputed] at computed
              dsimp at computed
              cases computed
          | some restKeys =>
              rw [restComputed] at computed
              dsimp at computed
              cases computed
              rcases List.mem_cons.mp member with same | later
              · exact ⟨cursor, List.mem_cons_self, by simpa [same] using cursorComputed⟩
              · obtain ⟨found, foundMember, foundComputed⟩ :=
                  inductionHypothesis restComputed (key := key) later
                exact ⟨found, List.mem_cons_of_mem cursor foundMember, foundComputed⟩

/-- Every successfully built cursor key is complete. -/
theorem buildCursorRule3Key?_complete {mol : RawMolecule}
    {children : CanonicalRerootCursor → List CanonicalRerootCursor}
    {observe : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation)} :
    ∀ (fuel : ℕ) (cursor : CanonicalRerootCursor)
      (key : RawMolecule.CanonicalRule3Key),
      buildCursorRule3Key? mol children observe fuel cursor = some key →
      key.constitutional.complete = true
  | 0, cursor, key, computed => by
      unfold buildCursorRule3Key? at computed
      cases observed : observe cursor with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childCursors : children cursor with
          | cons child rest =>
              rw [childCursors] at computed
              dsimp at computed
              cases computed
          | nil =>
              rw [childCursors] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  rw [RawMolecule.assembleCanonicalRule3Key_complete]
                  exact RawMolecule.canonicalRootKeyAuthoritative?_complete rootComputed
  | fuel + 1, cursor, key, computed => by
      unfold buildCursorRule3Key? at computed
      cases observed : observe cursor with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childCursors : children cursor with
          | nil =>
              rw [childCursors] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  rw [RawMolecule.assembleCanonicalRule3Key_complete]
                  exact RawMolecule.canonicalRootKeyAuthoritative?_complete rootComputed
          | cons child rest =>
              rw [childCursors] at computed
              dsimp at computed
              cases childKeysComputed : compileCursorRule3Children
                  (fun childCursor =>
                    buildCursorRule3Key? mol children observe fuel childCursor)
                  (child :: rest) with
              | none =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases computed
              | some childKeys =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
                  | none =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                  | some root =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                      rw [RawMolecule.assembleCanonicalRule3Key_complete]
                      exact RawMolecule.canonicalRootKeyAuthoritative?_complete rootComputed

/-- Every successfully built cursor key keeps its stored Rule-3 observations address-aligned with
the compared Rule-3 priority projection. -/
theorem buildCursorRule3Key?_rule3Aligned (mol : RawMolecule)
    (children : CanonicalRerootCursor → List CanonicalRerootCursor)
    (observe : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation)) :
    ∀ (fuel : ℕ) (cursor : CanonicalRerootCursor)
      (key : RawMolecule.CanonicalRule3Key),
      buildCursorRule3Key? mol children observe fuel cursor = some key →
      RawMolecule.CanonicalRule3Key.Rule3Aligned key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key computed
      unfold buildCursorRule3Key? at computed
      cases observed : observe cursor with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childCursors : children cursor with
          | cons child rest =>
              rw [childCursors] at computed
              dsimp at computed
              cases computed
          | nil =>
              rw [childCursors] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  exact RawMolecule.assembleCanonicalRule3Key_rule3Aligned root
                    rootObservation [] (by intro child member; simp at member)
  | succ fuel inductionHypothesis =>
      intro cursor key computed
      unfold buildCursorRule3Key? at computed
      cases observed : observe cursor with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childCursors : children cursor with
          | nil =>
              rw [childCursors] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  exact RawMolecule.assembleCanonicalRule3Key_rule3Aligned root
                    rootObservation [] (by intro child member; simp at member)
          | cons child rest =>
              rw [childCursors] at computed
              dsimp at computed
              cases childKeysComputed : compileCursorRule3Children
                  (fun childCursor =>
                    buildCursorRule3Key? mol children observe fuel childCursor)
                  (child :: rest) with
              | none =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases computed
              | some childKeys =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
                  | none =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                  | some root =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                      apply RawMolecule.assembleCanonicalRule3Key_rule3Aligned
                      intro builtChild member
                      have sortedMember : builtChild ∈ childKeys :=
                        (RawMolecule.sortCanonicalRule3Keys_perm childKeys).mem_iff.mp member
                      obtain ⟨sourceCursor, sourceMember, sourceComputed⟩ :=
                        compileCursorRule3Children_member childKeysComputed sortedMember
                      exact inductionHypothesis sourceCursor builtChild sourceComputed

/-! ## Honest Rule-4a occurrence resolution (repair 1) -/

/-- Occurrence-local Rule-4a class, obtained from the reviewed honest resolver.

`none` is unavailable evidence (a real-atom occurrence absent from the state), never a determinate
class.  `some nonstereogenic` arises only from non-real provenance; `some chiral` /
`some pseudoasymmetric` arise only from an actual recorded uppercase / lowercase fact. -/
def occurrenceRule4aKind? (state : OccurrenceAuxState) (cursor : CanonicalRerootCursor) :
    Option OfficialStereogenicUnitKind :=
  (occurrenceChiralityClass state cursor).rule4aKind

/-- A real-atom occurrence absent from the state is unavailable for Rule 4a. -/
theorem occurrenceRule4aKind?_eq_none_of_missing
    {state : OccurrenceAuxState} {cursor : CanonicalRerootCursor}
    (hProvenance : cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hMissing : state.factAt? cursor.node = none) :
    occurrenceRule4aKind? state cursor = none := by
  unfold occurrenceRule4aKind?
  rw [occurrenceChiralityClass_eq_unavailable_of_missing state cursor hProvenance hMissing]
  rfl

/-- A non-real occurrence is a determinate non-stereogenic Rule-4a unit. -/
theorem occurrenceRule4aKind?_eq_some_nonstereogenic_of_nonReal
    {state : OccurrenceAuxState} {cursor : CanonicalRerootCursor}
    (hNonReal : cursor.node.provenance ≠ RawMolecule.CanonicalNodeProvenance.realAtom) :
    occurrenceRule4aKind? state cursor = some OfficialStereogenicUnitKind.nonstereogenic := by
  unfold occurrenceRule4aKind?
  rw [occurrenceChiralityClass_eq_knownNonchiral_of_nonReal state cursor hNonReal]
  rfl

/-! ## Cumulative Rule-4a key -/

/-- One compiler-backed pre-Rule-4b key.

`rule3` is the existing `CanonicalRule3Key` (Rules 1a/1b/2 plus addressed Rule 3).  `rule4a` is
the cumulative, sibling-slot-addressed Rule-4a sphere projection of the same cursor tree: each
parent sorts child keys by the full comparator below *before* assigning slots and merging
descendant Rule-4a spheres. -/
structure OccurrencePreRule4bKey where
  rule3 : RawMolecule.CanonicalRule3Key
  rule4a : List (List (List ℕ × OfficialStereogenicUnitKind))
  deriving DecidableEq, Repr

/-- Rule-4a label comparator.  `Ordering.gt` means the left kind has higher Rule-4a priority. -/
def compareRule4aKind :
    OfficialStereogenicUnitKind → OfficialStereogenicUnitKind → Ordering :=
  Ordering.byKey OfficialStereogenicUnitKind.priority compare

theorem compareRule4aKind_eq_priority (left right : OfficialStereogenicUnitKind) :
    compareRule4aKind left right = compare left.priority right.priority :=
  rfl

/-- The priority projection computes exactly the official Rule-4a comparison. -/
theorem compareRule4aKind_eq_official (left right : OfficialStereogenicUnitKind) :
    compareRule4aKind left right = OfficialStereogenicUnitKind.compare left right := by
  cases left <;> cases right <;> rfl

theorem compareRule4aKind_transCmp : Std.TransCmp compareRule4aKind := by
  unfold compareRule4aKind
  infer_instance

/-- Complete pre-Rule-4b key comparison: Rules 1a/1b/2 and Rule 3 first, then Rule 4a.

`Ordering.gt` means the left key is senior, consistently with the runtime comparator. -/
def compareOccurrencePreRule4bKeys
    (left right : OccurrencePreRule4bKey) : Ordering :=
  compareLex
    (Ordering.byKey OccurrencePreRule4bKey.rule3 RawMolecule.compareCanonicalRule3Keys)
    (Ordering.byKey OccurrencePreRule4bKey.rule4a
      (RawMolecule.compareSparseCanonicalLayers compareRule4aKind))
    left right

/-- Once the Rule-3 key comparison decides, Rule 4a is never consulted. -/
theorem compareOccurrencePreRule4bKeys_eq_rule3_of_ne
    (left right : OccurrencePreRule4bKey)
    (different : RawMolecule.compareCanonicalRule3Keys left.rule3 right.rule3 ≠ Ordering.eq) :
    compareOccurrencePreRule4bKeys left right =
      RawMolecule.compareCanonicalRule3Keys left.rule3 right.rule3 := by
  unfold compareOccurrencePreRule4bKeys compareLex Ordering.byKey
  cases decided : RawMolecule.compareCanonicalRule3Keys left.rule3 right.rule3 with
  | eq => exact absurd decided different
  | lt => rfl
  | gt => rfl

/-- After a complete Rule-1a--3 tie, the key comparison is exactly the addressed Rule-4a
comparison. -/
theorem compareOccurrencePreRule4bKeys_eq_rule4a_of_rule3_eq
    (left right : OccurrencePreRule4bKey)
    (tie : RawMolecule.compareCanonicalRule3Keys left.rule3 right.rule3 = Ordering.eq) :
    compareOccurrencePreRule4bKeys left right =
      RawMolecule.compareSparseCanonicalLayers compareRule4aKind left.rule4a right.rule4a := by
  unfold compareOccurrencePreRule4bKeys compareLex Ordering.byKey
  rw [tie]
  rfl

/-- The key comparator inherits the proved transitivity of the canonical Rule-1a--3 key
comparator and of the addressed sparse-layer comparator. -/
theorem compareOccurrencePreRule4bKeys_transCmp :
    Std.TransCmp compareOccurrencePreRule4bKeys := by
  haveI : Std.TransCmp RawMolecule.compareCanonicalRule3Keys :=
    RawMolecule.compareCanonicalRule3Keys_transCmp
  haveI : Std.TransCmp compareRule4aKind := compareRule4aKind_transCmp
  unfold compareOccurrencePreRule4bKeys
  unfold RawMolecule.compareSparseCanonicalLayers
  unfold RawMolecule.compareSparseCanonicalLayer
  unfold RawMolecule.compareSparseCanonicalEntry
  unfold RawMolecule.compareCanonicalPath
  infer_instance

theorem compareOccurrencePreRule4bKeys_refl (key : OccurrencePreRule4bKey) :
    compareOccurrencePreRule4bKeys key key = Ordering.eq := by
  haveI : Std.TransCmp compareOccurrencePreRule4bKeys :=
    compareOccurrencePreRule4bKeys_transCmp
  exact Std.ReflCmp.compare_self (cmp := compareOccurrencePreRule4bKeys) (a := key)

/-! ## Descending cumulative sort -/

/-- Structural descending insertion by the complete cumulative comparator. -/
def insertOccurrencePreRule4bKey (key : OccurrencePreRule4bKey) :
    List OccurrencePreRule4bKey → List OccurrencePreRule4bKey
  | [] => [key]
  | head :: tail =>
      match compareOccurrencePreRule4bKeys key head with
      | .lt => head :: insertOccurrencePreRule4bKey key tail
      | .eq | .gt => key :: head :: tail

/-- Structural descending sort used before a parent assigns sibling addresses. -/
def sortOccurrencePreRule4bKeys : List OccurrencePreRule4bKey → List OccurrencePreRule4bKey
  | [] => []
  | key :: keys => insertOccurrencePreRule4bKey key (sortOccurrencePreRule4bKeys keys)

theorem insertOccurrencePreRule4bKey_perm (key : OccurrencePreRule4bKey) :
    ∀ keys, (insertOccurrencePreRule4bKey key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertOccurrencePreRule4bKey
      cases comparison : compareOccurrencePreRule4bKeys key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head (insertOccurrencePreRule4bKey_perm key tail)).trans
            (List.Perm.swap key head tail)

theorem sortOccurrencePreRule4bKeys_perm (keys : List OccurrencePreRule4bKey) :
    (sortOccurrencePreRule4bKeys keys).Perm keys := by
  induction keys with
  | nil => exact List.Perm.refl []
  | cons key keys inductionHypothesis =>
      exact (insertOccurrencePreRule4bKey_perm key (sortOccurrencePreRule4bKeys keys)).trans
        (List.Perm.cons key inductionHypothesis)

/-- Descending cumulative sibling priority. -/
def OccurrencePreRule4bKeysDescending (keys : List OccurrencePreRule4bKey) : Prop :=
  keys.Pairwise fun left right =>
    compareOccurrencePreRule4bKeys left right ≠ Ordering.lt

theorem insertOccurrencePreRule4bKey_descending
    (key : OccurrencePreRule4bKey) :
    ∀ keys, OccurrencePreRule4bKeysDescending keys →
      OccurrencePreRule4bKeysDescending (insertOccurrencePreRule4bKey key keys)
  | [], _ => by
      simp [insertOccurrencePreRule4bKey, OccurrencePreRule4bKeysDescending]
  | head :: tail, sorted => by
      letI : Std.TransCmp compareOccurrencePreRule4bKeys :=
        compareOccurrencePreRule4bKeys_transCmp
      have headOverTail : ∀ observed ∈ tail,
          compareOccurrencePreRule4bKeys head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : OccurrencePreRule4bKeysDescending tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertOccurrencePreRule4bKey
      cases comparison : compareOccurrencePreRule4bKeys key head with
      | gt =>
          rw [OccurrencePreRule4bKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [OccurrencePreRule4bKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted :=
            insertOccurrencePreRule4bKey_descending key tail tailSorted
          rw [OccurrencePreRule4bKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation := insertOccurrencePreRule4bKey_perm key tail
            have sourcePresent : observed ∈ key :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse :
                  compareOccurrencePreRule4bKeys head key = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              exact by simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortOccurrencePreRule4bKeys_descending :
    ∀ keys, OccurrencePreRule4bKeysDescending (sortOccurrencePreRule4bKeys keys)
  | [] => by
      simp [sortOccurrencePreRule4bKeys, OccurrencePreRule4bKeysDescending]
  | key :: keys =>
      insertOccurrencePreRule4bKey_descending key
        (sortOccurrencePreRule4bKeys keys)
        (sortOccurrencePreRule4bKeys_descending keys)

/-! ## Cumulative Rule-4a merge and compilation -/

/-- Prefix one Rule-4a layer with its final sibling slot. -/
def prefixRule4aLayer (slot : ℕ) (layer : List (List ℕ × OfficialStereogenicUnitKind)) :
    List (List ℕ × OfficialStereogenicUnitKind) :=
  layer.map fun entry => (slot :: entry.1, entry.2)

/-- Maximum Rule-4a sphere count among child keys. -/
def occurrencePreRule4bChildLayerCount (children : List OccurrencePreRule4bKey) : ℕ :=
  children.foldl (fun longest child => max longest child.rule4a.length) 0

/-- Merge Rule-4a spheres beneath their final cumulative sibling slots. -/
def mergeOccurrencePreRule4bChildren (children : List OccurrencePreRule4bKey) :
    List (List (List ℕ × OfficialStereogenicUnitKind)) :=
  let count := occurrencePreRule4bChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      prefixRule4aLayer child.2 (child.1.rule4a.getD depth [])

/-- Compile every enumerated cursor child once, failing if any child fails. -/
def compileOccurrencePreRule4bChildren
    (compile : CanonicalRerootCursor → Option OccurrencePreRule4bKey) :
    List CanonicalRerootCursor → Option (List OccurrencePreRule4bKey)
  | [] => some []
  | cursor :: rest => do
      let key ← compile cursor
      let keys ← compileOccurrencePreRule4bChildren compile rest
      some (key :: keys)

/-- Compile one cursor-rooted cumulative pre-Rule-4b key.

At every node both the Rule-3 observation and the Rule-4a occurrence class are required: `none`
from either refuses the whole key.  Children are sorted by the full cumulative comparator before
sibling slots are assigned, so Rule-4a genuinely refines Rule-1a--3-tied sibling groups. -/
def buildOccurrencePreRule4bKey? (mol : RawMolecule)
    (children : CanonicalRerootCursor → List CanonicalRerootCursor)
    (observe3 : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation))
    (resolve4a : CanonicalRerootCursor → Option OfficialStereogenicUnitKind) :
    ℕ → CanonicalRerootCursor → Option OccurrencePreRule4bKey
  | 0, cursor =>
      match observe3 cursor with
      | none => none
      | some rootObservation =>
          match resolve4a cursor with
          | none => none
          | some rootKind =>
              match children cursor with
              | [] =>
                  match mol.canonicalRootKeyAuthoritative? cursor.node true with
                  | none => none
                  | some root =>
                      some { rule3 := RawMolecule.assembleCanonicalRule3Key root rootObservation []
                             rule4a := [[([], rootKind)]] }
              | _ => none
  | fuel + 1, cursor =>
      match observe3 cursor with
      | none => none
      | some rootObservation =>
          match resolve4a cursor with
          | none => none
          | some rootKind =>
              match children cursor with
              | [] =>
                  match mol.canonicalRootKeyAuthoritative? cursor.node true with
                  | none => none
                  | some root =>
                      some { rule3 := RawMolecule.assembleCanonicalRule3Key root rootObservation []
                             rule4a := [[([], rootKind)]] }
              | child :: rest =>
                  match compileOccurrencePreRule4bChildren
                      (fun c =>
                        buildOccurrencePreRule4bKey? mol children observe3 resolve4a fuel c)
                      (child :: rest) with
                  | none => none
                  | some childKeys =>
                      match mol.canonicalRootKeyAuthoritative? cursor.node true with
                      | none => none
                      | some root =>
                          let sorted := sortOccurrencePreRule4bKeys childKeys
                          some { rule3 := RawMolecule.assembleCanonicalRule3Key root
                                      rootObservation (sorted.map fun child => child.rule3)
                                 rule4a := [[([], rootKind)]] ++
                                   mergeOccurrencePreRule4bChildren sorted }

/-- An unresolved Rule-3 observation refuses the whole cumulative key. -/
theorem buildOccurrencePreRule4bKey?_observe_none
    {mol : RawMolecule}
    {children : CanonicalRerootCursor → List CanonicalRerootCursor}
    {observe3 : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation)}
    {resolve4a : CanonicalRerootCursor → Option OfficialStereogenicUnitKind}
    {cursor : CanonicalRerootCursor} (unresolved : observe3 cursor = none) (fuel : ℕ) :
    buildOccurrencePreRule4bKey? mol children observe3 resolve4a fuel cursor = none := by
  cases fuel with
  | zero =>
      unfold buildOccurrencePreRule4bKey?
      simp [unresolved]
  | succ fuel =>
      unfold buildOccurrencePreRule4bKey?
      simp [unresolved]

/-- An unavailable Rule-4a occurrence class refuses the whole cumulative key. -/
theorem buildOccurrencePreRule4bKey?_resolve_none
    {mol : RawMolecule}
    {children : CanonicalRerootCursor → List CanonicalRerootCursor}
    {observe3 : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation)}
    {resolve4a : CanonicalRerootCursor → Option OfficialStereogenicUnitKind}
    {cursor : CanonicalRerootCursor}
    {rootObservation : Option RawMolecule.CanonicalRule3Observation}
    (observed : observe3 cursor = some rootObservation)
    (unresolved : resolve4a cursor = none) (fuel : ℕ) :
    buildOccurrencePreRule4bKey? mol children observe3 resolve4a fuel cursor = none := by
  cases fuel with
  | zero =>
      unfold buildOccurrencePreRule4bKey?
      rw [observed]
      dsimp
      simp [unresolved]
  | succ fuel =>
      unfold buildOccurrencePreRule4bKey?
      rw [observed]
      dsimp
      simp [unresolved]

/-- Every successfully built cumulative key is complete. -/
theorem buildOccurrencePreRule4bKey?_complete {mol : RawMolecule}
    {children : CanonicalRerootCursor → List CanonicalRerootCursor}
    {observe3 : CanonicalRerootCursor →
      Option (Option RawMolecule.CanonicalRule3Observation)}
    {resolve4a : CanonicalRerootCursor → Option OfficialStereogenicUnitKind} :
    ∀ (fuel : ℕ) (cursor : CanonicalRerootCursor) (key : OccurrencePreRule4bKey),
      buildOccurrencePreRule4bKey? mol children observe3 resolve4a fuel cursor = some key →
      key.rule3.constitutional.complete = true
  | 0, cursor, key, computed => by
      unfold buildOccurrencePreRule4bKey? at computed
      cases observed : observe3 cursor with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases resolved : resolve4a cursor with
          | none =>
              rw [resolved] at computed
              dsimp at computed
              cases computed
          | some rootKind =>
              rw [resolved] at computed
              dsimp at computed
              cases childCursors : children cursor with
              | cons child rest =>
                  rw [childCursors] at computed
                  dsimp at computed
                  cases computed
              | nil =>
                  rw [childCursors] at computed
                  dsimp at computed
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
                  | none =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                  | some root =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                      rw [RawMolecule.assembleCanonicalRule3Key_complete]
                      exact RawMolecule.canonicalRootKeyAuthoritative?_complete rootComputed
  | fuel + 1, cursor, key, computed => by
      unfold buildOccurrencePreRule4bKey? at computed
      cases observed : observe3 cursor with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases resolved : resolve4a cursor with
          | none =>
              rw [resolved] at computed
              dsimp at computed
              cases computed
          | some rootKind =>
              rw [resolved] at computed
              dsimp at computed
              cases childCursors : children cursor with
              | nil =>
                  rw [childCursors] at computed
                  dsimp at computed
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
                  | none =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                  | some root =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                      rw [RawMolecule.assembleCanonicalRule3Key_complete]
                      exact RawMolecule.canonicalRootKeyAuthoritative?_complete rootComputed
              | cons child rest =>
                  rw [childCursors] at computed
                  dsimp at computed
                  cases childKeysComputed : compileOccurrencePreRule4bChildren
                      (fun c =>
                        buildOccurrencePreRule4bKey? mol children observe3 resolve4a fuel c)
                      (child :: rest) with
                  | none =>
                      rw [childKeysComputed] at computed
                      dsimp at computed
                      cases computed
                  | some childKeys =>
                      rw [childKeysComputed] at computed
                      dsimp at computed
                      cases rootComputed : mol.canonicalRootKeyAuthoritative? cursor.node true with
                      | none =>
                          rw [rootComputed] at computed
                          dsimp at computed
                          cases computed
                      | some root =>
                          rw [rootComputed] at computed
                          dsimp at computed
                          cases computed
                          rw [RawMolecule.assembleCanonicalRule3Key_complete]
                          exact RawMolecule.canonicalRootKeyAuthoritative?_complete rootComputed

/-! ## Explicit Rule-4a regression (repair 3) -/

/-- A single chiral label is senior over a single pseudoasymmetric label at equal addressed
position. -/
theorem compareRule4aSparseLayers_chiral_over_pseudoasymmetric :
    RawMolecule.compareSparseCanonicalLayers compareRule4aKind
      [[([], OfficialStereogenicUnitKind.chiral)]]
      [[([], OfficialStereogenicUnitKind.pseudoasymmetric)]] = Ordering.gt := by
  unfold RawMolecule.compareSparseCanonicalLayers
    RawMolecule.compareSparseCanonicalLayer
    RawMolecule.compareSparseCanonicalEntry
    RawMolecule.compareCanonicalPath
  rfl

/-- The counterexample pair under the full cumulative comparator: with a Rule-1a--3 tie, the
chiral sibling is senior over the pseudoasymmetric sibling. -/
theorem compareOccurrencePreRule4bKeys_chiral_over_pseudoasymmetric
    (rule3 : RawMolecule.CanonicalRule3Key) :
    compareOccurrencePreRule4bKeys
      { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] }
      { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.pseudoasymmetric)]] } =
        Ordering.gt := by
  have rule3refl : RawMolecule.compareCanonicalRule3Keys rule3 rule3 = Ordering.eq := by
    haveI : Std.TransCmp RawMolecule.compareCanonicalRule3Keys :=
      RawMolecule.compareCanonicalRule3Keys_transCmp
    exact Std.ReflCmp.compare_self (cmp := RawMolecule.compareCanonicalRule3Keys) (a := rule3)
  have h := compareOccurrencePreRule4bKeys_eq_rule4a_of_rule3_eq
    (left := { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] })
    (right := { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.pseudoasymmetric)]] })
    rule3refl
  rw [h]
  unfold RawMolecule.compareSparseCanonicalLayers
    RawMolecule.compareSparseCanonicalLayer
    RawMolecule.compareSparseCanonicalEntry
    RawMolecule.compareCanonicalPath
  rfl

/-- The reverse of the counterexample pair: the pseudoasymmetric sibling is junior. -/
theorem compareOccurrencePreRule4bKeys_pseudoasymmetric_under_chiral
    (rule3 : RawMolecule.CanonicalRule3Key) :
    compareOccurrencePreRule4bKeys
      { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.pseudoasymmetric)]] }
      { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] } =
        Ordering.lt := by
  have rule3refl : RawMolecule.compareCanonicalRule3Keys rule3 rule3 = Ordering.eq := by
    haveI : Std.TransCmp RawMolecule.compareCanonicalRule3Keys :=
      RawMolecule.compareCanonicalRule3Keys_transCmp
    exact Std.ReflCmp.compare_self (cmp := RawMolecule.compareCanonicalRule3Keys) (a := rule3)
  have h := compareOccurrencePreRule4bKeys_eq_rule4a_of_rule3_eq
    (left := { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.pseudoasymmetric)]] })
    (right := { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] })
    rule3refl
  rw [h]
  unfold RawMolecule.compareSparseCanonicalLayers
    RawMolecule.compareSparseCanonicalLayer
    RawMolecule.compareSparseCanonicalEntry
    RawMolecule.compareCanonicalPath
  rfl

/-- The cumulative sort places the chiral sibling first regardless of input order. -/
theorem sortOccurrencePreRule4bKeys_chiral_first (rule3 : RawMolecule.CanonicalRule3Key) :
    sortOccurrencePreRule4bKeys
      [ { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.pseudoasymmetric)]] }
      , { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] } ] =
      [ { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] }
      , { rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.pseudoasymmetric)]] } ] := by
  have inner :
      sortOccurrencePreRule4bKeys
        [{ rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] }] =
      [{ rule3 := rule3, rule4a := [[([], OfficialStereogenicUnitKind.chiral)]] }] := rfl
  unfold sortOccurrencePreRule4bKeys insertOccurrencePreRule4bKey
  rw [inner]
  dsimp only
  rw [compareOccurrencePreRule4bKeys_pseudoasymmetric_under_chiral rule3]
  rfl

/-! ## Runtime compilation and comparison -/

/-- Compile one occurrence cursor to a complete pre-Rule-4b key.

Refuses (`none`) on: no recoverable ligand, unsupported (non-downward-directed) source geometry,
unavailable Rule-3 evidence, fuel exhaustion, or an unavailable Rule-4a occurrence class. -/
def compileOccurrencePreRule4bKey? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : OccurrenceAuxState) (center : ℕ) (fuel : ℕ)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy)
    (cursor : CanonicalRerootCursor) :
    Option OccurrencePreRule4bKey := do
  let ligand ← cursorLigand? cursor
  buildOccurrencePreRule4bKey? mol (occurrenceBranchChildren mol center)
    (cursorRule3Observer result mol center policy ligand) (occurrenceRule4aKind? state) fuel cursor

/-- Every compiled pre-Rule-4b key carries a complete constitutional key. -/
theorem compileOccurrencePreRule4bKey?_complete
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {cursor : CanonicalRerootCursor} {key : OccurrencePreRule4bKey}
    (compiled : compileOccurrencePreRule4bKey? result mol state center fuel policy cursor =
      some key) :
    key.rule3.constitutional.complete = true := by
  unfold compileOccurrencePreRule4bKey? at compiled
  cases ligandComputed : cursorLigand? cursor with
  | none =>
      rw [ligandComputed] at compiled
      dsimp at compiled
      cases compiled
  | some ligand =>
      rw [ligandComputed] at compiled
      dsimp at compiled
      cases built : buildOccurrencePreRule4bKey? mol (occurrenceBranchChildren mol center)
          (cursorRule3Observer result mol center policy ligand) (occurrenceRule4aKind? state)
          fuel cursor with
      | none =>
          rw [built] at compiled
          cases compiled
      | some builtKey =>
          rw [built] at compiled
          cases compiled
          exact buildOccurrencePreRule4bKey?_complete (mol := mol)
            (children := occurrenceBranchChildren mol center)
            (observe3 := cursorRule3Observer result mol center policy ligand)
            (resolve4a := occurrenceRule4aKind? state) fuel cursor key built

/-- An unsupported source cursor refuses the whole compiled key.

This is the public-compilation counterpart of `cursorRule3Observer_eq_none_of_not_directed`: the
outer refusal is propagated, never replaced by a determinate absence. -/
theorem compileOccurrencePreRule4bKey?_eq_none_of_not_directed
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {cursor : CanonicalRerootCursor}
    (undirected : isDirectedSourceCursor cursor = false) :
    compileOccurrencePreRule4bKey? result mol state center fuel policy cursor = none := by
  unfold compileOccurrencePreRule4bKey?
  cases ligandComputed : cursorLigand? cursor with
  | none => rfl
  | some ligand =>
      exact buildOccurrencePreRule4bKey?_observe_none
        (mol := mol) (children := occurrenceBranchChildren mol center)
        (observe3 := cursorRule3Observer result mol center policy ligand)
        (resolve4a := occurrenceRule4aKind? state) (cursor := cursor)
        (cursorRule3Observer_eq_none_of_not_directed result mol center policy ligand cursor
          undirected)
        fuel

/-- Runtime pre-Rule-4b comparison under an explicit whole-centre Rule-3 policy.

Both operands are compiled at the same centre, fuel and policy.  `none` is a refusal (a cursor
that could not be compiled); it is never an equality and never a zero-priority fact. -/
def compareOccurrencePreRule4bWithPolicy? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : OccurrenceAuxState) (center fuel : ℕ)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  (compileOccurrencePreRule4bKey? result mol state center fuel policy left).bind fun leftKey =>
    (compileOccurrencePreRule4bKey? result mol state center fuel policy right).bind
      fun rightKey => some (compareOccurrencePreRule4bKeys leftKey rightKey)

/-- Runtime pre-Rule-4b comparison at a centre, recomputing the corrected source policy. -/
def compareOccurrencePreRule4b? (result : ChemistryNormalizationResult)
    (mol : RawMolecule) (state : OccurrenceAuxState) (center fuel : ℕ)
    (left right : CanonicalRerootCursor) : Option Ordering :=
  compareOccurrencePreRule4bWithPolicy? result mol state center fuel
    (ChemistryNormalizationResult.rule3CenterPolicy result mol center) left right

theorem compareOccurrencePreRule4b?_eq_withPolicy
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : OccurrenceAuxState) (center fuel : ℕ)
    (left right : CanonicalRerootCursor) :
    compareOccurrencePreRule4b? result mol state center fuel left right =
      compareOccurrencePreRule4bWithPolicy? result mol state center fuel
        (ChemistryNormalizationResult.rule3CenterPolicy result mol center) left right :=
  rfl

/-- Actual runtime/key correspondence: on successfully compiled operands the runtime comparator
is exactly the compiled-key comparator. -/
theorem compareOccurrencePreRule4bWithPolicy?_eq_keyComparison
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {left right : CanonicalRerootCursor}
    {leftKey rightKey : OccurrencePreRule4bKey}
    (leftCompiled : compileOccurrencePreRule4bKey? result mol state center fuel policy left =
      some leftKey)
    (rightCompiled : compileOccurrencePreRule4bKey? result mol state center fuel policy right =
      some rightKey) :
    compareOccurrencePreRule4bWithPolicy? result mol state center fuel policy left right =
      some (compareOccurrencePreRule4bKeys leftKey rightKey) := by
  unfold compareOccurrencePreRule4bWithPolicy?
  rw [leftCompiled, rightCompiled]
  rfl

/-- A refused cursor produces a refused comparison, not a tie. -/
theorem compareOccurrencePreRule4bWithPolicy?_eq_none_of_left
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {left right : CanonicalRerootCursor}
    (refused : compileOccurrencePreRule4bKey? result mol state center fuel policy left = none) :
    compareOccurrencePreRule4bWithPolicy? result mol state center fuel policy left right =
      none := by
  unfold compareOccurrencePreRule4bWithPolicy?
  rw [refused]
  rfl

theorem compareOccurrencePreRule4bWithPolicy?_eq_none_of_right
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {left right : CanonicalRerootCursor} {leftKey : OccurrencePreRule4bKey}
    (leftCompiled : compileOccurrencePreRule4bKey? result mol state center fuel policy left =
      some leftKey)
    (refused : compileOccurrencePreRule4bKey? result mol state center fuel policy right =
      none) :
    compareOccurrencePreRule4bWithPolicy? result mol state center fuel policy left right =
      none := by
  unfold compareOccurrencePreRule4bWithPolicy?
  rw [leftCompiled, refused]
  rfl

/-- An unsupported left operand refuses the comparison. -/
theorem compareOccurrencePreRule4bWithPolicy?_eq_none_of_left_not_directed
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {left right : CanonicalRerootCursor}
    (undirected : isDirectedSourceCursor left = false) :
    compareOccurrencePreRule4bWithPolicy? result mol state center fuel policy left right =
      none :=
  compareOccurrencePreRule4bWithPolicy?_eq_none_of_left
    (compileOccurrencePreRule4bKey?_eq_none_of_not_directed
      (result := result) (mol := mol) (state := state) (center := center) (fuel := fuel)
      (policy := policy) (cursor := left) undirected)

/-- An unsupported right operand refuses the comparison. -/
theorem compareOccurrencePreRule4bWithPolicy?_eq_none_of_right_not_directed
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {left right : CanonicalRerootCursor} {leftKey : OccurrencePreRule4bKey}
    (leftCompiled : compileOccurrencePreRule4bKey? result mol state center fuel policy left =
      some leftKey)
    (undirected : isDirectedSourceCursor right = false) :
    compareOccurrencePreRule4bWithPolicy? result mol state center fuel policy left right =
      none :=
  compareOccurrencePreRule4bWithPolicy?_eq_none_of_right leftCompiled
    (compileOccurrencePreRule4bKey?_eq_none_of_not_directed
      (result := result) (mol := mol) (state := state) (center := center) (fuel := fuel)
      (policy := policy) (cursor := right) undirected)

/-! ## Upward-source regression

The fixture below is the smallest *actual* upward cursor state assembled from the compiled
canonical tree of the three-atom molecule.  The single bond `1 - 0` makes the predecessor history
`[2, 1, 0]` an actual molecular path (`2 = 1` and `1 - 0`) instead of a bare list, and the double
bond `2 = 1` makes the Rule-3 source reader fire.

The data are derived from the production definitions rather than written by hand:
`RawMolecule.canonicalRoot 0 1` is the downward node with history `[1, 0]` emitted from centre `0`;
`CanonicalRerootCursor.children` generates the real child at atom `2` with history `[2, 1, 0]`;
`canonicalOriginalParent?` recovers the downward node from that child; and the upward cursor pairs
the recovered node with the generated child as `previous?`.

The upward cursor is also emitted by actual `children` when the generated child node is used as
an occurrence root with `previous? := none`, as in `occurrenceLigandCursors`.
The regression below proves this membership directly. The directed reader then reports the far
endpoint `1` as the entry; the guarded observer returns unavailable. Upward geometry is not
reconstructed by this module. -/

/-- Minimal molecule carrying the actual path `2 = 1 - 0`.

The double bond `2 = 1` is the Rule-3 source bond.  The single bond `1 - 0` makes the predecessor
history `[2, 1, 0]` a real molecular path to the original centre `0`, so the fixture no longer
relies on a history the molecule cannot support. -/
def upwardRegressionMolecule : RawMolecule :=
  { atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
              AtomSpec.aliphatic Element.C]
    bonds := [{ source := 2, target := 1, kind := ParsedBondKind.double },
              { source := 1, target := 0, kind := ParsedBondKind.single }] }

/-- The actual downward canonical node at atom `1` emitted from centre `0`: history `[1, 0]`. -/
def upwardRegressionDownwardNode : RawMolecule.CanonicalBranchNode :=
  RawMolecule.canonicalRoot 0 1

/-- The emitted downward node carries history `[1, 0]` and parent `0`. -/
theorem upwardRegressionDownwardNode_history :
    upwardRegressionDownwardNode.history = [1, 0] ∧
      upwardRegressionDownwardNode.parent = 0 := by
  decide

/-- The cursor seated at that centre-emitted downward node. -/
def upwardRegressionDownwardCursor : CanonicalRerootCursor :=
  { node := upwardRegressionDownwardNode }

/-- The child cursors actually generated by the zipper's `children` at the downward node. -/
def upwardRegressionGeneratedChildren : List CanonicalRerootCursor :=
  upwardRegressionDownwardCursor.children upwardRegressionMolecule

/-- The real child cursor generated by `children`: atom `2` reached from atom `1`, history
`[2, 1, 0]`, with the downward node as its stored predecessor. -/
def upwardRegressionChildCursor : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 1, history := [2, 1, 0],
              provenance := RawMolecule.CanonicalNodeProvenance.realAtom },
    previous? := some upwardRegressionDownwardNode }

/-- The child cursor is an actual element of the zipper-generated child list. -/
theorem upwardRegressionChildCursor_mem_generated :
    upwardRegressionChildCursor ∈ upwardRegressionGeneratedChildren := by
  decide

/-- The generated child records the downward cursor node as its predecessor. -/
theorem upwardRegressionChildCursor_previous :
    upwardRegressionChildCursor.previous? = some upwardRegressionDownwardCursor.node := rfl

/-- The generated child's node is exactly the real atom-`2` node. -/
theorem upwardRegressionChildCursor_node :
    upwardRegressionChildCursor.node =
      { atom := 2, parent := 1, history := [2, 1, 0],
        provenance := RawMolecule.CanonicalNodeProvenance.realAtom } := rfl

/-- `canonicalOriginalParent?` of the generated child recovers the centre-emitted downward node. -/
theorem upwardRegressionChildCursor_originalParent :
    canonicalOriginalParent? upwardRegressionChildCursor.node =
      some upwardRegressionDownwardNode := by
  decide

/-- The upward cursor state: the node recovered from the actual generated child, paired with that
child as its stored predecessor. -/
def upwardRegressionCursor : CanonicalRerootCursor :=
  { node :=
      (canonicalOriginalParent? upwardRegressionChildCursor.node).getD
        upwardRegressionDownwardNode,
    previous? := some upwardRegressionChildCursor.node }

/-- Starting an occurrence frame at the actual generated child emits the upward cursor through
its real original-parent edge. This is a statement about the production zipper output. -/
theorem upwardRegressionCursor_mem_actual_children :
    upwardRegressionCursor ∈
      ({ node := upwardRegressionChildCursor.node } : CanonicalRerootCursor).children
        upwardRegressionMolecule := by
  decide

/-- The recovered node is the downward node on which `children` was invoked. -/
theorem upwardRegressionCursor_node :
    upwardRegressionCursor.node = upwardRegressionDownwardNode := by
  decide

/-- The stored predecessor is the actual generated child node. -/
theorem upwardRegressionCursor_previous :
    upwardRegressionCursor.previous? = some upwardRegressionChildCursor.node := rfl

/-- The predecessor history `[2, 1, 0]` is an actual molecular path: the double source bond
`2 = 1` and the single bond `1 - 0` are both present. -/
theorem upwardRegression_predecessorHistory_is_path :
    upwardRegressionMolecule.bondOrder 2 1 = 2 ∧
      upwardRegressionMolecule.bondOrder 1 0 = 1 := by
  constructor <;> decide

/-- The fixture's bond order is the required double bond. -/
theorem upwardRegressionMolecule_bondOrder : upwardRegressionMolecule.bondOrder 2 1 = 2 := by
  decide

/-- General form of the upward misread: when the predecessor's history is
`previous.atom :: cursor.node.atom :: rest`, the reader's entry is the cursor node atom (the `far`
endpoint), not a substituent. -/
theorem cursorRule3SourceUnitOfNode?_upward_reads_far_as_entry
    {mol : RawMolecule} {center : ℕ} {cursor : CanonicalRerootCursor}
    {previous : RawMolecule.CanonicalBranchNode} {rest : List ℕ}
    (hPrev : cursor.previous? = some previous)
    (hProvenance : cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNodeAtom : cursor.node.atom ≠ center)
    (hPrevAtom : previous.atom ≠ center)
    (hBond : mol.bondOrder previous.atom cursor.node.atom = 2)
    (hHistory : previous.history = previous.atom :: cursor.node.atom :: rest) :
    cursorRule3SourceUnitOfNode? mol center cursor =
      some { near := previous.atom, far := cursor.node.atom,
             entry? := some cursor.node.atom } := by
  unfold cursorRule3SourceUnitOfNode?
  rw [hPrev]
  dsimp only
  have hProv : (cursor.node.provenance ==
      RawMolecule.CanonicalNodeProvenance.realAtom) = true := by
    simp [hProvenance]
  have hNode : (cursor.node.atom != center) = true := by
    simp [hNodeAtom]
  have hPrevNe : (previous.atom != center) = true := by
    simp [hPrevAtom]
  have hBondBool : (mol.bondOrder previous.atom cursor.node.atom == 2) = true := by
    simp [hBond]
  rw [hProv, hNode, hPrevNe, hBondBool]
  simp [hHistory]

/-- The constructed upward cursor is not downward-directed: the predecessor's atom `2` and history
`[2, 1, 0]` do not match the cursor node's parent `0` and parent-suffix `[0]`. -/
theorem upwardRegressionCursor_not_directed :
    isDirectedSourceCursor upwardRegressionCursor = false := by
  decide

/-- Actual upward regression on the reader: the entry is the `far` endpoint `1`, not a
substituent. -/
theorem upwardRegression_sourceUnit_reads_far_as_entry :
    cursorRule3SourceUnitOfNode? upwardRegressionMolecule 0 upwardRegressionCursor =
      some { near := 2, far := 1, entry? := some 1 } := by
  apply cursorRule3SourceUnitOfNode?_upward_reads_far_as_entry
    (previous := upwardRegressionChildCursor.node) (rest := [0])
  · exact upwardRegressionCursor_previous
  · decide
  · decide
  · decide
  · exact upwardRegressionMolecule_bondOrder
  · rfl

/-- The guarded observer refuses the upward cursor instead of returning a determinate absence. -/
theorem upwardRegression_observer_refuses
    (result : ChemistryNormalizationResult)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy) (ligand : ℕ) :
    cursorRule3Observer result upwardRegressionMolecule 0 policy ligand
      upwardRegressionCursor = none :=
  cursorRule3Observer_eq_none_of_not_directed result upwardRegressionMolecule 0 policy ligand
    upwardRegressionCursor upwardRegressionCursor_not_directed

/-- The public compiler refuses the upward cursor. -/
theorem upwardRegression_compile_refuses
    (result : ChemistryNormalizationResult) (state : OccurrenceAuxState)
    (fuel : ℕ) (policy : ChemistryNormalizationResult.Rule3CenterPolicy) :
    compileOccurrencePreRule4bKey? result upwardRegressionMolecule state 0 fuel policy
      upwardRegressionCursor = none :=
  compileOccurrencePreRule4bKey?_eq_none_of_not_directed
    upwardRegressionCursor_not_directed

/-! ## Frontier adapter and finite-pool certification -/

/-- Actual frontier adapter over occurrence cursors.

`resolve` is the reviewed honest tri-state classifier (outer `none` = unavailable, `some none` =
known not to contribute an uppercase chiral descriptor, `some (some d)` = uppercase descriptor
`d`).  The runtime comparator uses `Ordering.gt` for the senior side; the generic frontier helper
uses `Ordering.lt`.  The adapter therefore applies `Ordering.swap`. -/
def occurrenceFrontierSpec (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : OccurrenceAuxState) (center fuel : ℕ)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy) :
    FrontierSpec CanonicalRerootCursor RS where
  children := occurrenceBranchChildren mol center
  resolve := occurrenceChiralityClassification? state
  before := fun left right =>
    (compareOccurrencePreRule4bWithPolicy? result mol state center fuel policy left right).map
      Ordering.swap

/-- Frontier-adapter correspondence on compiled operands. -/
theorem occurrenceFrontierSpec_before_eq
    {result : ChemistryNormalizationResult} {mol : RawMolecule} {state : OccurrenceAuxState}
    {center fuel : ℕ} {policy : ChemistryNormalizationResult.Rule3CenterPolicy}
    {left right : CanonicalRerootCursor}
    {leftKey rightKey : OccurrencePreRule4bKey}
    (leftCompiled : compileOccurrencePreRule4bKey? result mol state center fuel policy left =
      some leftKey)
    (rightCompiled : compileOccurrencePreRule4bKey? result mol state center fuel policy right =
      some rightKey) :
    (occurrenceFrontierSpec result mol state center fuel policy).before left right =
      some (Ordering.swap (compareOccurrencePreRule4bKeys leftKey rightKey)) := by
  show (compareOccurrencePreRule4bWithPolicy? result mol state center fuel policy
      left right).map Ordering.swap =
    some (Ordering.swap (compareOccurrencePreRule4bKeys leftKey rightKey))
  rw [compareOccurrencePreRule4bWithPolicy?_eq_keyComparison leftCompiled rightCompiled]
  rfl

/-- The frontier adapter agrees with the canonical key comparator on every pair of successful
compilations, up to the explicit seniority swap. -/
theorem occurrenceFrontierSpec_comparesByCompiledKey
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : OccurrenceAuxState) (center fuel : ℕ)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy) :
    ComparesByCompiledKey
      (occurrenceFrontierSpec result mol state center fuel policy).before
      (compileOccurrencePreRule4bKey? result mol state center fuel policy)
      compareOccurrencePreRule4bKeys := by
  intro left right leftKey rightKey leftCompiled rightCompiled
  dsimp [occurrenceFrontierSpec]
  rw [compareOccurrencePreRule4bWithPolicy?_eq_keyComparison leftCompiled rightCompiled]
  rw [runtimeSeniorSwap_eq_swap]
  rfl

/-- A finite pool of cursors with per-node compilation receipts. -/
def occurrenceCompiledKeyPool
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : OccurrenceAuxState) (center fuel : ℕ)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy)
    (cursors : List CanonicalRerootCursor)
    (keyOf : CanonicalRerootCursor → OccurrencePreRule4bKey)
    (receipt : ∀ c, c ∈ cursors →
      compileOccurrencePreRule4bKey? result mol state center fuel policy c = some (keyOf c)) :
    CompiledKeyPool CanonicalRerootCursor OccurrencePreRule4bKey where
  cursors := cursors
  compile := compileOccurrencePreRule4bKey? result mol state center fuel policy
  keyOf := keyOf
  compareKey := compareOccurrencePreRule4bKeys
  compareKey_transCmp := compareOccurrencePreRule4bKeys_transCmp
  receipt := receipt

/-- The complete finite-pool adapter: from the compiled-key pool and the checked comparator
bridge, the reviewed `FinitePoolAdapter` supplies all frontier order laws, pool completeness,
successful ranking, and class-identifier facts without any global cursor totality assumption. -/
def occurrenceFinitePoolAdapter
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : OccurrenceAuxState) (center fuel : ℕ)
    (policy : ChemistryNormalizationResult.Rule3CenterPolicy)
    (cursors : List CanonicalRerootCursor)
    (keyOf : CanonicalRerootCursor → OccurrencePreRule4bKey)
    (receipt : ∀ c, c ∈ cursors →
      compileOccurrencePreRule4bKey? result mol state center fuel policy c = some (keyOf c)) :
    FinitePoolAdapter CanonicalRerootCursor RS OccurrencePreRule4bKey where
  spec := occurrenceFrontierSpec result mol state center fuel policy
  pool := occurrenceCompiledKeyPool result mol state center fuel policy cursors keyOf receipt
  bridge := occurrenceFrontierSpec_comparesByCompiledKey result mol state center fuel policy

/-! ## Kernel trust checks -/

assert_kernel_only isDirectedSourceCursor_eq_true_iff
assert_kernel_only cursorRule3SourceUnitOfNode?_eq_rule3SourceUnitOfNode?_of_directed
assert_kernel_only cursorRule3Observer_eq_rule3BranchObserver_of_directed
assert_kernel_only cursorRule3Observer_eq_none_of_not_directed
assert_kernel_only buildCursorRule3Key?_observe_none
assert_kernel_only compileCursorRule3Children_member
assert_kernel_only buildCursorRule3Key?_complete
assert_kernel_only buildCursorRule3Key?_rule3Aligned
assert_kernel_only occurrenceRule4aKind?_eq_none_of_missing
assert_kernel_only occurrenceRule4aKind?_eq_some_nonstereogenic_of_nonReal
assert_kernel_only compareRule4aKind_eq_priority
assert_kernel_only compareRule4aKind_eq_official
assert_kernel_only compareRule4aKind_transCmp
assert_kernel_only compareOccurrencePreRule4bKeys_eq_rule3_of_ne
assert_kernel_only compareOccurrencePreRule4bKeys_eq_rule4a_of_rule3_eq
assert_kernel_only compareOccurrencePreRule4bKeys_transCmp
assert_kernel_only compareOccurrencePreRule4bKeys_refl
assert_kernel_only insertOccurrencePreRule4bKey_perm
assert_kernel_only sortOccurrencePreRule4bKeys_perm
assert_kernel_only insertOccurrencePreRule4bKey_descending
assert_kernel_only sortOccurrencePreRule4bKeys_descending
assert_kernel_only compareRule4aSparseLayers_chiral_over_pseudoasymmetric
assert_kernel_only compareOccurrencePreRule4bKeys_chiral_over_pseudoasymmetric
assert_kernel_only compareOccurrencePreRule4bKeys_pseudoasymmetric_under_chiral
assert_kernel_only sortOccurrencePreRule4bKeys_chiral_first
assert_kernel_only buildOccurrencePreRule4bKey?_observe_none
assert_kernel_only buildOccurrencePreRule4bKey?_resolve_none
assert_kernel_only buildOccurrencePreRule4bKey?_complete
assert_kernel_only compileOccurrencePreRule4bKey?_complete
assert_kernel_only compileOccurrencePreRule4bKey?_eq_none_of_not_directed
assert_kernel_only compareOccurrencePreRule4b?_eq_withPolicy
assert_kernel_only compareOccurrencePreRule4bWithPolicy?_eq_keyComparison
assert_kernel_only compareOccurrencePreRule4bWithPolicy?_eq_none_of_left
assert_kernel_only compareOccurrencePreRule4bWithPolicy?_eq_none_of_right
assert_kernel_only compareOccurrencePreRule4bWithPolicy?_eq_none_of_left_not_directed
assert_kernel_only compareOccurrencePreRule4bWithPolicy?_eq_none_of_right_not_directed
assert_kernel_only cursorRule3SourceUnitOfNode?_upward_reads_far_as_entry
assert_kernel_only upwardRegressionDownwardNode_history
assert_kernel_only upwardRegressionChildCursor_mem_generated
assert_kernel_only upwardRegressionChildCursor_previous
assert_kernel_only upwardRegressionChildCursor_node
assert_kernel_only upwardRegressionChildCursor_originalParent
assert_kernel_only upwardRegressionCursor_node
assert_kernel_only upwardRegressionCursor_previous
assert_kernel_only upwardRegression_predecessorHistory_is_path
assert_kernel_only upwardRegressionCursor_not_directed
assert_kernel_only upwardRegressionMolecule_bondOrder
assert_kernel_only upwardRegression_sourceUnit_reads_far_as_entry
assert_kernel_only upwardRegression_observer_refuses
assert_kernel_only upwardRegression_compile_refuses
assert_kernel_only occurrenceFrontierSpec_before_eq
assert_kernel_only occurrenceFrontierSpec_comparesByCompiledKey

end TetraStereo.OneCenter.OccurrencePreRule4b

assert_kernel_only TetraStereo.OneCenter.OccurrencePreRule4b.upwardRegressionCursor_mem_actual_children
