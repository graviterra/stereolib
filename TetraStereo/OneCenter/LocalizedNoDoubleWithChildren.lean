import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WithChildren

/-!
# Parameterized executable no-localized-double descriptor pipeline

`LocalizedNoDoubleDescriptorExecutable` compiles the descriptor-bearing Rule-3--Rule-5 pipeline over
the total executable child reader `executableLocalizedRerootChildren?`.  Every reroot descent in that
pipeline reads the child expansion of the *current* cursor from the input itself, so a caller who
evaluates the pipeline many times (once per round, or once per candidate) re-reads the same
expansions over and over.

This module copies the whole executable pipeline into the namespace
`TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WithChildren` with one extra leading argument

```
readChildren : input.LocalizedRerootCursor carrierFuel →
  Option (List (input.LocalizedRerootCursor carrierFuel))
```

inserted directly after `(input) {carrierFuel}`.  Inside each copy, every read of
`input.executableLocalizedRerootChildren?` is replaced by `readChildren` and every recursive or
cross call is redirected to the copied function of the same basename.  Nothing else changes: the
same rules, the same merge and sort order, the same fuel arithmetic (`localizedDescriptorBearing-
Rule3EvaluationFuel`, `localizedOccurrenceRerootEvaluationFuel`), and the same `none` refusals.  The
copies therefore let a caller bind a *cached* children table once, outside the rounds, and run the
descriptor compiler repeatedly against it.

The tracked ligand order `localizedNoDoubleTrackedOrderExec?` reads no children at all (it consults
the comparator on the cumulative key frame), so it is not copied and the copies call the original.

Each copy is proved extensionally equal to the original executable function it replaces with
`readChildren` instantiated at `input.executableLocalizedRerootChildren?`, under the single
hypothesis that `readChildren` agrees pointwise with that reader.  The two fuel-recursive key
compilers are proved by fuel induction; the six compound Rules-4b--4c--5 wrappers and the four
top-level wrappers follow by rewriting with those equalities.  Agreement with the *proof-facing*
descriptor-bearing pipeline is then obtained by composing the final theorem below with the existing
`localizedNoDoubleDescriptorExec?_eq_localizedOccurrenceDescriptorBearingRule3Through5Descriptor?`.

All equalities are equalities of `Option`, so rejection behaviour (`none`) is included on both sides.
The read hypothesis is a `Prop`, hence proof-erased: it is an argument of the theorems only and never
appears as runtime data or as a parameter of any copied definition.
-/

/-! ## Copied executable definitions -/

/-- Copied executable Rule-3 key twin, parameterized by the child reader.  Identical to
`buildLocalizedNoDoubleRule3KeyExec?` except that every cursor expansion is read through
`readChildren` and the recursive descent calls this copy. -/
def buildLocalizedNoDoubleRule3KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List input.LocalizedRule3PhysicalUnitId →
      input.LocalizedRerootCursor carrierFuel →
        Option input.LocalizedRerootRecursiveRule3SpatialKey
  | 0, _excluded, cursor => do
      let children ← readChildren cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations none
            rule3 := input.localizedRule3SpatialRootPriorities none }
      else none
  | fuel + 1, excluded, cursor => do
      let children ← readChildren cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := input.localizedRule3SpatialRootObservations none
            rule3 := input.localizedRule3SpatialRootPriorities none }
      else
        let childKeys ← children.mapM
          (buildLocalizedNoDoubleRule3KeyExec? input readChildren target view fuel excluded)
        let sorted := input.sortLocalizedRerootRecursiveRule3SpatialKeys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := input.localizedRule3SpatialRootObservations none ++
              input.mergeLocalizedRerootRule3ObservationChildren sorted
            rule3 := input.localizedRule3SpatialRootPriorities none ++
              input.mergeLocalizedRerootRule3PriorityChildren sorted }

/-- Copied executable single-pass Rule-3 frame twin, parameterized by the child reader. -/
def buildLocalizedNoDoubleRule3FrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame
  | 0, _cursors => none
  | fuel + 1, cursors => do
      let rawKeys ← cursors.mapM
        (buildLocalizedNoDoubleRule3KeyExec? input readChildren target view fuel [])
      some { rawKeys, coupled := false, excluded := [], keys := rawKeys }

/-- Copied executable cumulative Rules-4a--5 key twin, parameterized by the child reader. -/
def buildLocalizedRerootCumulativeRule45KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← readChildren cursor
      if children = [] then
        let label := input.localizedDependencyLabel target view cursor
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, cursor => do
      let children ← readChildren cursor
      let label := input.localizedDependencyLabel target view cursor
      if children = [] then
        some
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        let childKeys ← children.mapM
          (buildLocalizedRerootCumulativeRule45KeyExec? input readChildren stage target view fuel)
        let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
        some
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }

/-- Copied executable twin of `buildLocalizedRerootRule4bcReading?`, parameterized by the child
reader. -/
def buildLocalizedRerootRule4bcReadingExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option RS → Option input.LocalizedRerootRule4bcReading
  | none => do
      let rule4bKey ← buildLocalizedRerootCumulativeRule45KeyExec?
        input readChildren .rule4a target view fuel cursor
      let rule4cKey ← buildLocalizedRerootCumulativeRule45KeyExec?
        input readChildren .rule4cNoReference target view fuel cursor
      some
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }
  | some reference => do
      let rule4bKey ← buildLocalizedRerootCumulativeRule45KeyExec?
        input readChildren (.rule4b reference) target view fuel cursor
      let rule4cKey ← buildLocalizedRerootCumulativeRule45KeyExec?
        input readChildren (.rule4c reference) target view fuel cursor
      some
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }

/-- Copied executable twin of `buildLocalizedRerootRule4bcReadings?`, parameterized by the child
reader. -/
def buildLocalizedRerootRule4bcReadingsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → Option (List input.LocalizedRerootRule4bcReading)
  | [] => some []
  | reference :: references => do
      let reading ← buildLocalizedRerootRule4bcReadingExec?
        input readChildren target view fuel cursor reference
      let readings ← buildLocalizedRerootRule4bcReadingsExec?
        input readChildren target view fuel cursor references
      some (reading :: readings)

/-- Copied executable twin of `buildLocalizedRerootCompoundRule4bcKey?`, parameterized by the child
reader. -/
def buildLocalizedRerootCompoundRule4bcKeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule4bcKey := do
  let rule4aKey ← buildLocalizedRerootCumulativeRule45KeyExec?
    input readChildren .rule4a target view fuel cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  let readings ← buildLocalizedRerootRule4bcReadingsExec?
    input readChildren target view fuel cursor alternatives
  some
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings }

/-- Copied executable twin of `buildLocalizedRerootRule5Reading?`, parameterized by the child
reader. -/
def buildLocalizedRerootRule5ReadingExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    Option input.LocalizedRerootRule5Reading := do
  let commonR ← buildLocalizedRerootCumulativeRule45KeyExec?
    input readChildren (localizedRule5StageFor prior.reference? .R) target view fuel cursor
  let commonS ← buildLocalizedRerootCumulativeRule45KeyExec?
    input readChildren (localizedRule5StageFor prior.reference? .S) target view fuel cursor
  some { prior := prior, commonR := commonR, commonS := commonS }

/-- Copied executable twin of `buildLocalizedRerootRule5Readings?`, parameterized by the child
reader. -/
def buildLocalizedRerootRule5ReadingsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List input.LocalizedRerootRule4bcReading →
      Option (List input.LocalizedRerootRule5Reading)
  | [] => some []
  | prior :: priors => do
      let reading ← buildLocalizedRerootRule5ReadingExec?
        input readChildren target view fuel cursor prior
      let readings ← buildLocalizedRerootRule5ReadingsExec?
        input readChildren target view fuel cursor priors
      some (reading :: readings)

/-- Copied executable twin of `buildLocalizedRerootCompoundRule45Key?`, parameterized by the child
reader. -/
def buildLocalizedRerootCompoundRule45KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key := do
  let prior ← buildLocalizedRerootCompoundRule4bcKeyExec?
    input readChildren target view fuel cursor
  let readings ← buildLocalizedRerootRule5ReadingsExec?
    input readChildren target view fuel cursor prior.readings
  some { prior := prior, rule5Readings := readings }

/-- Copied executable four-ligand frame twin, parameterized by the child reader. -/
def localizedNoDoubleFourLigandFrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedOccurrenceFourLigandFrame carrierFuel) := do
  let cursors ← readChildren { occurrence := target, previous? := none }
  if length_eq : cursors.length = 4 then
    some { cursors := cursors, length_eq := length_eq }
  else none

/-- Copied executable key-frame twin, parameterized by the child reader.  Both the Rule-3 frame and
the compound Rules-4b/4c/5 keys are compiled through the copies, so one reader serves the whole
frame. -/
def localizedNoDoubleKeyFrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let rule3Frame ← buildLocalizedNoDoubleRule3FrameExec?
    input readChildren target view descriptorFuel base.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none

/-- Copied executable spatial-evidence twin, parameterized by the child reader.  The tracked order
reads no children and is used from the original module unchanged. -/
def localizedNoDoubleSpatialEvidenceExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← localizedNoDoubleFourLigandFrameExec? input readChildren target
  let keys ← localizedNoDoubleKeyFrameExec?
    input readChildren target view base
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

/-- Copied executable full descriptor twin, parameterized by the child reader.  The rational
determinant and the pseudo-asymmetric classification are the originals; only the evidence compiler
is the copy. -/
def localizedNoDoubleDescriptorExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← localizedNoDoubleSpatialEvidenceExec?
    input readChildren target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-! ## Exact equality to the executable pipeline at the input's own reader

Every copy below is proved equal to the executable function of the same basename from
`TetraStereo.OneCenter.CertifiedLocalizedCIPInput` when `readChildren` is the input's own reader.
The hypothesis `readEq` is a proposition about the reader, so it carries no runtime data; it is an
argument of these theorems only.  The equalities are equalities of `Option`, so `none` on one side
forces `none` on the other. -/

/-- The reader-parameterized Rule-3 key twin computes exactly the executable Rule-3 key at every
fuel, exclusion list, and cursor. -/
theorem buildLocalizedNoDoubleRule3KeyExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor,
      buildLocalizedNoDoubleRule3KeyExec? input readChildren target view fuel excluded cursor =
        CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3KeyExec? input target view fuel excluded cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor
      simp [buildLocalizedNoDoubleRule3KeyExec?,
        CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3KeyExec?, readEq cursor]
  | succ fuel ih =>
      intro excluded cursor
      have childEq :
          buildLocalizedNoDoubleRule3KeyExec? input readChildren target view fuel excluded =
            CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3KeyExec? input target view fuel excluded := by
        funext child
        exact ih excluded child
      simp [buildLocalizedNoDoubleRule3KeyExec?,
        CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3KeyExec?, readEq cursor, childEq]

/-- The reader-parameterized Rule-3 frame twin computes exactly the executable Rule-3 frame at every
fuel and cursor list. -/
theorem buildLocalizedNoDoubleRule3FrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursors,
      buildLocalizedNoDoubleRule3FrameExec? input readChildren target view fuel cursors =
        CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3FrameExec? input target view fuel cursors := by
  intro fuel
  cases fuel with
  | zero =>
      intro cursors
      simp [buildLocalizedNoDoubleRule3FrameExec?,
        CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3FrameExec?]
  | succ fuel =>
      intro cursors
      have keyEq : buildLocalizedNoDoubleRule3KeyExec? input readChildren target view fuel [] =
          CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3KeyExec? input target view fuel [] := by
        funext cursor
        exact buildLocalizedNoDoubleRule3KeyExec?_eq_original
          input readChildren readEq target view fuel [] cursor
      have rawEq : cursors.mapM
            (buildLocalizedNoDoubleRule3KeyExec? input readChildren target view fuel []) =
          cursors.mapM
            (CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3KeyExec? input target view fuel []) := by
        rw [keyEq]
      simp [buildLocalizedNoDoubleRule3FrameExec?,
        CertifiedLocalizedCIPInput.buildLocalizedNoDoubleRule3FrameExec?, rawEq]

/-- The reader-parameterized cumulative Rules-4a--5 key twin computes exactly the executable
cumulative key at every stage, fuel, and cursor. -/
theorem buildLocalizedRerootCumulativeRule45KeyExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      buildLocalizedRerootCumulativeRule45KeyExec? input readChildren stage target view fuel cursor =
        CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyExec? input stage target view fuel cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor
      simp [buildLocalizedRerootCumulativeRule45KeyExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyExec?, readEq cursor]
  | succ fuel ih =>
      intro cursor
      have childEq :
          buildLocalizedRerootCumulativeRule45KeyExec? input readChildren stage target view fuel =
            CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyExec? input stage target view fuel := by
        funext child
        exact ih child
      simp [buildLocalizedRerootCumulativeRule45KeyExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyExec?, readEq cursor, childEq]

/-- The reader-parameterized Rule-4b/4c alternative twin computes exactly the executable alternative
at every reference choice. -/
theorem buildLocalizedRerootRule4bcReadingExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) :
    buildLocalizedRerootRule4bcReadingExec? input readChildren target view fuel cursor reference =
      CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingExec? input target view fuel cursor reference := by
  cases reference with
  | none =>
      simp only [buildLocalizedRerootRule4bcReadingExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingExec?,
        buildLocalizedRerootCumulativeRule45KeyExec?_eq_original input readChildren readEq]
  | some reference =>
      simp only [buildLocalizedRerootRule4bcReadingExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingExec?,
        buildLocalizedRerootCumulativeRule45KeyExec?_eq_original input readChildren readEq]

/-- The reader-parameterized Rule-4b/4c alternative-list twin computes exactly the executable
alternative list at every reference list. -/
theorem buildLocalizedRerootRule4bcReadingsExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ references,
      buildLocalizedRerootRule4bcReadingsExec? input readChildren target view fuel cursor references =
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsExec? input
          target view fuel cursor references
  | [] => by
      simp only [buildLocalizedRerootRule4bcReadingsExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsExec?]
  | reference :: references => by
      simp only [buildLocalizedRerootRule4bcReadingsExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsExec?,
        buildLocalizedRerootRule4bcReadingExec?_eq_original
          input readChildren readEq target view fuel cursor reference,
        buildLocalizedRerootRule4bcReadingsExec?_eq_original
          input readChildren readEq target view fuel cursor references]

/-- The reader-parameterized compound Rules-4b/4c twin computes exactly the executable compound key
at every fuel and cursor, including the same reference-count priority and the same `none`. -/
theorem buildLocalizedRerootCompoundRule4bcKeyExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    buildLocalizedRerootCompoundRule4bcKeyExec? input readChildren target view fuel cursor =
      CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyExec? input target view fuel cursor := by
  simp only [buildLocalizedRerootCompoundRule4bcKeyExec?,
    CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyExec?,
    buildLocalizedRerootCumulativeRule45KeyExec?_eq_original input readChildren readEq,
    buildLocalizedRerootRule4bcReadingsExec?_eq_original input readChildren readEq]

/-- The reader-parameterized Rule-5 reading twin computes exactly the executable common-`R` /
common-`S` reading pair. -/
theorem buildLocalizedRerootRule5ReadingExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    buildLocalizedRerootRule5ReadingExec? input readChildren target view fuel cursor prior =
      CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingExec? input target view fuel cursor prior := by
  simp only [buildLocalizedRerootRule5ReadingExec?,
    CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingExec?,
    buildLocalizedRerootCumulativeRule45KeyExec?_eq_original input readChildren readEq]

/-- The reader-parameterized Rule-5 reading-list twin computes exactly the executable Rule-5 reading
list at every prior-reading list. -/
theorem buildLocalizedRerootRule5ReadingsExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ priors,
      buildLocalizedRerootRule5ReadingsExec? input readChildren target view fuel cursor priors =
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsExec? input target view fuel cursor priors
  | [] => by
      simp only [buildLocalizedRerootRule5ReadingsExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsExec?]
  | prior :: priors => by
      simp only [buildLocalizedRerootRule5ReadingsExec?,
        CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsExec?,
        buildLocalizedRerootRule5ReadingExec?_eq_original
          input readChildren readEq target view fuel cursor prior,
        buildLocalizedRerootRule5ReadingsExec?_eq_original
          input readChildren readEq target view fuel cursor priors]

/-- The reader-parameterized through-Rule-5 compound twin computes exactly the executable compound
Rules-4b--5 key at every fuel and cursor. -/
theorem buildLocalizedRerootCompoundRule45KeyExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view fuel cursor =
      CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyExec? input target view fuel cursor := by
  simp only [buildLocalizedRerootCompoundRule45KeyExec?,
    CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyExec?,
    buildLocalizedRerootCompoundRule4bcKeyExec?_eq_original input readChildren readEq,
    buildLocalizedRerootRule5ReadingsExec?_eq_original input readChildren readEq]

/-- The reader-parameterized four-ligand frame twin computes exactly the executable four-ligand
frame, including the rejection when the expansion does not have exactly four cursors. -/
theorem localizedNoDoubleFourLigandFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel) :
    localizedNoDoubleFourLigandFrameExec? input readChildren target =
      CertifiedLocalizedCIPInput.localizedNoDoubleFourLigandFrameExec? input target := by
  simp only [localizedNoDoubleFourLigandFrameExec?,
    CertifiedLocalizedCIPInput.localizedNoDoubleFourLigandFrameExec?,
    readEq { occurrence := target, previous? := none }]

/-- The reader-parameterized key-frame twin computes exactly the executable key frame at every
target, view, and base frame. -/
theorem localizedNoDoubleKeyFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    localizedNoDoubleKeyFrameExec? input readChildren target view base =
      CertifiedLocalizedCIPInput.localizedNoDoubleKeyFrameExec? input target view base := by
  have rule45Eq :
      (buildLocalizedRerootCompoundRule45KeyExec? input readChildren target view
          (localizedOccurrenceRerootEvaluationFuel carrierFuel)) =
        (CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyExec? input
          target view (localizedOccurrenceRerootEvaluationFuel carrierFuel)) := by
    funext cursor
    exact buildLocalizedRerootCompoundRule45KeyExec?_eq_original
      input readChildren readEq target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor
  simp only [localizedNoDoubleKeyFrameExec?,
    CertifiedLocalizedCIPInput.localizedNoDoubleKeyFrameExec?,
    buildLocalizedNoDoubleRule3FrameExec?_eq_original input readChildren readEq target view,
    rule45Eq]

/-- The reader-parameterized spatial-evidence twin computes exactly the executable spatial evidence
at every target and view. -/
theorem localizedNoDoubleSpatialEvidenceExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedNoDoubleSpatialEvidenceExec? input readChildren target view =
      CertifiedLocalizedCIPInput.localizedNoDoubleSpatialEvidenceExec? input target view := by
  simp only [localizedNoDoubleSpatialEvidenceExec?,
    CertifiedLocalizedCIPInput.localizedNoDoubleSpatialEvidenceExec?,
    localizedNoDoubleFourLigandFrameExec?_eq_original input readChildren readEq target,
    localizedNoDoubleKeyFrameExec?_eq_original input readChildren readEq target view]

/-- **Final theorem.**  The reader-parameterized executable no-localized-double descriptor computes
exactly the executable descriptor of `LocalizedNoDoubleDescriptorExecutable` at every target and
dependency view, as soon as the supplied reader agrees pointwise with
`input.executableLocalizedRerootChildren?`.

Composing this with
`localizedNoDoubleDescriptorExec?_eq_localizedOccurrenceDescriptorBearingRule3Through5Descriptor?`
gives the same agreement with the proof-facing descriptor-bearing occurrence descriptor, so a caller
may bind a cached children table once, outside the rounds, and still obtain the certified
descriptor. -/
theorem localizedNoDoubleDescriptorExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor : input.LocalizedRerootCursor carrierFuel,
      readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    localizedNoDoubleDescriptorExec? input readChildren target view =
      CertifiedLocalizedCIPInput.localizedNoDoubleDescriptorExec? input target view := by
  simp only [localizedNoDoubleDescriptorExec?,
    CertifiedLocalizedCIPInput.localizedNoDoubleDescriptorExec?,
    localizedNoDoubleSpatialEvidenceExec?_eq_original input readChildren readEq target view]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WithChildren
