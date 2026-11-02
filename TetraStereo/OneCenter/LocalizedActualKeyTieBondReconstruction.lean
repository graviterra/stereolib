import TetraStereo.OneCenter.LocalizedActualShapeBondOrderTransport
import TetraStereo.OneCenter.FullStateParentNoninterference
import TetraStereo.KernelOnly

set_option autoImplicit false





































































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open LocalizedMultipleBondOrderReconstruction

/-! ## 1.  An actual production comparator tie determines the constitutional observable -/

/-- **Actual comparator tie at two cursors.**  If the shipped production comparator
`compareLocalizedConstitutionalCursors?` returns `eq` on two cursors, then any two successful
actual cumulative `WithRead` builds at those cursors (possibly at different stages, with different
label readers and different budgets) have the same Rule-1a / Rule-1b / Rule-2 observable
projection.

The comparator fixes only its own `Exec` builds at the linear budget.  Those builds are
constitutionally sound (`buildLocalizedRerootRuleMajorKeyExec?_sound`), and every successful
`WithRead` build has a constitutional projection satisfying the independent declarative
derivation (`buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative`).
`declarative_constitutional_observable_unique` then identifies each build's observable with the
comparator's own at the same cursor, and the comparator tie identifies the two comparator builds.
No successful builder, no shape equality and no table correspondence is assumed. -/
theorem constitutionalObservable_eq_of_compareCursors_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuelLeft fuelRight : Nat)
    (cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel)
    (keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key)
    (builtLeft : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stageLeft readLeft fuelLeft cursorLeft = some keyLeft)
    (builtRight : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stageRight readRight fuelRight cursorRight = some keyRight)
    (compared : input.compareLocalizedConstitutionalCursors? cursorLeft cursorRight =
      some Ordering.eq) :
    constitutionalObservable keyLeft.constitutional =
      constitutionalObservable keyRight.constitutional := by
  obtain ⟨plainLeft, plainRight, plainLeftBuilt, plainRightBuilt, comparedKeys⟩ :=
    input.compareLocalizedConstitutionalCursors?_computations cursorLeft cursorRight
      Ordering.eq compared
  have comparedObservable : constitutionalObservable plainLeft =
      constitutionalObservable plainRight := by
    have refined := comparedKeys
    rw [ruleMajor_compare_eq_observable] at refined
    exact (compareConstitutionalObservable_eq_iff _ _).mp refined
  have leftObservable : constitutionalObservable keyLeft.constitutional =
      constitutionalObservable plainLeft :=
    input.declarative_constitutional_observable_unique fuelLeft
      (2 * (carrierFuel + 1) + 1) cursorLeft keyLeft.constitutional plainLeft
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        stageLeft readLeft fuelLeft cursorLeft keyLeft builtLeft)
      (input.buildLocalizedRerootRuleMajorKeyExec?_sound
        (2 * (carrierFuel + 1) + 1) cursorLeft plainLeft plainLeftBuilt)
  have rightObservable : constitutionalObservable keyRight.constitutional =
      constitutionalObservable plainRight :=
    input.declarative_constitutional_observable_unique fuelRight
      (2 * (carrierFuel + 1) + 1) cursorRight keyRight.constitutional plainRight
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
        stageRight readRight fuelRight cursorRight keyRight builtRight)
      (input.buildLocalizedRerootRuleMajorKeyExec?_sound
        (2 * (carrierFuel + 1) + 1) cursorRight plainRight plainRightBuilt)
  exact leftObservable.trans (comparedObservable.trans rightObservable.symm)

/-- **Cumulative full-comparator tie.**  If the cumulative full comparator returns `eq` on two
actual keys, then their constitutional observables agree.  The comparison-visible projection of a
cumulative key is the existing `localizedRerootCumulativeRule45Observable`, which compares Rule 1a,
Rule 1b, Rule 2 and the cumulative descriptor; equality of projections is the existing
`compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq`. -/
theorem constitutionalObservable_eq_of_fullCompare_eq
    (input : CertifiedLocalizedCIPInput)
    (keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key)
    (compared : input.compareLocalizedRerootCumulativeRule45Keys keyLeft keyRight =
      Ordering.eq) :
    constitutionalObservable keyLeft.constitutional =
      constitutionalObservable keyRight.constitutional := by
  have observable :=
    (input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq keyLeft
      keyRight).mp compared
  have rule1aEq : keyLeft.constitutional.rule1a = keyRight.constitutional.rule1a := by
    simpa only [localizedRerootCumulativeRule45Observable] using
      congrArg LocalizedCumulativeRule45Observable.rule1a observable
  have rule1bEq : keyLeft.constitutional.rule1b = keyRight.constitutional.rule1b := by
    simpa only [localizedRerootCumulativeRule45Observable] using
      congrArg LocalizedCumulativeRule45Observable.rule1b observable
  have rule2Eq : keyLeft.constitutional.rule2 = keyRight.constitutional.rule2 := by
    simpa only [localizedRerootCumulativeRule45Observable] using
      congrArg LocalizedCumulativeRule45Observable.rule2 observable
  simp only [constitutionalObservable, rule1aEq, rule1bEq, rule2Eq]

/-! ## 2.  A comparator tie and two table matches give the three actual column equalities -/

/-- **Actual column equalities from a comparator tie.**  Each decorated tree's four addressed
tables equal its key's tables (`LocalizedCumulativeTreeTableMatch`), and the two keys' constitutional
observables agree.  Then the three constitutional columns of the two trees agree exactly.

The two stages are independent: the descriptor stage is never read. -/
theorem constitutionalColumns_eq_of_actualComparison
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key)
    (leftMatch : LocalizedCumulativeTreeTableMatch stageLeft left keyLeft)
    (rightMatch : LocalizedCumulativeTreeTableMatch stageRight right keyRight)
    (observableEq : constitutionalObservable keyLeft.constitutional =
      constitutionalObservable keyRight.constitutional) :
    (tables stageLeft left).rule1a = (tables stageRight right).rule1a ∧
      (tables stageLeft left).rule1b = (tables stageRight right).rule1b ∧
        (tables stageLeft left).rule2 = (tables stageRight right).rule2 := by
  obtain ⟨left1a, left1b, left2, _leftDescriptor⟩ := leftMatch
  obtain ⟨right1a, right1b, right2, _rightDescriptor⟩ := rightMatch
  refine ⟨?_, ?_, ?_⟩
  · rw [left1a, right1a]
    exact congrArg LocalizedConstitutionalObservable.rule1a observableEq
  · rw [left1b, right1b]
    exact congrArg LocalizedConstitutionalObservable.rule1b observableEq
  · rw [left2, right2]
    exact congrArg LocalizedConstitutionalObservable.rule2 observableEq




theorem shape_eq_of_actualComparison
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key)
    (leftMatch : LocalizedCumulativeTreeTableMatch stageLeft left keyLeft)
    (rightMatch : LocalizedCumulativeTreeTableMatch stageRight right keyRight)
    (observableEq : constitutionalObservable keyLeft.constitutional =
      constitutionalObservable keyRight.constitutional) :
    shape left = shape right := by
  obtain ⟨rule1aEq, rule1bEq, rule2Eq⟩ :=
    constitutionalColumns_eq_of_actualComparison input stageLeft stageRight left right
      keyLeft keyRight leftMatch rightMatch observableEq
  exact table_shape_eq_of_columns_eq stageLeft stageRight left right rule1aEq rule1bEq rule2Eq

/-- **Actual equal shapes from the cumulative full comparator.**  Same conclusion starting from
`compareLocalizedRerootCumulativeRule45Keys = eq` on the two keys. -/
theorem shape_eq_of_fullCompare_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key)
    (leftMatch : LocalizedCumulativeTreeTableMatch stageLeft left keyLeft)
    (rightMatch : LocalizedCumulativeTreeTableMatch stageRight right keyRight)
    (compared : input.compareLocalizedRerootCumulativeRule45Keys keyLeft keyRight =
      Ordering.eq) :
    shape left = shape right :=
  shape_eq_of_actualComparison input stageLeft stageRight left right keyLeft keyRight
    leftMatch rightMatch
    (constitutionalObservable_eq_of_fullCompare_eq input keyLeft keyRight compared)

/-! ## 3.  Actual trees with equal shape from successful actual builds and a comparator tie -/










theorem exists_shape_eq_of_actualComparison
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuelLeft fuelRight : Nat)
    (cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel)
    (keyLeft keyRight : input.LocalizedRerootCumulativeRule45Key)
    (builtLeft : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stageLeft readLeft fuelLeft cursorLeft = some keyLeft)
    (builtRight : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      stageRight readRight fuelRight cursorRight = some keyRight)
    (compared : input.compareLocalizedConstitutionalCursors? cursorLeft cursorRight =
      some Ordering.eq) :
    ∃ leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel,
      leftTree.source = cursorLeft ∧ rightTree.source = cursorRight ∧
        LocalizedCumulativeTreeFullMatch stageLeft leftTree keyLeft ∧
          LocalizedCumulativeTreeFullMatch stageRight rightTree keyRight ∧
            LocalizedCumulativeTreeRealizes input readLeft leftTree ∧
              LocalizedCumulativeTreeRealizes input readRight rightTree ∧
                shape leftTree = shape rightTree := by
  obtain ⟨leftTree, leftSource, leftFull, leftRealizes, _leftChildren, _leftPerm⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input stageLeft readLeft fuelLeft
      cursorLeft keyLeft builtLeft
  obtain ⟨rightTree, rightSource, rightFull, rightRealizes, _rightChildren, _rightPerm⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input stageRight readRight fuelRight
      cursorRight keyRight builtRight
  refine ⟨leftTree, rightTree, leftSource, rightSource, leftFull, rightFull,
    leftRealizes, rightRealizes, ?_⟩
  exact shape_eq_of_actualComparison input stageLeft stageRight leftTree rightTree
    keyLeft keyRight leftFull.tableMatch rightFull.tableMatch
    (constitutionalObservable_eq_of_compareCursors_eq input stageLeft stageRight
      readLeft readRight fuelLeft fuelRight cursorLeft cursorRight keyLeft keyRight
      builtLeft builtRight compared)

/-! ## 4.  The weighted physical data of an actual comparator tie -/













structure ActualComparisonBondData
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key) where
  acyclic : input.moleculeGraph.Acyclic
  enough : input.certified.input.molecule.atomCount ≤ carrierFuel
  leftRealizes : LocalizedCumulativeTreeRealizes input readLeft left
  rightRealizes : LocalizedCumulativeTreeRealizes input readRight right
  leftRootReal : left.source.occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  rightRootReal : right.source.occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  leftStage : LocalizedCumulativeRule45Stage
  rightStage : LocalizedCumulativeRule45Stage
  leftMatch : LocalizedCumulativeTreeTableMatch leftStage left leftKey
  rightMatch : LocalizedCumulativeTreeTableMatch rightStage right rightKey
  tie : constitutionalObservable leftKey.constitutional =
    constitutionalObservable rightKey.constitutional
  leftPrevious : input.LocalizedCIPOccurrence carrierFuel
  leftIncoming : left.source.previous? = some leftPrevious
  leftSameRoot : left.source.occurrence.1.root = leftPrevious.1.root
  leftValid : input.LocalizedRerootCursorValid left.source
  leftPreviousReal : leftPrevious.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  rightPrevious : input.LocalizedCIPOccurrence carrierFuel
  rightIncoming : right.source.previous? = some rightPrevious
  rightSameRoot : right.source.occurrence.1.root = rightPrevious.1.root
  rightValid : input.LocalizedRerootCursorValid right.source
  rightPreviousReal : rightPrevious.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  oAtomL : input.Atom
  pAtomL : input.Atom
  oAtomR : input.Atom
  pAtomR : input.Atom
  leftObserved : left.source.occurrence.1.node.current? = some oAtomL
  leftPreviousObserved : leftPrevious.1.node.current? = some pAtomL
  leftIncomingEdge : input.moleculeGraph.Adj pAtomL oAtomL
  rightObserved : right.source.occurrence.1.node.current? = some oAtomR
  rightPreviousObserved : rightPrevious.1.node.current? = some pAtomR
  rightIncomingEdge : input.moleculeGraph.Adj pAtomR oAtomR

section ActualComparisonTransport

/-- **The derived actual shape equality of a comparator tie.** -/
theorem actualComparisonShapeEq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey) :
    shape left = shape right :=
  shape_eq_of_actualComparison input D.leftStage D.rightStage left right leftKey rightKey
    D.leftMatch D.rightMatch D.tie



noncomputable def toShapeBondData
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey) :
    ActualShapeBondData input carrierFuel readLeft readRight left right where
  acyclic := D.acyclic
  enough := D.enough
  leftRealizes := D.leftRealizes
  rightRealizes := D.rightRealizes
  leftRootReal := D.leftRootReal
  rightRootReal := D.rightRootReal
  hshape := actualComparisonShapeEq input D
  leftPrevious := D.leftPrevious
  leftIncoming := D.leftIncoming
  leftSameRoot := D.leftSameRoot
  leftValid := D.leftValid
  leftPreviousReal := D.leftPreviousReal
  rightPrevious := D.rightPrevious
  rightIncoming := D.rightIncoming
  rightSameRoot := D.rightSameRoot
  rightValid := D.rightValid
  rightPreviousReal := D.rightPreviousReal
  oAtomL := D.oAtomL
  pAtomL := D.pAtomL
  oAtomR := D.oAtomR
  pAtomR := D.pAtomR
  leftObserved := D.leftObserved
  leftPreviousObserved := D.leftPreviousObserved
  leftIncomingEdge := D.leftIncomingEdge
  rightObserved := D.rightObserved
  rightPreviousObserved := D.rightPreviousObserved
  rightIncomingEdge := D.rightIncomingEdge



noncomputable def actualComparisonBranchIso
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey) :
    RootedBranchIso (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal)
      (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal) :=
  actualShapeBranchIso (toShapeBondData input D)












theorem actualComparison_bond_order_transport
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey) :
    (∀ p : RealPosition left, actualPhysicalIncidentExcess p =
      actualPhysicalIncidentExcess ((actualComparisonBranchIso input D).toEquiv p)) ∧
    (∀ p : RealPosition left,
      actualIncomingExcessAt
        (canonicalRealPositionRootedBranch D.leftRealizes D.leftRootReal) D.pAtomL p =
      actualIncomingExcessAt
        (canonicalRealPositionRootedBranch D.rightRealizes D.rightRootReal) D.pAtomR
        ((actualComparisonBranchIso input D).toEquiv p)) ∧
    (∀ (p c : RealPosition left), RealPositionChild p c →
      input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom c) =
        input.moleculeGraph.bond
          (realPositionAtom ((actualComparisonBranchIso input D).toEquiv p))
          (realPositionAtom ((actualComparisonBranchIso input D).toEquiv c))) ∧
    input.moleculeGraph.bond D.pAtomL
        (realPositionAtom ⟨rootPosition left, D.leftRootReal⟩) =
      input.moleculeGraph.bond D.pAtomR
        (realPositionAtom ⟨rootPosition right, D.rightRootReal⟩) := by
  have transported := actualShape_bond_order_transport (readLeft := readLeft)
    (readRight := readRight) (left := left) (right := right)
    (toShapeBondData input D)
  simpa only [actualComparisonBranchIso, actualLeftIncomingExcess,
    actualRightIncomingExcess, toShapeBondData] using transported



theorem actualComparison_adjacent_bond_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey)
    (p q : RealPosition left)
    (adjacent : input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom q)) :
    input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom q) =
      input.moleculeGraph.bond
        (realPositionAtom ((actualComparisonBranchIso input D).toEquiv p))
        (realPositionAtom ((actualComparisonBranchIso input D).toEquiv q)) := by
  have transported := actualAdjacentBondEq (readLeft := readLeft) (readRight := readRight)
    (left := left) (right := right) (toShapeBondData input D) p q adjacent
  simpa only [actualComparisonBranchIso, toShapeBondData] using transported



theorem actualComparisonBranchIso_apply_val
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey)
    (p : RealPosition left) :
    ((actualComparisonBranchIso input D).toEquiv p).1.val = p.1.val :=
  realPositionShapeEquiv_apply_val D.acyclic D.leftRealizes D.rightRealizes
    D.leftRootReal D.rightRootReal (actualComparisonShapeEq input D) p

/-! ## 5.  atomicZ / mass preservation at every mapped real position -/

/-- **A realized decorated tree is the `localizedRootTree` of its own source.**  The unique
constructor of `LocalizedCumulativeTreeRealizes` exposes its root cursor and its sorted children. -/
theorem exists_eq_localizedRootTree_of_realizes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    ∃ (cursor : input.LocalizedRerootCursor carrierFuel)
      (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)),
      tree = localizedRootTree input cursor (read cursor) children := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      exact ⟨cursor, sortedChildren, rfl⟩

/-- **The constitutional columns of a realized position node are the official atom-label
components.**  For any realized decorated tree, the node at any position is its own
`localizedRootTree`, hence its Rule-1a atomic number and Rule-2 isotope mass are the two components
of the official atom label of its source node's current atom, and its Rule-1b distance is the
node's original-root distance.  This needs no `SimpleBonded` hypothesis. -/
theorem positionNode_columns_eq_officialLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).atomicNumber =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          (positionNode p).source.occurrence.1.node)).1 ∧
      (positionNode p).rule1bDistance =
          (positionNode p).source.occurrence.1.node.rule1bRootDistance ∧
        (positionNode p).isotopeMass =
          (ofLex (input.moleculeGraph.officialNodeAtomLabel
            (positionNode p).source.occurrence.1.node)).2 := by
  obtain ⟨cursor, children, nodeEq⟩ :=
    exists_eq_localizedRootTree_of_realizes input
      (read := read) (realizes_of_subtree realizes (positionNode_spec p))
  rw [nodeEq]
  exact ⟨rfl, rfl, rfl⟩

/-- **The real-position equivalence keeps the underlying position.**  `realPositionShapeEquiv` is
`shapePositionEquiv` lifted to the real-position subtype; its underlying `Position` is exactly
`shapePositionEquiv` at the same address. -/
theorem realPositionShapeEquiv_apply_position_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    (acyclic : input.moleculeGraph.Acyclic)
    (leftRealizes : LocalizedCumulativeTreeRealizes input readLeft left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (hshape : shape left = shape right) (p : RealPosition left) :
    ((realPositionShapeEquiv acyclic leftRealizes rightRealizes leftRootReal rightRootReal
      hshape p).1) = shapePositionEquiv hshape p.1 := rfl






theorem actualComparison_node_columns
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey)
    (p : RealPosition left) :
    (positionNode ((actualComparisonBranchIso input D).toEquiv p).1).atomicNumber =
        (positionNode p.1).atomicNumber ∧
      (positionNode ((actualComparisonBranchIso input D).toEquiv p).1).rule1bDistance =
          (positionNode p.1).rule1bDistance ∧
        (positionNode ((actualComparisonBranchIso input D).toEquiv p).1).isotopeMass =
            (positionNode p.1).isotopeMass := by
  have mapEq : (actualComparisonBranchIso input D).toEquiv =
      realPositionShapeEquiv D.acyclic D.leftRealizes D.rightRealizes D.leftRootReal
        D.rightRootReal (actualComparisonShapeEq input D) := rfl
  rw [mapEq]
  rw [realPositionShapeEquiv_apply_position_eq input D.acyclic D.leftRealizes
    D.rightRealizes D.leftRootReal D.rightRootReal (actualComparisonShapeEq input D) p]
  have nodeShape :=
    shapePositionEquiv_positionNode_shape_eq (actualComparisonShapeEq input D) p.1
  have atomicEq := congrArg (fun node => node.atomicNumber) nodeShape
  have distanceEq := congrArg (fun node => node.rule1bDistance) nodeShape
  have massEq := congrArg (fun node => node.isotopeMass) nodeShape
  exact ⟨by simpa only [shape_atomicNumber] using atomicEq,
    by simpa only [shape_rule1bDistance] using distanceEq,
    by simpa only [shape_isotopeMass] using massEq⟩

/-- **atomicZ / mass preservation in official-label form.**  At every mapped real position the
official atom label of the physical atom is preserved in both its Rule-1a atomic-number component
and its Rule-2 isotope-mass component, and the Rule-1b original-root distance of the two positions
agrees as well.

The physical atom of a position is the current atom (`realPositionAtom`) of its node source, and
`officialNodeAtomLabel` is exactly the label read by the shipped constitutional rules; the bridge
from the tree columns to that label at any realized node is
`positionNode_columns_eq_officialLabel`.  No `SimpleBonded` hypothesis is used. -/
theorem actualComparison_officialLabel_columns
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {left right : LocalizedCumulativeDecoratedTree input carrierFuel}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (D : ActualComparisonBondData input carrierFuel readLeft readRight left right
      leftKey rightKey)
    (p : RealPosition left) :
    (ofLex (input.moleculeGraph.officialNodeAtomLabel
        (positionNode ((actualComparisonBranchIso input D).toEquiv p).1).source.occurrence.1.node)).1 =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          (positionNode p.1).source.occurrence.1.node)).1 ∧
      (positionNode ((actualComparisonBranchIso input D).toEquiv p).1).source.occurrence.1.node.rule1bRootDistance =
        (positionNode p.1).source.occurrence.1.node.rule1bRootDistance ∧
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
          (positionNode ((actualComparisonBranchIso input D).toEquiv p).1).source.occurrence.1.node)).2 =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          (positionNode p.1).source.occurrence.1.node)).2 := by
  obtain ⟨mappedAtomic, mappedDistance, mappedMass⟩ :=
    positionNode_columns_eq_officialLabel input (read := readRight) D.rightRealizes
      ((actualComparisonBranchIso input D).toEquiv p).1
  obtain ⟨leftAtomic, leftDistance, leftMass⟩ :=
    positionNode_columns_eq_officialLabel input (read := readLeft) D.leftRealizes p.1
  obtain ⟨columnsAtomic, columnsDistance, columnsMass⟩ :=
    actualComparison_node_columns input D p
  exact ⟨mappedAtomic.symm.trans (columnsAtomic.trans leftAtomic),
    mappedDistance.symm.trans (columnsDistance.trans leftDistance),
    mappedMass.symm.trans (columnsMass.trans leftMass)⟩

end ActualComparisonTransport

/-! ## 6.  The adequate-budget actual wrapper -/




























theorem exists_actualKeyTie_weightedReconstruction
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (readLeft readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (cursorLeft cursorRight : input.LocalizedRerootCursor carrierFuel)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid cursorLeft)
    (rightValid : input.LocalizedRerootCursorValid cursorRight)
    (leftRootReal : cursorLeft.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : cursorRight.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (leftPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (leftIncoming : cursorLeft.previous? = some leftPrevious)
    (leftSameRoot : cursorLeft.occurrence.1.root = leftPrevious.1.root)
    (leftPreviousReal : leftPrevious.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (rightIncoming : cursorRight.previous? = some rightPrevious)
    (rightSameRoot : cursorRight.occurrence.1.root = rightPrevious.1.root)
    (rightPreviousReal : rightPrevious.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    {oAtomL pAtomL oAtomR pAtomR : input.Atom}
    (leftObserved : cursorLeft.occurrence.1.node.current? = some oAtomL)
    (leftPreviousObserved : leftPrevious.1.node.current? = some pAtomL)
    (leftIncomingEdge : input.moleculeGraph.Adj pAtomL oAtomL)
    (rightObserved : cursorRight.occurrence.1.node.current? = some oAtomR)
    (rightPreviousObserved : rightPrevious.1.node.current? = some pAtomR)
    (rightIncomingEdge : input.moleculeGraph.Adj pAtomR oAtomR)
    (compared : input.compareLocalizedConstitutionalCursors? cursorLeft cursorRight =
      some Ordering.eq) :
    ∃ (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
      (leftTree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (leftRealizesTree : LocalizedCumulativeTreeRealizes input readLeft leftTree)
      (leftRootRealTree : leftTree.source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom)
      (rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (rightRealizesTree : LocalizedCumulativeTreeRealizes input readRight rightTree)
      (rightRootRealTree : rightTree.source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom)
      (shapeEq : shape leftTree = shape rightTree)
      (iso : RootedBranchIso
        (canonicalRealPositionRootedBranch leftRealizesTree leftRootRealTree)
        (canonicalRealPositionRootedBranch rightRealizesTree rightRootRealTree)),
      leftTree.source = cursorLeft ∧
      rightTree.source = cursorRight ∧
      LocalizedCumulativeTreeFullMatch stageLeft leftTree leftKey ∧
      LocalizedCumulativeTreeFullMatch stageRight rightTree rightKey ∧
      iso = actualRealPositionBranchIso acyclic leftRealizesTree rightRealizesTree
        leftRootRealTree rightRootRealTree shapeEq ∧
      (∀ p : RealPosition leftTree, (iso.toEquiv p).1.val = p.1.val) ∧
      (∀ p : RealPosition leftTree, actualPhysicalIncidentExcess p =
        actualPhysicalIncidentExcess (iso.toEquiv p)) ∧
      (∀ p : RealPosition leftTree,
        actualIncomingExcessAt
          (canonicalRealPositionRootedBranch leftRealizesTree leftRootRealTree) pAtomL p =
        actualIncomingExcessAt
          (canonicalRealPositionRootedBranch rightRealizesTree rightRootRealTree) pAtomR
          (iso.toEquiv p)) ∧
      (∀ (p c : RealPosition leftTree), RealPositionChild p c →
        input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom c) =
          input.moleculeGraph.bond (realPositionAtom (iso.toEquiv p))
            (realPositionAtom (iso.toEquiv c))) ∧
      input.moleculeGraph.bond pAtomL
          (realPositionAtom ⟨rootPosition leftTree, leftRootRealTree⟩) =
        input.moleculeGraph.bond pAtomR
          (realPositionAtom ⟨rootPosition rightTree, rightRootRealTree⟩) ∧
      (∀ (p q : RealPosition leftTree),
        input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom q) →
        input.moleculeGraph.bond (realPositionAtom p) (realPositionAtom q) =
          input.moleculeGraph.bond (realPositionAtom (iso.toEquiv p))
            (realPositionAtom (iso.toEquiv q))) ∧
      (∀ p : RealPosition leftTree,
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
            (positionNode (iso.toEquiv p).1).source.occurrence.1.node)).1 =
          (ofLex (input.moleculeGraph.officialNodeAtomLabel
            (positionNode p.1).source.occurrence.1.node)).1 ∧
        (positionNode (iso.toEquiv p).1).source.occurrence.1.node.rule1bRootDistance =
          (positionNode p.1).source.occurrence.1.node.rule1bRootDistance ∧
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
            (positionNode (iso.toEquiv p).1).source.occurrence.1.node)).2 =
          (ofLex (input.moleculeGraph.officialNodeAtomLabel
            (positionNode p.1).source.occurrence.1.node)).2) := by

  obtain ⟨leftKey, leftBuilt⟩ :=
    CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input stageLeft readLeft cursorLeft leftValid
  obtain ⟨rightKey, rightBuilt⟩ :=
    CertifiedLocalizedCIPInput.WholeStateCumulativeLabels.exists_buildLocalizedRerootCumulativeRule45KeyWithRead?_at_twice
      input stageRight readRight cursorRight rightValid

  obtain ⟨leftTree, leftSource, leftFull, leftRealizesTree, _leftChildren, _leftPerm⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input stageLeft readLeft
      (2 * (carrierFuel + 1)) cursorLeft leftKey leftBuilt
  obtain ⟨rightTree, rightSource, rightFull, rightRealizesTree, _rightChildren, _rightPerm⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input stageRight readRight
      (2 * (carrierFuel + 1)) cursorRight rightKey rightBuilt
  have leftRootRealTree : leftTree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [leftSource]
    exact leftRootReal
  have rightRootRealTree : rightTree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [rightSource]
    exact rightRootReal
  -- Section 1: the production comparator tie forces equal constitutional observables.
  have tie : constitutionalObservable leftKey.constitutional =
      constitutionalObservable rightKey.constitutional :=
    constitutionalObservable_eq_of_compareCursors_eq input stageLeft stageRight readLeft
      readRight (2 * (carrierFuel + 1)) (2 * (carrierFuel + 1)) cursorLeft cursorRight
      leftKey rightKey leftBuilt rightBuilt compared
  -- Section 2: the tie plus the two actual table matches give the erased shape equality.
  let shapeEq : shape leftTree = shape rightTree :=
    shape_eq_of_actualComparison input stageLeft stageRight leftTree rightTree leftKey
      rightKey leftFull.tableMatch rightFull.tableMatch tie
  -- The actual comparison bond data of the two derived trees.
  let D : ActualComparisonBondData input carrierFuel readLeft readRight leftTree rightTree
      leftKey rightKey :=
    { acyclic := acyclic
      enough := enough
      leftRealizes := leftRealizesTree
      rightRealizes := rightRealizesTree
      leftRootReal := leftRootRealTree
      rightRootReal := rightRootRealTree
      leftStage := stageLeft
      rightStage := stageRight
      leftMatch := leftFull.tableMatch
      rightMatch := rightFull.tableMatch
      tie := tie
      leftPrevious := leftPrevious
      leftIncoming := by rw [leftSource]; exact leftIncoming
      leftSameRoot := by rw [leftSource]; exact leftSameRoot
      leftValid := by rw [leftSource]; exact leftValid
      leftPreviousReal := leftPreviousReal
      rightPrevious := rightPrevious
      rightIncoming := by rw [rightSource]; exact rightIncoming
      rightSameRoot := by rw [rightSource]; exact rightSameRoot
      rightValid := by rw [rightSource]; exact rightValid
      rightPreviousReal := rightPreviousReal
      oAtomL := oAtomL
      pAtomL := pAtomL
      oAtomR := oAtomR
      pAtomR := pAtomR
      leftObserved := by rw [leftSource]; exact leftObserved
      leftPreviousObserved := leftPreviousObserved
      leftIncomingEdge := leftIncomingEdge
      rightObserved := by rw [rightSource]; exact rightObserved
      rightPreviousObserved := rightPreviousObserved
      rightIncomingEdge := rightIncomingEdge }
  -- The two isomorphisms have the same underlying position equivalence.
  have isoEq : (actualComparisonBranchIso input D).toEquiv =
      (actualRealPositionBranchIso acyclic leftRealizesTree rightRealizesTree
        leftRootRealTree rightRootRealTree shapeEq).toEquiv := rfl
  refine ⟨leftKey, rightKey, leftTree, leftRealizesTree, leftRootRealTree, rightTree,
    rightRealizesTree, rightRootRealTree, shapeEq,
    actualRealPositionBranchIso acyclic leftRealizesTree rightRealizesTree leftRootRealTree
      rightRootRealTree shapeEq, ?_⟩
  rw [← isoEq]
  exact ⟨leftSource, rightSource, leftFull, rightFull, rfl,
    fun p => actualComparisonBranchIso_apply_val input D p,
    (actualComparison_bond_order_transport input D).1,
    (actualComparison_bond_order_transport input D).2.1,
    (actualComparison_bond_order_transport input D).2.2.1,
    (actualComparison_bond_order_transport input D).2.2.2,
    fun p q adjacent => actualComparison_adjacent_bond_eq input D p q adjacent,
    fun p => actualComparison_officialLabel_columns input D p⟩

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.constitutionalObservable_eq_of_compareCursors_eq
assert_kernel_only TetraStereo.OneCenter.constitutionalObservable_eq_of_fullCompare_eq
assert_kernel_only TetraStereo.OneCenter.constitutionalColumns_eq_of_actualComparison
assert_kernel_only TetraStereo.OneCenter.shape_eq_of_actualComparison
assert_kernel_only TetraStereo.OneCenter.shape_eq_of_fullCompare_eq
assert_kernel_only TetraStereo.OneCenter.exists_shape_eq_of_actualComparison
assert_kernel_only TetraStereo.OneCenter.ActualComparisonBondData
assert_kernel_only TetraStereo.OneCenter.actualComparisonShapeEq
assert_kernel_only TetraStereo.OneCenter.toShapeBondData
assert_kernel_only TetraStereo.OneCenter.actualComparisonBranchIso
assert_kernel_only TetraStereo.OneCenter.actualComparison_bond_order_transport
assert_kernel_only TetraStereo.OneCenter.actualComparison_adjacent_bond_eq
assert_kernel_only TetraStereo.OneCenter.actualComparisonBranchIso_apply_val
assert_kernel_only TetraStereo.OneCenter.exists_eq_localizedRootTree_of_realizes
assert_kernel_only TetraStereo.OneCenter.positionNode_columns_eq_officialLabel
assert_kernel_only TetraStereo.OneCenter.realPositionShapeEquiv_apply_position_eq
assert_kernel_only TetraStereo.OneCenter.actualComparison_node_columns
assert_kernel_only TetraStereo.OneCenter.actualComparison_officialLabel_columns
assert_kernel_only TetraStereo.OneCenter.exists_actualKeyTie_weightedReconstruction
