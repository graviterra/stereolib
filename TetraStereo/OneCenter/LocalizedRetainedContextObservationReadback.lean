import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge
import TetraStereo.OneCenter.DeclarativeCIPRetainedContextObservation
import TetraStereo.OneCenter.LocalizedContextTreeReadback
import TetraStereo.OneCenter.LocalizedContextBranchStages
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Retained constitutional observations on realized contextual trees

The approved retained observer reads a real Rule 1b distance as the length of
`rerootWalk unit.root unit.path (ancestorAtoms node)`.  On an arbitrary realized child of a
detected target, that walk is derived from the actual subtree cursor: it is
`molecularFrameUnit.path`, including the ligand root and without an acyclicity hypothesis.
Ring-duplicate leaves keep the stored duplicate distance.  Rules 1a and 2 stay the established
atom observations.

The same derived walk feeds the molecular reader.  A real node reads `readContext`; its reading
is never `unavailable`.  A ring duplicate reads `unavailable`.  No fresh-root, fixed-depth, or
original-ligand restriction is used, and physical shortest distance is not identified with the
retained length.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open MolecularEvidenceTree
open LocalizedCumulativeDecoratedTree
open TetraStereo.OneCenter.Rule4aTableBridge

variable (input : CertifiedLocalizedCIPInput)

private theorem history_reverse_eq_cons_tail
    {α : Type} {history : List α} {root : α}
    (last : history.getLast? = some root) :
    history.reverse = root :: history.reverse.tail := by
  have nonempty : history ≠ [] := by
    intro empty
    simp [empty] at last
  have headEq : history.reverse.head? = some root := by
    have raw := (List.getLast?_reverse (l := history.reverse)).symm
    rw [List.reverse_reverse] at raw
    exact raw.trans last
  cases reverseEq : history.reverse with
  | nil =>
      exact absurd (by simpa using congrArg List.reverse reverseEq) nonempty
  | cons head tail =>
      have headRoot : head = root := by
        have headSome : history.reverse.head? = some head := by simp [reverseEq]
        exact Option.some.inj (headSome.symm.trans headEq)
      subst headRoot
      rfl

/-- Every simple-bonded carrier frame has path length equal to the official history depth.
The path is `history.reverse.tail`, and every such history ends at the stored root. -/
theorem retainedFramePathLength_eq_officialDepth
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    (input.molecularFrameUnit occurrence.1).path.length = occurrence.1.node.depth := by
  have last := input.carrierOccurrence_history_getLast_eq_root singleBonded occurrence
  have rev := history_reverse_eq_cons_tail last
  have lengthEq : occurrence.1.node.history.length =
      (input.molecularFrameUnit occurrence.1).path.length + 1 := by
    have hlen := congrArg List.length rev
    rw [List.length_reverse, List.length_cons] at hlen
    simp only [molecularFrameUnit]
    exact hlen
  unfold OfficialCIPNode.depth
  omega

/-- A real carrier node stores Rule 1b as its official depth, which is the frame-path length. -/
theorem retainedRealRule1bRootDistance_eq_framePathLength
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    occurrence.1.node.rule1bRootDistance =
      (input.molecularFrameUnit occurrence.1).path.length := by
  simp [OfficialCIPNode.rule1bRootDistance, real,
    retainedFramePathLength_eq_officialDepth input singleBonded occurrence]

/-- A ring-duplicate carrier node stores Rule 1b as the duplicate-provenance distance. -/
theorem retainedRingRule1bRootDistance_eq_stored
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) {distance : Nat}
    (ring : occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    occurrence.1.node.rule1bRootDistance = distance := by
  simp [OfficialCIPNode.rule1bRootDistance, ring]

/-- An executable parent is not a duplicate leaf, hence on a single-bond molecule it is real. -/
theorem retainedExecutableParent_realAtom
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (source child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren source) :
    source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  have childIntended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames source := by
    rw [← input.executableLocalizedRerootChildren_map source]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have notDuplicate : source.occurrence.1.node.isDuplicateLeaf = false := by
    by_cases duplicate : source.occurrence.1.node.isDuplicateLeaf = true
    · unfold intendedLocalizedRerootChildFrames at childIntended
      rw [if_pos duplicate] at childIntended
      cases childIntended
    · exact (Bool.not_eq_true _).mp duplicate
  cases input.carrierOccurrence_provenance_simple_or_ring singleBonded source.occurrence with
  | inl real => exact real
  | inr ring =>
      obtain ⟨distance, ring⟩ := ring
      simp [OfficialCIPNode.isDuplicateLeaf, ring,
        OfficialCIPNodeProvenance.isDuplicateLeaf] at notDuplicate

private theorem pathLabels_cons_extract
    {Atom : Type} {root : Atom} {labels : List (Option Atom)} {steps : List Atom}
    (h : some root :: labels = steps.map some) :
    ∃ rest, steps = root :: rest ∧ labels = rest.map some := by
  cases steps with
  | nil => simp at h
  | cons first rest =>
      change some root :: labels = some first :: rest.map some at h
      obtain ⟨headEq, tailEq⟩ := List.cons.inj h
      have firstEq : first = root := (Option.some.inj headEq).symm
      subst first
      exact ⟨rest, rfl, tailEq⟩

private theorem cursor_current_exists {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∃ atom, cursor.occurrence.1.node.current? = some atom := by
  have derived := (input.mem_localizedOccurrences_iff carrierFuel
    cursor.occurrence.1).mp cursor.occurrence.2
  exact Option.isSome_iff_exists.mp
    (input.declarativeLocalizedOccurrence_node_current_isSome derived)

/-- Path labels of a realized subtree are an atom list.  Ring leaves are included: every carrier
cursor has a current atom. -/
private theorem pathLabels_exists_some_of_realizedSubtree
    {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {address : List Nat} {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree address = some actual) :
    ∃ steps : List input.Atom,
      MolecularEvidenceTree.pathLabels (toOfficialSourceTree tree) address = steps.map some := by
  induction address generalizing tree actual with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      have actualEq : actual = tree := (Option.some.inj lookup).symm
      subst actual
      obtain ⟨rootAtom, rootCurrent⟩ := cursor_current_exists input tree.source
      refine ⟨[rootAtom], ?_⟩
      change [((toOfficialSourceTree tree).sourceAtAddress? []).bind
        OfficialCIPNode.current?] = [some rootAtom]
      simp only [OfficialCIPSourceTree.sourceAtAddress?, OfficialCIPSourceTree.subtreeAt?,
        Option.map_some, Option.bind_some]
      rw [toOfficialSourceTree_source, rootCurrent]
  | cons slot rest ih =>
      obtain ⟨child, childLookup, restLookup⟩ :=
        (subtreeAt?_cons_eq_some_iff).mp lookup
      cases tree with
      | mk source atomicNumber rule1bDistance isotopeMass label children =>
          have childOfficialLookup :
              (toOfficialSourceTreeList children)[slot]? = some (toOfficialSourceTree child) := by
            rw [toOfficialSourceTreeList_eq_map]
            simp [childLookup]
          obtain ⟨tailSteps, tailLabels⟩ := ih (tree := child) (actual := actual) restLookup
          obtain ⟨rootAtom, rootCurrent⟩ := cursor_current_exists input source
          have labelsCons := MolecularEvidenceTree.pathLabels_cons source.occurrence.1.node
            (toOfficialSourceTreeList children) slot rest (toOfficialSourceTree child)
            childOfficialLookup
          refine ⟨rootAtom :: tailSteps, ?_⟩
          rw [toOfficialSourceTree_mk, labelsCons, rootCurrent, tailLabels]
          rfl

/-- The frame of a realized subtree is the retained reroot walk of its path labels.  The root
child may be any executable child of the detected target, and a deeper node may be a ring
duplicate.  Acyclicity is not used: each step is
`molecularFrameUnit_executableChild_rerootStep_of_simpleBonded`. -/
theorem retainedMolecularFrameUnit_eq_rerootWalk_of_realizedPathLabels
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    {target : input.LocalizedRerootCursor carrierFuel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    {address : List Nat} {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree address = some actual)
    {rootAtom : input.Atom}
    (rootCurrent : tree.source.occurrence.1.node.current? = some rootAtom)
    {steps : List input.Atom}
    (labels : MolecularEvidenceTree.pathLabels (toOfficialSourceTree tree) address =
      steps.map some) :
    (input.molecularFrameUnit actual.source.occurrence.1).root =
        (input.molecularFrameUnit target.occurrence.1).root ∧
      (input.molecularFrameUnit actual.source.occurrence.1).path =
        rerootWalk (input.molecularFrameUnit target.occurrence.1).root
          (input.molecularFrameUnit target.occurrence.1).path steps := by
  induction address generalizing target tree actual rootAtom steps realizes rootChild
      rootCurrent with
  | nil =>
      have actualEq : actual = tree := by
        rw [subtreeAt?_nil] at lookup
        exact (Option.some.inj lookup).symm
      subst actual
      have labelsRoot : MolecularEvidenceTree.pathLabels (toOfficialSourceTree tree) [] =
          [some rootAtom] := by
        change [((toOfficialSourceTree tree).sourceAtAddress? []).bind
          OfficialCIPNode.current?] = [some rootAtom]
        simp only [OfficialCIPSourceTree.sourceAtAddress?, OfficialCIPSourceTree.subtreeAt?,
          Option.map_some, Option.bind_some]
        rw [toOfficialSourceTree_source, rootCurrent]
      have stepsEq : steps = [rootAtom] := by
        apply (List.map_injective_iff.mpr (fun a b h => Option.some.inj h))
        calc
          steps.map some = [some rootAtom] := labels.symm.trans labelsRoot
          _ = [rootAtom].map some := rfl
      have step := input.molecularFrameUnit_executableChild_rerootStep_of_simpleBonded
        singleBonded target tree.source rootCurrent rootChild
      rw [stepsEq]
      simpa [rerootWalk] using step
  | cons slot rest ih =>
      obtain ⟨child, childLookup, restLookup⟩ :=
        (subtreeAt?_cons_eq_some_iff).mp lookup
      cases tree with
      | mk source atomicNumber rule1bDistance isotopeMass label children =>
          have childOfficialLookup :
              (toOfficialSourceTreeList children)[slot]? = some (toOfficialSourceTree child) := by
            rw [toOfficialSourceTreeList_eq_map]
            simp [childLookup]
          have labelsCons := MolecularEvidenceTree.pathLabels_cons source.occurrence.1.node
            (toOfficialSourceTreeList children) slot rest (toOfficialSourceTree child)
            childOfficialLookup
          have labels' : some rootAtom ::
              MolecularEvidenceTree.pathLabels (toOfficialSourceTree child) rest =
                steps.map some := by
            rw [toOfficialSourceTree_mk, labelsCons, rootCurrent] at labels
            exact labels
          obtain ⟨tailSteps, stepsEq, tailLabels⟩ := pathLabels_cons_extract labels'
          obtain ⟨childRootAtom, childRootCurrent⟩ :=
            cursor_current_exists input child.source
          have childRealizes := realizes_of_child realizes childLookup
          have childExec := mem_executable_of_child realizes childLookup
          have ihResult := ih (target := source) (tree := child) (actual := actual)
            (realizes := childRealizes) (rootChild := childExec) (lookup := restLookup)
            (rootCurrent := childRootCurrent) (steps := tailSteps) (labels := tailLabels)
          have rootStep := input.molecularFrameUnit_executableChild_rerootStep_of_simpleBonded
            singleBonded target source rootCurrent rootChild
          constructor
          · exact ihResult.1.trans rootStep.1
          · calc
              (input.molecularFrameUnit actual.source.occurrence.1).path =
                  rerootWalk (input.molecularFrameUnit source.occurrence.1).root
                    (input.molecularFrameUnit source.occurrence.1).path tailSteps := ihResult.2
              _ = rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                    (rerootStep (input.molecularFrameUnit target.occurrence.1).root
                      (input.molecularFrameUnit target.occurrence.1).path rootAtom)
                    tailSteps := by
                    rw [rootStep.1, rootStep.2]
              _ = rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                    (input.molecularFrameUnit target.occurrence.1).path
                    (rootAtom :: tailSteps) := by
                    change rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                        (rerootStep (input.molecularFrameUnit target.occurrence.1).root
                          (input.molecularFrameUnit target.occurrence.1).path rootAtom) tailSteps =
                      rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                        (input.molecularFrameUnit target.occurrence.1).path
                        ([rootAtom] ++ tailSteps)
                    rw [rerootWalk_append (input.molecularFrameUnit target.occurrence.1).root
                      (input.molecularFrameUnit target.occurrence.1).path [rootAtom] tailSteps]
                    simp [rerootWalk]
              _ = rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                    (input.molecularFrameUnit target.occurrence.1).path steps := by
                    rw [stepsEq]

/-- Derived path identity.  For every node of an actual child tree, `ancestorAtoms` is realized,
and the subtree cursor's molecular frame is exactly `rerootWalk` of the target frame along those
steps.  The identity is not a hypothesis. -/
theorem retainedCursorFrame_eq_ancestorWalk
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (target : input.LocalizedRerootCursor carrierFuel)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? tree node.1 = some actual) :
    ∃ steps : List input.Atom,
      retainedOccurrenceSteps (ruleMajorTreeGraph tree) node = some steps ∧
        (input.molecularFrameUnit actual.source.occurrence.1).root =
          (input.molecularFrameUnit target.occurrence.1).root ∧
        (input.molecularFrameUnit actual.source.occurrence.1).path =
          rerootWalk (input.molecularFrameUnit target.occurrence.1).root
            (input.molecularFrameUnit target.occurrence.1).path steps := by
  let sourceTree := toOfficialSourceTree tree
  obtain ⟨steps, labels⟩ := pathLabels_exists_some_of_realizedSubtree input lookup
  have stepsEq : ancestorAtoms sourceTree.toDeclarativeDigraph node = some steps :=
    input.ancestorAtoms_eq_some_of_pathLabels sourceTree node labels
  obtain ⟨rootAtom, rootCurrent⟩ := cursor_current_exists input tree.source
  obtain ⟨rootEq, pathEq⟩ :=
    input.retainedMolecularFrameUnit_eq_rerootWalk_of_realizedPathLabels singleBonded read
      realizes rootChild lookup rootCurrent labels
  refine ⟨steps, ?_, rootEq, pathEq⟩
  simpa [retainedOccurrenceSteps, ruleMajorTreeGraph] using stepsEq

private theorem subtreeAt?_eq_decoratedSubtreeAt?
    {carrierFuel : Nat} (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (address : List Nat) :
    subtreeAt? tree address = tree.decoratedSubtreeAt? address := by
  induction address generalizing tree with
  | nil => simp [subtreeAt?, decoratedSubtreeAt?]
  | cons slot rest ih =>
      simp only [subtreeAt?_cons, decoratedSubtreeAt?]
      cases tree.children[slot]? with
      | none => simp
      | some child =>
          simpa using ih child

private theorem retainedDeclarativeLabel_eq_source
    {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (node : (ruleMajorTreeGraph tree).Node)
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree node.1 = some actual) :
    (ruleMajorTreeGraph tree).label node =
      actual.source.occurrence.1.node.toDeclarativeLabel := by
  let sourceTree := toOfficialSourceTree tree
  have erased : sourceTree.subtreeAt? node.1 = some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, lookup]
    rfl
  have labelEq := sourceTree.declarativeLabel_eq_of_subtreeAt?
    (toOfficialSourceTree actual) node erased
  change sourceTree.declarativeLabel node = _
  rw [labelEq, toOfficialSourceTree_source]

/-- At every node of an actual child tree, the retained natural observation equals the actual
decorated observation.  Real Rule 1b is the derived walk length, which equals the official real
depth.  Ring Rule 1b is the stored duplicate distance.  Rules 1a and 2 are the production atom
label. -/
theorem retainedContextRuleValue_eq_armObservation
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (rule : ConstitutionalRule)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? tree node.1 = some actual) :
    retainedContextRuleValue input.moleculeGraph (ruleMajorTreeGraph tree) unit rule node =
      armObservation rule actual := by
  have labelEq := retainedDeclarativeLabel_eq_source input node lookup
  have decLookup : tree.decoratedSubtreeAt? node.1 = some actual := by
    rw [← subtreeAt?_eq_decoratedSubtreeAt? input tree node.1]
    exact lookup
  have shape := realizes_of_decoratedSubtreeAt? tree realizes node.1 actual decLookup
  have observed : armObservation rule actual =
      armSourceObservation input rule actual.source := by
    rw [shape]
    cases rule <;> rfl
  rw [observed]
  cases rule with
  | rule1aAtomicNumber =>
      simpa [retainedContextRuleValue, ruleValue, armSourceObservation, labelEq] using
        (MoleculeGraph.officialNodeAtomLabel_first_eq_nodeAtomicNumber
          input.moleculeGraph actual.source.occurrence.1.node).symm
  | rule2AtomicMass =>
      simpa [retainedContextRuleValue, ruleValue, armSourceObservation, labelEq] using
        (MoleculeGraph.officialNodeAtomLabel_second_eq_nodeAtomicMass
          input.moleculeGraph actual.source.occurrence.1.node).symm
  | rule1bDuplicateNodeProximity =>
      obtain ⟨steps, stepsEq, _rootEq, pathEq⟩ :=
        input.retainedCursorFrame_eq_ancestorWalk singleBonded target tree realizes rootChild
          node actual lookup
      have targetRoot : (input.molecularFrameUnit target.occurrence.1).root = unit.1.root :=
        congrArg OccurrenceUnit.root targetUnit
      have targetPath : (input.molecularFrameUnit target.occurrence.1).path = unit.1.path :=
        congrArg OccurrenceUnit.path targetUnit
      have walkEq : (input.molecularFrameUnit actual.source.occurrence.1).path =
          rerootWalk unit.1.root unit.1.path steps := by
        rw [pathEq, targetRoot, targetPath]
      cases input.carrierOccurrence_provenance_simple_or_ring singleBonded
          actual.source.occurrence with
      | inl real =>
          obtain ⟨atom, current⟩ := cursor_current_exists input actual.source
          have label : (ruleMajorTreeGraph tree).label node = ⟨some atom, .realAtom⟩ := by
            rw [labelEq, OfficialCIPNode.toDeclarativeLabel, current, real]
            rfl
          have distance :=
            input.retainedRealRule1bRootDistance_eq_framePathLength singleBonded
              actual.source.occurrence real
          have walkLength : (rerootWalk unit.1.root unit.1.path steps).length =
              actual.source.occurrence.1.node.rule1bRootDistance := by
            rw [← walkEq]
            exact distance.symm
          rw [retainedContextRuleValue_rule1b_real input.moleculeGraph
            (ruleMajorTreeGraph tree) unit label stepsEq, walkLength]
          rfl
      | inr ring =>
          obtain ⟨distance, ring⟩ := ring
          obtain ⟨atom, current⟩ := cursor_current_exists input actual.source
          have label : (ruleMajorTreeGraph tree).label node =
              ⟨some atom, .ringDuplicate distance⟩ := by
            rw [labelEq, OfficialCIPNode.toDeclarativeLabel, current, ring]
            rfl
          rw [retainedContextRuleValue_rule1b_ring input.moleculeGraph
            (ruleMajorTreeGraph tree) unit label]
          exact (input.retainedRingRule1bRootDistance_eq_stored actual.source.occurrence ring).symm

/-- Priority form of the retained observation readback, for every constitutional rule. -/
theorem retainedContextNodeObservation_eq_armObservation
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (rule : ConstitutionalRule)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? tree node.1 = some actual) :
    retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit rule node =
      priorityValue rule (armObservation rule actual) := by
  rw [retainedContextNodeObservation,
    retainedContextRuleValue_eq_armObservation input singleBonded target unit targetUnit tree
      realizes rootChild rule node actual lookup]

/-- The same observation law for one actual rule-major child arm.  The arm cursor is an arbitrary
executable child of the detected target; the stage and reader are the arm's own. -/
theorem retainedContextArm_nodeObservation
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target cursor : input.LocalizedRerootCursor carrierFuel)
    (child : cursor ∈ input.executableLocalizedRerootChildren target)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (arm : input.RuleMajorContextArm carrierFuel stage read cursor)
    (rule : ConstitutionalRule)
    (node : (ruleMajorTreeGraph arm.tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? arm.tree node.1 = some actual) :
    retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph arm.tree) unit
        rule node =
      priorityValue rule (armObservation rule actual) := by
  have rootChild : arm.tree.source ∈ input.executableLocalizedRerootChildren target := by
    rw [arm.sourceEq]
    exact child
  exact retainedContextNodeObservation_eq_armObservation input singleBonded target unit targetUnit
    arm.tree (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) rootChild rule node actual
    lookup

private theorem retainedCursorUnit_of_ancestorWalk
    {carrierFuel : Nat}
    {target : input.LocalizedRerootCursor carrierFuel}
    {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    {steps : List input.Atom}
    (rootEq : (input.molecularFrameUnit actual.source.occurrence.1).root =
      (input.molecularFrameUnit target.occurrence.1).root)
    (pathEq : (input.molecularFrameUnit actual.source.occurrence.1).path =
      rerootWalk (input.molecularFrameUnit target.occurrence.1).root
        (input.molecularFrameUnit target.occurrence.1).path steps) :
    input.molecularFrameUnit actual.source.occurrence.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩ := by
  have targetRoot : (input.molecularFrameUnit target.occurrence.1).root = unit.1.root :=
    congrArg OccurrenceUnit.root targetUnit
  have targetPath : (input.molecularFrameUnit target.occurrence.1).path = unit.1.path :=
    congrArg OccurrenceUnit.path targetUnit
  have rootField : (input.molecularFrameUnit actual.source.occurrence.1).root = unit.1.root :=
    rootEq.trans targetRoot
  have pathField : (input.molecularFrameUnit actual.source.occurrence.1).path =
      rerootWalk unit.1.root unit.1.path steps := by
    rw [pathEq, targetRoot, targetPath]
  cases frameEq : input.molecularFrameUnit actual.source.occurrence.1 with
  | mk frameRoot framePath =>
      have rootEq' : frameRoot = unit.1.root := by simpa [frameEq] using rootField
      have pathEq' : framePath = rerootWalk unit.1.root unit.1.path steps := by
        simpa [frameEq] using pathField
      simp [rootEq', pathEq']

/-- Label readback from the derived walk.  The decorated label is the molecular reader's value.
Real nodes equal `occurrenceReading`, which is `readContext` and is not `unavailable`.  Every
other simple-bonded carrier node is a ring duplicate: its reading and localized label are
`unavailable`.  This does not claim that every node is available. -/
theorem retainedRealizedTree_label_eq_occurrenceReading
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input
      (input.molecularReader descriptorMap target.occurrence) tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? tree node.1 = some actual) :
    actual.label =
        (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
          node).toLocalizedLabel ∧
      (((ruleMajorTreeGraph tree).label node).provenance = .realAtom ↔
        occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node ≠
          .unavailable) ∧
      (((ruleMajorTreeGraph tree).label node).provenance ≠ .realAtom →
        ∃ distance, actual.source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance ∧
          occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
            node = .unavailable) := by
  obtain ⟨steps, stepsEq, rootEq, pathEq⟩ :=
    input.retainedCursorFrame_eq_ancestorWalk singleBonded target tree realizes rootChild node
      actual lookup
  have cursorUnit := retainedCursorUnit_of_ancestorWalk input unit targetUnit rootEq pathEq
  have labelRead := subtreeAt?_node_label_eq_read realizes lookup
  have readerEq := input.molecularReader_eq_contextLabel_of_actual_walk descriptorMap
    target.occurrence actual.source unit steps targetUnit cursorUnit
  have labelEq := retainedDeclarativeLabel_eq_source input node lookup
  cases input.carrierOccurrence_provenance_simple_or_ring singleBonded
      actual.source.occurrence with
  | inl real =>
      have graphReal : ((ruleMajorTreeGraph tree).label node).provenance = .realAtom := by
        rw [labelEq, OfficialCIPNode.toDeclarativeLabel, real]
        rfl
      have readingEq : occurrenceReading input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree) node =
          readContext input.moleculeGraph descriptorMap unit steps :=
        occurrenceReading_eq_readContext input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree) graphReal stepsEq
      have available := occurrenceReading_ne_unavailable_of_real_and_ancestorAtoms
        input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) graphReal stepsEq
      exact And.intro
        (by rw [labelRead, readerEq, if_pos real, readingEq])
        (And.intro
          (Iff.intro (fun _ => available) (fun _ => graphReal))
          (fun notReal => absurd graphReal notReal))
  | inr ring =>
      obtain ⟨distance, ring⟩ := ring
      have graphRing : ((ruleMajorTreeGraph tree).label node).provenance =
          .ringDuplicate distance := by
        rw [labelEq, OfficialCIPNode.toDeclarativeLabel, ring]
        rfl
      have notReal : ((ruleMajorTreeGraph tree).label node).provenance ≠ .realAtom := by
        rw [graphRing]
        intro eqReal
        cases eqReal
      have unavailable : occurrenceReading input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree) node = .unavailable := by
        simp [occurrenceReading, graphRing]
      exact And.intro
        (by rw [labelRead, readerEq, if_neg (by rw [ring]; intro eqReal; cases eqReal),
          unavailable])
        (And.intro
          (Iff.intro (fun realProv => absurd realProv notReal) (fun h => absurd unavailable h))
          (fun _ => ⟨distance, ring, unavailable⟩))

/-- Actual child-arm form of the label readback.  The arm reader is the molecular reader at the
detected target. -/
theorem retainedContextArm_label_eq_occurrenceReading
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    {carrierFuel : Nat}
    (target cursor : input.LocalizedRerootCursor carrierFuel)
    (child : cursor ∈ input.executableLocalizedRerootChildren target)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    {stage : LocalizedCumulativeRule45Stage}
    (arm : input.RuleMajorContextArm carrierFuel stage
      (input.molecularReader descriptorMap target.occurrence) cursor)
    (node : (ruleMajorTreeGraph arm.tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : subtreeAt? arm.tree node.1 = some actual) :
    actual.label =
        (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph arm.tree)
          node).toLocalizedLabel ∧
      (((ruleMajorTreeGraph arm.tree).label node).provenance = .realAtom ↔
        occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph arm.tree)
          node ≠ .unavailable) ∧
      (((ruleMajorTreeGraph arm.tree).label node).provenance ≠ .realAtom →
        ∃ distance, actual.source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance ∧
          occurrenceReading input.moleculeGraph descriptorMap unit
            (ruleMajorTreeGraph arm.tree) node = .unavailable) := by
  have rootChild : arm.tree.source ∈ input.executableLocalizedRerootChildren target := by
    rw [arm.sourceEq]
    exact child
  exact retainedRealizedTree_label_eq_occurrenceReading input descriptorMap singleBonded target
    unit targetUnit arm.tree (LocalizedRuleMajorSortTrace.realizes_of_trace arm.trace) rootChild
    node actual lookup

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference
open DeclarativeCIP CertifiedLocalizedCIPInput TetraStereo.OneCenter.Rule4aTableBridge

/-- At carrier fuel, the derived label is also the generated dependency reader.  Real detected
cursors read `referenceState`; ring duplicates and real non-centers are `none` on that reader.
The chemical reading law remains the general theorem above. -/
theorem retainedGeneratedReader_label_eq_dependency
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor (carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified (carrierFuel input))
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (input.certified.molecularReader (descriptorMap input) target.occurrence) tree)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target)
    (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input.certified (carrierFuel input))
    (lookup : subtreeAt? tree node.1 = some actual) :
    actual.label =
      input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView (referenceState input) target.occurrence)
        actual.source ∧
      actual.label =
        (occurrenceReading input.certified.moleculeGraph (descriptorMap input) unit
          (ruleMajorTreeGraph tree) node).toLocalizedLabel := by
  have chemical := input.certified.retainedRealizedTree_label_eq_occurrenceReading
    (descriptorMap input) singleBonded target unit targetUnit tree realizes rootChild node
    actual lookup
  have generated := molecularReader_eq_generatedReader_of_simpleBonded input singleBonded
    target.occurrence
  have runtime : actual.label =
      input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView (referenceState input) target.occurrence)
        actual.source := by
    rw [subtreeAt?_node_label_eq_read realizes lookup, generated]
  exact ⟨runtime, chemical.1⟩

end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedFramePathLength_eq_officialDepth
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedRealRule1bRootDistance_eq_framePathLength
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedRingRule1bRootDistance_eq_stored
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedExecutableParent_realAtom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedMolecularFrameUnit_eq_rerootWalk_of_realizedPathLabels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedCursorFrame_eq_ancestorWalk
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedContextRuleValue_eq_armObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedContextNodeObservation_eq_armObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedContextArm_nodeObservation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedRealizedTree_label_eq_occurrenceReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.retainedContextArm_label_eq_occurrenceReading
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.retainedGeneratedReader_label_eq_dependency
