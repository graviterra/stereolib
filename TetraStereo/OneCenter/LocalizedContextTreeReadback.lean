import TetraStereo.OneCenter.LocalizedRerootContextPath
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open MolecularEvidenceTree
open LocalizedCumulativeDecoratedTree

variable (input : CertifiedLocalizedCIPInput)

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
  obtain ⟨atom, observed⟩ := Option.isSome_iff_exists.mp
    (input.declarativeLocalizedOccurrence_node_current_isSome derived)
  exact ⟨atom, observed⟩

/-- The path in a realized decorated tree follows actual reroot steps.  The root tree source is
an executable child of `target`; the node's path labels are the atom labels read at every prefix.
The induction uses the realized sibling permutation to recover the executable child relation. -/
theorem molecularFrameUnit_eq_rerootWalk_of_realizedPathLabels
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
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
  induction address generalizing target tree actual rootAtom steps realizes rootChild rootCurrent with
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
      have step := input.molecularFrameUnit_executableChild_rerootStep
        singleBonded acyclic target tree.source rootCurrent rootChild
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
          obtain ⟨tailSteps, stepsEq, tailLabels⟩ :=
            pathLabels_cons_extract labels'
          have childCurrentSome := input.declarativeLocalizedOccurrence_node_current_isSome
            ((input.mem_localizedOccurrences_iff carrierFuel child.source.occurrence.1).mp
              child.source.occurrence.2)
          obtain ⟨childRootAtom, childRootCurrent⟩ :=
            Option.isSome_iff_exists.mp childCurrentSome
          have childRealizes := realizes_of_child realizes childLookup
          have childExec := mem_executable_of_child realizes childLookup
          have ihResult := ih (target := source) (tree := child) (actual := actual)
            (realizes := childRealizes) (rootChild := childExec) (lookup := restLookup)
            (rootCurrent := childRootCurrent) (steps := tailSteps) (labels := tailLabels)
          have rootStep := input.molecularFrameUnit_executableChild_rerootStep
            singleBonded acyclic target source rootCurrent rootChild
          constructor
          · exact ihResult.1.trans rootStep.1
          · calc
              (input.molecularFrameUnit actual.source.occurrence.1).path =
                  rerootWalk (input.molecularFrameUnit source.occurrence.1).root
                    (input.molecularFrameUnit source.occurrence.1).path tailSteps := ihResult.2
              _ = rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                    (rerootStep (input.molecularFrameUnit target.occurrence.1).root
                      (input.molecularFrameUnit target.occurrence.1).path rootAtom) tailSteps := by
                    rw [rootStep.1, rootStep.2]
              _ = rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                    (input.molecularFrameUnit target.occurrence.1).path
                    (rootAtom :: tailSteps) := by
                    change rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                        (rerootStep (input.molecularFrameUnit target.occurrence.1).root
                          (input.molecularFrameUnit target.occurrence.1).path rootAtom) tailSteps =
                      rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                        (input.molecularFrameUnit target.occurrence.1).path ([rootAtom] ++ tailSteps)
                    rw [rerootWalk_append (input.molecularFrameUnit target.occurrence.1).root
                      (input.molecularFrameUnit target.occurrence.1).path [rootAtom] tailSteps]
                    simp [rerootWalk]
              _ = rerootWalk (input.molecularFrameUnit target.occurrence.1).root
                    (input.molecularFrameUnit target.occurrence.1).path steps := by
                    rw [stepsEq]

private theorem pathLabels_exists_some_of_realizedSubtree
    {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {address : List Nat} {actual : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree address = some actual) :
    ∃ steps : List input.Atom, MolecularEvidenceTree.pathLabels (toOfficialSourceTree tree) address =
      steps.map some := by
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

/-- The path-label equation yields the independent ancestor-atom sequence used by
`occurrenceReading`. -/
theorem ancestorAtoms_eq_some_of_pathLabels
    (sourceTree : OfficialCIPSourceTree input.Atom)
    (node : sourceTree.toDeclarativeDigraph.Node)
    {steps : List input.Atom}
    (labels : MolecularEvidenceTree.pathLabels sourceTree node.1 = steps.map some) :
    ancestorAtoms sourceTree.toDeclarativeDigraph node = some steps := by
  rw [ancestorAtoms, MolecularEvidenceTree.ancestorPath_toDeclarativeDigraph, labels]
  exact MolecularEvidenceTree.mapM_id_map_some steps

/-- A real node with an atom ancestor path is always an available occurrence reading.  Lack of a
dependent descriptor is represented by `outsideInventory` or `unassigned`, never `unavailable`. -/
theorem occurrenceReading_ne_unavailable_of_real_and_ancestorAtoms
    {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
    {node : graph.Node} {steps : List Atom}
    (real : (graph.label node).provenance = .realAtom)
    (path : ancestorAtoms graph node = some steps) :
    occurrenceReading molecule descriptorMap unit graph node ≠ .unavailable := by
  rw [occurrenceReading_eq_readContext molecule descriptorMap unit graph real path]
  unfold readContext
  cases contextOccurrence molecule unit steps with
  | none => simp
  | some source =>
      cases hmap : descriptorMap source with
      | none => simp [hmap]
      | some value => simp [hmap]

/-- Every label in a realized source tree is exactly the independent occurrence reading at its
actual target unit.  The target can have any existing molecular path, and no walk or reader
correspondence is supplied: both follow from the realized source tree and its executable root
child. -/
theorem realizedTree_node_label_eq_occurrenceReading
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input
      (input.molecularReader descriptorMap target.occurrence) tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (node : ((toOfficialSourceTree tree).toDeclarativeDigraph).Node) :
    ∃ actual, subtreeAt? tree node.1 = some actual ∧
      actual.label =
        (occurrenceReading input.moleculeGraph descriptorMap unit
          ((toOfficialSourceTree tree).toDeclarativeDigraph) node).toLocalizedLabel ∧
      occurrenceReading input.moleculeGraph descriptorMap unit
        ((toOfficialSourceTree tree).toDeclarativeDigraph) node ≠ .unavailable := by
  let sourceTree := toOfficialSourceTree tree
  obtain ⟨erased, herased⟩ :=
    sourceTree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses node.1 node.2
  rw [toOfficialSourceTree_subtreeAt?_eq, Option.map_eq_some_iff] at herased
  obtain ⟨actual, hactual, rfl⟩ := herased
  have hlookup : sourceTree.subtreeAt? node.1 = some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, hactual]
    rfl
  have hlabel := sourceTree.declarativeLabel_eq_of_subtreeAt? _ node hlookup
  have hprovenance : (sourceTree.toDeclarativeDigraph.label node).provenance =
      (toOfficialSourceTree actual).source.provenance.toDeclarative := by
    change (sourceTree.declarativeLabel node).provenance = _
    rw [hlabel]
    rfl
  have actualReal : actual.source.occurrence.1.node.provenance = .realAtom :=
    input.carrierOccurrence_provenance_real singleBonded acyclic actual.source.occurrence
  have graphReal : (sourceTree.toDeclarativeDigraph.label node).provenance = .realAtom := by
    rw [hprovenance, toOfficialSourceTree_source, actualReal]
    rfl
  obtain ⟨steps, stepsEq⟩ :=
    pathLabels_exists_some_of_realizedSubtree input hactual
  have hsteps : ancestorAtoms (sourceTree.toDeclarativeDigraph) node = some steps := by
    exact ancestorAtoms_eq_some_of_pathLabels input sourceTree node stepsEq
  obtain ⟨rootAtom, rootCurrent⟩ := cursor_current_exists input tree.source
  obtain ⟨rootEq, pathEq⟩ := input.molecularFrameUnit_eq_rerootWalk_of_realizedPathLabels
    singleBonded acyclic (input.molecularReader descriptorMap target.occurrence)
    realizes rootChild hactual rootCurrent stepsEq
  have cursorUnit : input.molecularFrameUnit actual.source.occurrence.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩ := by
    rw [← targetUnit]
    cases actualFrame : input.molecularFrameUnit actual.source.occurrence.1 with
    | mk actualRoot actualPath =>
      cases targetFrame : input.molecularFrameUnit target.occurrence.1 with
      | mk targetRoot targetPath =>
        have rootEq' : actualRoot = targetRoot := by
          simpa [actualFrame, targetFrame] using rootEq
        have pathEq' : actualPath = rerootWalk targetRoot targetPath steps := by
          simpa [actualFrame, targetFrame] using pathEq
        subst actualRoot
        subst actualPath
        rfl
  have hreading : occurrenceReading input.moleculeGraph descriptorMap unit
      (sourceTree.toDeclarativeDigraph) node =
        readContext input.moleculeGraph descriptorMap unit steps :=
    occurrenceReading_eq_readContext input.moleculeGraph descriptorMap unit
      (sourceTree.toDeclarativeDigraph) graphReal hsteps
  refine ⟨actual, hactual, ?_, ?_⟩
  rw [subtreeAt?_node_label_eq_read realizes hactual, hreading]
  · exact input.molecularReader_eq_readContext_of_actual_walk descriptorMap singleBonded acyclic
      target.occurrence actual.source unit steps targetUnit cursorUnit
  · exact occurrenceReading_ne_unavailable_of_real_and_ancestorAtoms
      input.moleculeGraph descriptorMap unit (sourceTree.toDeclarativeDigraph) graphReal hsteps

/-- The rule-major arm interface is the production specialization of the general realized-tree
readback theorem. -/
theorem ruleMajorArm_node_label_eq_occurrenceReading
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (target : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (arm : input.RuleMajorRootArm center index stage
      (input.molecularReader descriptorMap target.occurrence))
    (rootChild : arm.tree.source ∈ input.executableLocalizedRerootChildren target)
    (node : ((toOfficialSourceTree arm.tree).toDeclarativeDigraph).Node) :
    ∃ actual, subtreeAt? arm.tree node.1 = some actual ∧
      actual.label =
        (occurrenceReading input.moleculeGraph descriptorMap unit
          ((toOfficialSourceTree arm.tree).toDeclarativeDigraph) node).toLocalizedLabel ∧
      occurrenceReading input.moleculeGraph descriptorMap
        unit ((toOfficialSourceTree arm.tree).toDeclarativeDigraph) node ≠ .unavailable := by
  exact realizedTree_node_label_eq_occurrenceReading input descriptorMap singleBonded acyclic
    target unit targetUnit arm.tree arm.realizes rootChild node

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_eq_rerootWalk_of_realizedPathLabels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ancestorAtoms_eq_some_of_pathLabels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceReading_ne_unavailable_of_real_and_ancestorAtoms
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realizedTree_node_label_eq_occurrenceReading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorArm_node_label_eq_occurrenceReading
