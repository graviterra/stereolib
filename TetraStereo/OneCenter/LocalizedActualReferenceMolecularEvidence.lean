import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedPhysicalSparseRootReader
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.OneCenter.AuxiliaryContextIntegrity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false















































namespace TetraStereo
namespace OneCenter

/-! ## The descriptor projection is a section on localized labels -/

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

/-- The existing occurrence-label projection is a section of the localized descriptor projection
on all four localized label variants. -/
theorem localizedAuxiliaryDescriptor_toLocalizedLabel
    (label : LocalizedAuxiliaryLabel) :
    Descriptor.toLocalizedLabel (localizedAuxiliaryDescriptor label) = some label := by
  cases label with
  | chiral descriptor => cases descriptor <;> rfl
  | pseudoasymmetric descriptor => cases descriptor <;> rfl

/-- Reading a mapped optional label back returns the label. -/
theorem option_map_localizedAuxiliaryDescriptor_bind
    (state : Option LocalizedAuxiliaryLabel) :
    (state.map localizedAuxiliaryDescriptor).bind Descriptor.toLocalizedLabel = state := by
  cases state with
  | none => rfl
  | some label => exact localizedAuxiliaryDescriptor_toLocalizedLabel label

/-! ## The actual current atom of a real path node -/

/-- A real physical path node's stored history ends at its stored original root. -/
theorem realPathNode_history_getLast
    (input : CertifiedLocalizedCIPInput) {root : input.Atom} {node : OfficialCIPNode input.Atom}
    (real : input.RealPathNode root node) :
    node.history.getLast? = some root := by
  obtain ⟨current, path, observed, head, provenance, simple, supportReverse, penultimate⟩ := real
  rw [← supportReverse, List.getLast?_reverse]
  cases path with
  | nil => rfl
  | cons adjacent rest => rfl

/-- **The molecular unit atom of a real path is its current physical atom**, including the empty
path (root) case.  The unit path is the reversed history after the root, so its last entry is the
most recent atom of the history, which is the current atom. -/
theorem occurrenceUnit_atom_eq_current_of_history {Atom : Type*} {root current : Atom}
    {history : List Atom}
    (head : history.head? = some current) (last : history.getLast? = some root) :
    OccurrenceUnit.atom ⟨root, history.reverse.tail⟩ = current := by
  cases history with
  | nil => simp at head
  | cons first rest =>
      have firstEq : first = current := by simpa using head
      cases rest with
      | nil =>
          have hlast : some current = some root := by simpa [firstEq] using last
          have rootEq : root = current := by simpa using hlast.symm
          rw [firstEq, rootEq]
          simp [OccurrenceUnit.atom]
      | cons second tail =>
          have hstep : ((first :: second :: tail).reverse.tail).getLast? = some first := by
            rw [List.tail_reverse]
            simp
          show ((first :: second :: tail).reverse.tail).getLast?.getD root = current
          rw [hstep, firstEq]
          simp

/-- The molecular frame unit's atom is the frame's actual `current?` atom. -/
theorem molecularFrameUnit_atom_eq_current
    (input : CertifiedLocalizedCIPInput) (frame : input.LocalizedCIPOccurrenceFrame)
    {current : input.Atom}
    (head : frame.node.history.head? = some current)
    (last : frame.node.history.getLast? = some frame.root) :
    (input.molecularFrameUnit frame).atom = current := by
  show OccurrenceUnit.atom ⟨frame.root, frame.node.history.reverse.tail⟩ = current
  exact occurrenceUnit_atom_eq_current_of_history head last

/-! ## Injectivity of the molecular unit on the actual carrier -/

/-- **The runtime molecular unit injectively codes actual carrier occurrences** on a finite
acyclic single-bond molecule.  Equal units give equal stored roots and equal current atoms; the
existing fixed-root carrier injectivity then gives equal occurrences. -/
theorem molecularFrameUnit_injective_on_carrier
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (left right : input.LocalizedCIPOccurrence fuel)
    (unitEq : input.molecularFrameUnit left.1 = input.molecularFrameUnit right.1) :
    left = right := by
  have rootEq : left.1.root = right.1.root :=
    congrArg OccurrenceUnit.root unitEq
  obtain ⟨currentLeft, _pathLeft, observedLeft, headLeft, _provenanceLeft, _simpleLeft,
    _supportLeft, _penultimateLeft⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic left
  obtain ⟨currentRight, _pathRight, observedRight, headRight, _provenanceRight, _simpleRight,
    _supportRight, _penultimateRight⟩ :=
    input.carrierOccurrence_realPath singleBonded acyclic right
  have lastLeft : left.1.node.history.getLast? = some left.1.root :=
    input.realPathNode_history_getLast
      (input.carrierOccurrence_realPath singleBonded acyclic left)
  have lastRight : right.1.node.history.getLast? = some right.1.root :=
    input.realPathNode_history_getLast
      (input.carrierOccurrence_realPath singleBonded acyclic right)
  have atomLeft : (input.molecularFrameUnit left.1).atom = currentLeft :=
    input.molecularFrameUnit_atom_eq_current left.1 headLeft lastLeft
  have atomRight : (input.molecularFrameUnit right.1).atom = currentRight :=
    input.molecularFrameUnit_atom_eq_current right.1 headRight lastRight
  have currentEq : currentLeft = currentRight := by
    rw [← atomLeft, ← atomRight]
    exact congrArg OccurrenceUnit.atom unitEq
  apply input.localizedCIPOccurrence_current_injective_at_fixedRoot
    singleBonded acyclic left right rootEq
  rw [observedLeft, observedRight, currentEq]

end CertifiedLocalizedCIPInput

/-! ## The map generated by the actual reference state -/

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

/-- The actual carrier occurrence, if any, whose molecular frame unit is the given unit. -/
noncomputable def actualReferenceOccurrenceOf
    (input : LocalizedUniversalReference.Input)
    (unit : OccurrenceUnit input.certified.Atom) :
    Option (LocalizedUniversalReference.Occurrence input) :=
  if h : ∃ occurrence : LocalizedUniversalReference.Occurrence input,
      input.certified.molecularFrameUnit occurrence.1 = unit then
    some (Classical.choose h)
  else none

/-- **The actual molecular descriptor map.**  A detected unit is assigned the descriptor of the
generated reference state at the actual carrier occurrence carrying that unit; when no carrier
occurrence carries the unit the map returns `none`.  The map uses no caller data beyond the
runtime input. -/
noncomputable def actualReferenceDescriptorMap (input : LocalizedUniversalReference.Input) :
    DescriptorMap (DetectedOccurrence input.certified.moleculeGraph) :=
  fun unit =>
    (actualReferenceOccurrenceOf input unit.1).bind fun occurrence =>
      (LocalizedUniversalReference.referenceState input occurrence).map
        localizedAuxiliaryDescriptor

/-- **Characterization of the chosen occurrence.**  On the finite acyclic single-bond domain the
map returns `some occurrence` exactly at the carrier occurrences carrying the unit. -/
theorem actualReferenceOccurrenceOf_eq_some_iff
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (unit : OccurrenceUnit input.certified.Atom)
    (occurrence : LocalizedUniversalReference.Occurrence input) :
    actualReferenceOccurrenceOf input unit = some occurrence ↔
      input.certified.molecularFrameUnit occurrence.1 = unit := by
  constructor
  · intro hsome
    unfold actualReferenceOccurrenceOf at hsome
    split at hsome
    · rename_i hex
      have hval : Classical.choose hex = occurrence := Option.some.inj hsome
      rw [← hval]
      exact Classical.choose_spec hex
    · simp at hsome
  · intro hunit
    have hex : ∃ occurrence : LocalizedUniversalReference.Occurrence input,
        input.certified.molecularFrameUnit occurrence.1 = unit := ⟨occurrence, hunit⟩
    have hchoose : Classical.choose hex = occurrence :=
      molecularFrameUnit_injective_on_carrier input.certified singleBonded acyclic
        (Classical.choose hex) occurrence (by rw [Classical.choose_spec hex, hunit])
    unfold actualReferenceOccurrenceOf
    rw [dif_pos hex, hchoose]

/-- **Exact map readback at every actual detected occurrence.**  If the actual occurrence carries
the detected unit, then reading the constructed map at that unit returns exactly the generated
reference state at the occurrence. -/
theorem actualReferenceDescriptorMap_readback
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (occurrence : LocalizedUniversalReference.Occurrence input)
    (unitEq : input.certified.molecularFrameUnit occurrence.1 = unit.1) :
    (actualReferenceDescriptorMap input unit).bind Descriptor.toLocalizedLabel =
      LocalizedUniversalReference.referenceState input occurrence := by
  have hsome : actualReferenceOccurrenceOf input unit.1 = some occurrence :=
    (actualReferenceOccurrenceOf_eq_some_iff input singleBonded acyclic unit.1 occurrence).mpr unitEq
  unfold actualReferenceDescriptorMap
  rw [hsome]
  exact option_map_localizedAuxiliaryDescriptor_bind _

/-- **The constructed map's reader is the actual production reader**, pointwise on the whole
carrier.  At a real detected occurrence the reader returns exactly the generated reference state
there; at a real non-detected occurrence the generated state is `none` by the actual physical
noncandidate theorem (under the explicit no-double-source-records hypothesis); duplicate and
placeholder occurrences do not exist on the acyclic single-bond carrier. -/
theorem actualReference_molecularReader
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1)) :
    input.certified.molecularReader (actualReferenceDescriptorMap input) target =
      input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) := by
  funext cursor
  unfold CertifiedLocalizedCIPInput.molecularReader
  by_cases dependency : input.certified.LocalizedDepthDependency cursor.occurrence target
  · unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
    simp only [CertifiedLocalizedCIPInput.molecularView,
      CertifiedLocalizedCIPInput.localizedDependencyView]
    simp only [dif_pos dependency]
    by_cases hreal : cursor.occurrence.1.node.provenance = .realAtom
    · rw [if_pos hreal]
      by_cases hcenter : IsDetectedCenter input.certified.moleculeGraph
          (input.certified.molecularFrameUnit cursor.occurrence.1).atom
      · rw [dif_pos hcenter]
        exact actualReferenceDescriptorMap_readback input singleBonded acyclic
          ⟨input.certified.molecularFrameUnit cursor.occurrence.1, hcenter⟩
          cursor.occurrence rfl
      · rw [dif_neg hcenter]
        have hnone : LocalizedUniversalReference.referenceState input cursor.occurrence = none := by
          apply CertifiedLocalizedCIPInput.referenceState_eq_none_of_actualPhysicalNoncandidate
            input noDouble cursor.occurrence
          obtain ⟨current, _path, observed, head, _provenance, _simple, _support,
            _penultimate⟩ :=
            input.certified.carrierOccurrence_realPath singleBonded acyclic cursor.occurrence
          have last : cursor.occurrence.1.node.history.getLast? =
              some cursor.occurrence.1.root :=
            input.certified.realPathNode_history_getLast
              (input.certified.carrierOccurrence_realPath singleBonded acyclic cursor.occurrence)
          have frameAtom : (input.certified.molecularFrameUnit cursor.occurrence.1).atom = current :=
            input.certified.molecularFrameUnit_atom_eq_current cursor.occurrence.1 head last
          refine ⟨current, observed, ?_⟩
          intro hmem
          have htet : input.certified.moleculeGraph.IsTetrahedralCenter current := by
            simpa [CertifiedLocalizedCIPInput.tetrahedralCenterSet] using hmem
          rw [MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card] at htet
          exact hcenter (by rw [frameAtom]; exact htet)
        exact hnone.symm
    · obtain ⟨_current, _path, _observed, _head, provenance, _simple, _support,
        _penultimate⟩ :=
        input.certified.carrierOccurrence_realPath singleBonded acyclic cursor.occurrence
      exact absurd provenance hreal
  · unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
    simp only [dif_neg dependency]

/-! ## The actual production endpoints -/

/-- **Whole-tree identification with the actual reference-state reader.**  For the actual
original-root ligand tree built from the generated reference state itself, at every stage, every
node of its declarative digraph at every depth is an actual decorated node, and its actual label
is the localized label of the molecular evidence's reading at that node.  There is no free
descriptor map and no reader-agreement premise: the map is `actualReferenceDescriptorMap` and the
reader is the actual production dependency reader over `referenceState`. -/
theorem actualReference_molecularReader_ligandRoot_observations
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (center : input.certified.TetrahedralCenter) (index : Fin 4)
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (htargetRoot : target.1.root = center.1) (htargetAddress : target.1.address = [])
    (stage : LocalizedCumulativeRule45Stage) :
    ∃ key : input.certified.LocalizedRerootCumulativeRule45Key,
      input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.certified.localizedDependencyLabel target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target))
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some key ∧
        ∃ tree : LocalizedCumulativeDecoratedTree input.certified
            (input.certified.certified.input.molecule.atomCount + 1),
          tree.source = input.certified.localizedLigandRootCursor center index ∧
            LocalizedCumulativeTreeTableMatch stage tree key ∧
              LocalizedCumulativeTreeRealizes input.certified
                (input.certified.localizedDependencyLabel target
                  (input.certified.localizedDependencyView
                    (LocalizedUniversalReference.referenceState input) target))
                tree ∧
                RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph center.1
                  (input.certified.canonicalLigandAtom center index)
                  (toOfficialSourceTree tree).toDeclarativeDigraph ∧
                ∀ node : (toOfficialSourceTree tree).toDeclarativeDigraph.Node,
                    ∃ actual, subtreeAt? tree node.1 = some actual ∧
                      actual.label =
                        (occurrenceReading input.certified.moleculeGraph
                          (actualReferenceDescriptorMap input)
                          (input.certified.topUnit center)
                          (toOfficialSourceTree tree).toDeclarativeDigraph node).toLocalizedLabel := by
  obtain ⟨key, built, tree, source, tables, realizes, faithful, readings⟩ :=
    MolecularEvidenceTree.molecularReader_ligandRoot_observations input.certified
      (actualReferenceDescriptorMap input) center index target htargetRoot htargetAddress stage
  have hreader := actualReference_molecularReader input singleBonded acyclic noDouble target
  rw [hreader] at built
  rw [hreader] at realizes
  exact ⟨key, built, tree, source, tables, realizes, faithful, readings⟩

/-- **Final-occurrence form.**  The target is the distinguished final occurrence of the detected
center: original root, empty address, arbitrary depth. -/
theorem actualReference_molecularReader_finalOccurrence_observations
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (center : input.certified.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage) :
    ∃ key : input.certified.LocalizedRerootCumulativeRule45Key,
      input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
          (input.certified.localizedDependencyLabel
            (input.certified.localizedFinalOccurrence
              (input.certified.certified.input.molecule.atomCount + 1) center)
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input)
              (input.certified.localizedFinalOccurrence
                (input.certified.certified.input.molecule.atomCount + 1) center)))
          (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
          (input.certified.localizedLigandRootCursor center index) = some key ∧
        ∃ tree : LocalizedCumulativeDecoratedTree input.certified
            (input.certified.certified.input.molecule.atomCount + 1),
          tree.source = input.certified.localizedLigandRootCursor center index ∧
            LocalizedCumulativeTreeTableMatch stage tree key ∧
              LocalizedCumulativeTreeRealizes input.certified
                (input.certified.localizedDependencyLabel
                  (input.certified.localizedFinalOccurrence
                    (input.certified.certified.input.molecule.atomCount + 1) center)
                  (input.certified.localizedDependencyView
                    (LocalizedUniversalReference.referenceState input)
                    (input.certified.localizedFinalOccurrence
                      (input.certified.certified.input.molecule.atomCount + 1) center)))
                tree ∧
                RootedDigraph.FaithfulExactExpansion input.certified.moleculeGraph center.1
                  (input.certified.canonicalLigandAtom center index)
                  (toOfficialSourceTree tree).toDeclarativeDigraph ∧
                ∀ node : (toOfficialSourceTree tree).toDeclarativeDigraph.Node,
                    ∃ actual, subtreeAt? tree node.1 = some actual ∧
                      actual.label =
                        (occurrenceReading input.certified.moleculeGraph
                          (actualReferenceDescriptorMap input)
                          (input.certified.topUnit center)
                          (toOfficialSourceTree tree).toDeclarativeDigraph node).toLocalizedLabel := by
  refine actualReference_molecularReader_ligandRoot_observations input singleBonded acyclic
    noDouble center index
    (input.certified.localizedFinalOccurrence
      (input.certified.certified.input.molecule.atomCount + 1) center) ?_ ?_ stage
  · exact AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified _ center
  · exact AuxiliaryContextIntegrity.localizedFinalOccurrence_address input.certified _ center

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedAuxiliaryDescriptor_toLocalizedLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.option_map_localizedAuxiliaryDescriptor_bind
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_history_getLast
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceUnit_atom_eq_current_of_history
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_atom_eq_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_injective_on_carrier
assert_kernel_only TetraStereo.OneCenter.actualReferenceOccurrenceOf
assert_kernel_only TetraStereo.OneCenter.actualReferenceDescriptorMap
assert_kernel_only TetraStereo.OneCenter.actualReferenceOccurrenceOf_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.actualReferenceDescriptorMap_readback
assert_kernel_only TetraStereo.OneCenter.actualReference_molecularReader
assert_kernel_only TetraStereo.OneCenter.actualReference_molecularReader_ligandRoot_observations
assert_kernel_only TetraStereo.OneCenter.actualReference_molecularReader_finalOccurrence_observations

end OneCenter
end TetraStereo
