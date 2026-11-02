import TetraStereo.OneCenter.LocalizedPhysicalNearestRule4bReference
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.OneCenter.LocalizedActualReaderPhysicalBranchInverse
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

noncomputable section







































/-! ## Upper-case descriptors of auxiliary labels -/

/-- The upper-case chiral descriptor carried by an auxiliary label, if any. -/
def chiralDescriptorOfLabel : Option LocalizedAuxiliaryLabel → Option RS
  | some (.chiral descriptor) => some descriptor
  | _ => none

/-- A label reads back as an upper-case chiral descriptor exactly when it *is* that label. -/
theorem chiralDescriptorOfLabel_eq_some_iff (label : Option LocalizedAuxiliaryLabel)
    (descriptor : RS) :
    chiralDescriptorOfLabel label = some descriptor ↔ label = some (.chiral descriptor) := by
  cases label with
  | none => simp [chiralDescriptorOfLabel]
  | some label =>
      cases label with
      | chiral other =>
          simp only [chiralDescriptorOfLabel, Option.some.injEq,
            LocalizedTetrahedralRSPseudoDescriptor.chiral.injEq]
      | pseudoasymmetric other => simp [chiralDescriptorOfLabel]

/-- A label reads back as no upper-case chiral descriptor exactly when it is not chiral. -/
theorem chiralDescriptorOfLabel_eq_none_iff (label : Option LocalizedAuxiliaryLabel) :
    chiralDescriptorOfLabel label = none ↔
      ∀ descriptor : RS, label ≠ some (.chiral descriptor) := by
  constructor
  · intro readNone descriptor same
    subst same
    simp [chiralDescriptorOfLabel] at readNone
  · intro notChiral
    cases label with
    | none => rfl
    | some label =>
        cases label with
        | chiral descriptor => exact absurd rfl (notChiral descriptor)
        | pseudoasymmetric descriptor => rfl

/-! ## The physical cut branch and the physical mark -/

/-- The rooted cut branch of a final root at a physical attachment atom. -/
def ActualSlotCut (input : LocalizedUniversalReference.Input)
    (root attachment : input.certified.Atom) : Set input.certified.Atom :=
  AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph root attachment

/-- **The physical mark.**  An atom is physically marked when it is not the root, is an
automatically detected degree-four candidate, and is not a physical terminal twin centre.  The
value attached to a marked atom is supplied separately, from the actual reference state at its
unique actual occurrence in the cut branch. -/
def PhysicalMarkedAtom (input : LocalizedUniversalReference.Input)
    (root : input.certified.TetrahedralCenter) (atom : input.certified.Atom) : Prop :=
  atom ≠ root.1 ∧
    ∃ candidate : atom ∈ input.certified.tetrahedralCenterSet,
      ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨atom, candidate⟩

/-! ## The actual generated dependency view -/

/-- The production restricted dependency view of the final reference state at the final occurrence
of the detected center. -/
noncomputable def referenceDependencyView (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    input.certified.LocalizedDependencyView (ActualReaderPhysicalBranchInverse.topTarget input c) :=
  input.certified.localizedDependencyView
    (LocalizedUniversalReference.referenceState input)
    (ActualReaderPhysicalBranchInverse.topTarget input c)

/-! ## Root preservation of actual positions -/

/-- Every actual child step of a realized tree keeps the occurrence root of its source. -/
private theorem branch_child_source_root_eq_of_realizes
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    child.source.occurrence.1.root = tree.source.occurrence.1.root := by
  have edge := mem_executable_of_child realizes lookup
  have derived := input.executableLocalizedRerootChildren_declarative tree.source
  have childIntended : child.source.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames tree.source := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child.source, edge, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    tree.source child.source.occurrence.1 childIntended
  exact ((input.mem_localizedRerootNeighborFrames_iff tree.source.occurrence.1
    child.source.occurrence.1).mp neighbor).2.1

/-- Every actual subtree step of a realized tree keeps the occurrence root of its source. -/
private theorem subtreeAt?_source_root_eq_of_realizes
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    ∀ (path : List Nat) (node : LocalizedCumulativeDecoratedTree input carrierFuel),
      subtreeAt? tree path = some node →
        node.source.occurrence.1.root = tree.source.occurrence.1.root
  | [], node, lookup => by
      rw [subtreeAt?_nil] at lookup
      cases lookup
      rfl
  | slot :: rest, node, lookup => by
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact (subtreeAt?_source_root_eq_of_realizes child (realizes_of_child realizes childLookup)
        rest node restLookup).trans
        (branch_child_source_root_eq_of_realizes realizes childLookup)

/-- Every actual position source keeps the occurrence root of the tree source. -/
theorem positionSource_root_eq_of_realized
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionSource p).occurrence.1.root = tree.source.occurrence.1.root :=
  subtreeAt?_source_root_eq_of_realizes tree realizes p.val (positionNode p)
    (positionNode_spec p)

/-! ## The actual production slot key and its decorated tree -/

/-- The declarative content of the actually computed four-ligand frame. -/
noncomputable def actualSlotDerived (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame) :
    input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame :=
  (input.certified.localizedOccurrenceFourLigandFrame?_eq_some_iff
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame).mp frameComputed

/-- The actual production compound Rules-4a--5 key of one frame slot of the final occurrence. -/
noncomputable def actualSlotCompoundKey (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) : input.certified.LocalizedRerootCompoundRule45Key :=
  frame.compoundKeyAt input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (referenceDependencyView input c) (actualSlotDerived input c frame frameComputed) slot



theorem actualSlotCompoundBuilt (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    input.certified.buildLocalizedRerootCompoundRule45Key?
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        ((frame.cursorAt slot)) =
      some (actualSlotCompoundKey input c frame frameComputed slot) :=
  frame.compoundKeyAt_built input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (referenceDependencyView input c) (actualSlotDerived input c frame frameComputed) slot

/-- The actual production Rules-4b/4c prior of the slot is the production compound build. -/
theorem actualSlotPriorBuilt (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    input.certified.buildLocalizedRerootCompoundRule4bcKey?
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        ((frame.cursorAt slot)) =
      some (actualSlotCompoundKey input c frame frameComputed slot).prior :=
  (buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (referenceDependencyView input c)
    (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
    (frame.cursorAt slot)
    (actualSlotCompoundKey input c frame frameComputed slot)
    (actualSlotCompoundBuilt input c frame frameComputed slot)).1

/-- The actual production Rule-4a key of the slot is the actual production cumulative build. -/
theorem actualSlotRule4aBuilt (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    input.certified.buildLocalizedRerootCumulativeRule45Key?
        .rule4a
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        ((frame.cursorAt slot)) =
      some (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey :=
  input.certified.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (referenceDependencyView input c) _ ((frame.cursorAt slot))
    (actualSlotCompoundKey input c frame frameComputed slot).prior
    (actualSlotPriorBuilt input c frame frameComputed slot)

/-- The actual decorated occurrence tree of the Rule-4a build at this slot exists, with its
source, its exact label table, and its realization of the generated restricted dependency reader. -/
noncomputable def actualSlotTreeExists (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    ∃ tree : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input),
      tree.source = frame.cursorAt slot ∧
        tree.labelTable =
          (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.labels ∧
          LocalizedCumulativeTreeRealizes input.certified
            (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree := by
  obtain ⟨tree, treeSource, _tableMatch, labelTableEq, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key?
      input.certified .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      ((frame.cursorAt slot))
      (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey
      (actualSlotRule4aBuilt input c frame frameComputed slot)
  exact ⟨tree, treeSource, labelTableEq, realizes⟩

/-- **The actual decorated occurrence tree of the slot.**  A fixed choice among the actual
production builder outputs at the fixed cursor `frame.cursorAt slot`; it is never quantified over
all possible source roots. -/
noncomputable def actualSlotTree (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input) :=
  Classical.choose (actualSlotTreeExists input c frame frameComputed slot)

/-- The source of the actual slot tree is the actual frame cursor. -/
theorem actualSlotTree_source (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    (actualSlotTree input c frame frameComputed slot).source = frame.cursorAt slot :=
  (Classical.choose_spec (actualSlotTreeExists input c frame frameComputed slot)).1

/-- The label table of the actual slot tree is the actual production Rule-4a label table. -/
theorem actualSlotTree_labelTable (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    (actualSlotTree input c frame frameComputed slot).labelTable =
      (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.labels :=
  (Classical.choose_spec (actualSlotTreeExists input c frame frameComputed slot)).2.1

/-- The actual slot tree realizes the actual generated restricted dependency reader. -/
theorem actualSlotTree_realizes (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (actualSlotTree input c frame frameComputed slot) :=
  (Classical.choose_spec (actualSlotTreeExists input c frame frameComputed slot)).2.2

/-- The actual slot tree records the final target as its incoming coordinate. -/
theorem actualSlotTree_previousEq (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    (actualSlotTree input c frame frameComputed slot).source.previous? =
      some (ActualReaderPhysicalBranchInverse.topTarget input c) := by
  rw [actualSlotTree_source]
  exact input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (frame.cursorAt slot) (List.get_mem frame.cursors _)

/-- The actual slot tree's source cursor is valid. -/
theorem actualSlotTree_valid (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    input.certified.LocalizedRerootCursorValid
      (actualSlotTree input c frame frameComputed slot).source := by
  rw [actualSlotTree_source]
  exact input.certified.localizedOccurrenceFourLigandFrame_cursor_valid
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (frame.cursorAt slot) (List.get_mem frame.cursors _)

/-- The actual slot tree's source keeps the final target's occurrence root. -/
theorem actualSlotTree_sameRoot (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    (actualSlotTree input c frame frameComputed slot).source.occurrence.1.root =
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.root := by
  rw [actualSlotTree_source]
  exact input.certified.localizedOccurrenceFourLigandFrame_cursor_root
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (frame.cursorAt slot) (List.get_mem frame.cursors _)

/-- The actual slot tree's source observes the slot's ligand atom. -/
theorem actualSlotTree_oObserved (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom) :
    (actualSlotTree input c frame frameComputed slot).source.occurrence.1.node.current? =
      some oAtom := by
  rw [actualSlotTree_source]
  exact oObserved

/-- Every actual frame slot of the final occurrence is strictly outward of the final target. -/
theorem actualSlot_cursor_previousShorter (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    (ActualReaderPhysicalBranchInverse.topTarget input c).1.address.length <
      (frame.cursorAt slot).occurrence.1.address.length :=
  ActualReaderPhysicalBranchInverse.frame_cursor_strictlyDeeper_of_target_address_nil
    input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (ActualReaderPhysicalBranchInverse.topTarget_address input c)
    (frame.cursorAt slot) (List.get_mem frame.cursors _)

/-- The actual slot tree's source is strictly deeper than the final target. -/
theorem actualSlotTree_previousShorter (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) :
    (ActualReaderPhysicalBranchInverse.topTarget input c).1.address.length <
      (actualSlotTree input c frame frameComputed slot).source.occurrence.1.address.length := by
  rw [actualSlotTree_source]
  exact actualSlot_cursor_previousShorter input c frame frameComputed slot

/-- The final root is physically adjacent to the ligand atom observed by any actual frame slot.
This is derived from the actual carrier neighbor classification of the frame cursor, not assumed. -/
theorem actualSlot_incomingEdge (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4) {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom) :
    input.certified.moleculeGraph.Adj c.1 oAtom := by
  have present : frame.cursorAt slot ∈ frame.cursors := List.get_mem frame.cursors _
  have neighbor := input.certified.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (frame.cursorAt slot) present
  obtain ⟨_carrier, _sameRoot, classified⟩ :=
    (input.certified.mem_localizedRerootNeighborFrames_iff
      (ActualReaderPhysicalBranchInverse.topTarget input c).1
      (frame.cursorAt slot).occurrence.1).mp neighbor
  have childCase : (ActualReaderPhysicalBranchInverse.topTarget input c).1.address.length + 1 =
      (frame.cursorAt slot).occurrence.1.address.length ∧
        (ActualReaderPhysicalBranchInverse.topTarget input c).1.address =
          (frame.cursorAt slot).occurrence.1.address.dropLast := by
    rcases classified with parentCase | childCase
    · obtain ⟨lengthEq, _⟩ := parentCase
      rw [ActualReaderPhysicalBranchInverse.topTarget_address] at lengthEq
      simp at lengthEq
    · exact childCase
  obtain ⟨lengthEq, _dropLast⟩ := childCase
  have lengthOne : (frame.cursorAt slot).occurrence.1.address.length = 1 := by
    simpa [ActualReaderPhysicalBranchInverse.topTarget_address] using lengthEq.symm
  obtain ⟨last, addressEq⟩ := List.length_eq_one_iff.mp lengthOne
  have addressForm : (frame.cursorAt slot).occurrence.1.address =
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.address ++ [last] := by
    rw [addressEq, ActualReaderPhysicalBranchInverse.topTarget_address]
    rfl
  exact input.certified.outwardChildFrame_current_adjacent
    (ActualReaderPhysicalBranchInverse.topTarget_current input c)
    (frame.cursorAt slot).occurrence.1 neighbor last addressForm oObserved

/-! ## The cut-branch value of the actual mark -/

/-- The actual position/cut-branch equivalence at a slot of the final occurrence. -/
noncomputable def actualSlotCutEquiv (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom) :
    Position (actualSlotTree input c frame frameComputed slot) ≃
      AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom :=
  positionCutEquiv (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
    singleBonded acyclic (globalCarrierFuel_adequate input)
    (actualSlotTree_realizes input c frame frameComputed slot)
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualSlotTree_previousEq input c frame frameComputed slot)
    (actualSlotTree_valid input c frame frameComputed slot)
    (actualSlotTree_sameRoot input c frame frameComputed slot)
    (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
    (ActualReaderPhysicalBranchInverse.topTarget_current input c)
    (actualSlot_incomingEdge input c frame frameComputed slot oObserved)

/-- The atom of the position recovered from an actual cut-branch atom is that atom. -/
theorem actualSlotCutEquiv_symm_apply (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {a : input.certified.Atom}
    (mem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom) :
    positionAtom singleBonded acyclic
      ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved).symm ⟨a, mem⟩) = a :=
  positionAtom_positionCutEquiv_symm (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
    singleBonded acyclic (globalCarrierFuel_adequate input)
    (actualSlotTree_realizes input c frame frameComputed slot)
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualSlotTree_previousEq input c frame frameComputed slot)
    (actualSlotTree_valid input c frame frameComputed slot)
    (actualSlotTree_sameRoot input c frame frameComputed slot)
    (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
    (ActualReaderPhysicalBranchInverse.topTarget_current input c)
    (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    ⟨a, mem⟩

/-- The position recovered from an actual cut-branch atom which occurs at position `p` *is* `p`.
Uniqueness is the actual injectivity of `positionAtom`, not an assumed occurrence alignment. -/
theorem actualSlotCutEquiv_symm_positionAtom (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {a : input.certified.Atom}
    (mem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom)
    {p : Position (actualSlotTree input c frame frameComputed slot)}
    (atomEq : positionAtom singleBonded acyclic p = a) :
    (actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved).symm ⟨a, mem⟩ = p := by
  apply positionAtom_injective (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
    singleBonded acyclic (globalCarrierFuel_adequate input)
    (actualSlotTree_realizes input c frame frameComputed slot)
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualSlotTree_previousEq input c frame frameComputed slot)
    (actualSlotTree_sameRoot input c frame frameComputed slot)
    (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
    (ActualReaderPhysicalBranchInverse.topTarget_current input c)
  rw [actualSlotCutEquiv_symm_apply input c frame frameComputed slot singleBonded acyclic
    oAtom oObserved mem, atomEq]

/-- **The actual physical mark on the slot's cut branch.**  A branch atom is marked with the
descriptor that the actual final reference state assigns to its unique actual occurrence; atoms
outside the branch are unmarked. -/
noncomputable def branchMarkedDescriptor (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (atom : input.certified.Atom) : Option RS := by
  classical
  exact if mem : atom ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom then
    chiralDescriptorOfLabel
      (LocalizedUniversalReference.referenceState input
        (positionSource ((actualSlotCutEquiv input c frame frameComputed slot singleBonded
          acyclic oAtom oObserved).symm ⟨atom, mem⟩)).occurrence)
  else none




theorem branchMarkedDescriptor_positionAtom (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (p : Position (actualSlotTree input c frame frameComputed slot)) :
    branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved (positionAtom singleBonded acyclic p) =
      chiralDescriptorOfLabel
        (LocalizedUniversalReference.referenceState input
          (positionSource p).occurrence) := by
  have mem : positionAtom singleBonded acyclic p ∈
      AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom :=
    positionAtom_mem_cutBranch (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
      singleBonded acyclic (globalCarrierFuel_adequate input)
      (actualSlotTree_realizes input c frame frameComputed slot)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualSlotTree_previousEq input c frame frameComputed slot)
      (actualSlotTree_valid input c frame frameComputed slot)
      (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p
  unfold branchMarkedDescriptor
  rw [dif_pos mem]
  rw [actualSlotCutEquiv_symm_positionAtom input c frame frameComputed slot singleBonded
    acyclic oAtom oObserved mem rfl]

/-! ## The actual reader correspondence on the actual slot tree -/

/-- The actual slot tree's labels are the actual whole reference state at actual occurrences. -/
theorem actualSlotTree_positionNode_label_eq_state (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (p : Position (actualSlotTree input c frame frameComputed slot)) :
    (positionNode p).label =
      LocalizedUniversalReference.referenceState input (positionSource p).occurrence :=
  positionNode_label_eq_state_of_outward (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (LocalizedUniversalReference.referenceState input)
    (actualSlotTree_realizes input c frame frameComputed slot)
    (actualSlotTree_valid input c frame frameComputed slot)
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualSlotTree_previousEq input c frame frameComputed slot)
    (actualSlotTree_previousShorter input c frame frameComputed slot)
    rfl p

/-- **The actual reader correspondence on the actual slot tree.**  Reading the label as an
upper-case chiral descriptor is exactly the physical mark of the position's atom. -/
theorem actualSlotTree_reader (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom) :
    ∀ (p : Position (actualSlotTree input c frame frameComputed slot)) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
          oAtom oObserved (positionAtom singleBonded acyclic p) = some descriptor := by
  intro p descriptor
  rw [actualSlotTree_positionNode_label_eq_state input c frame frameComputed slot p,
    branchMarkedDescriptor_positionAtom input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved p, chiralDescriptorOfLabel_eq_some_iff]

/-! ## The actual classification of the reference state on the cut branch

The two theorems below are the only place where the physical domain enters.  They are stated for an
*arbitrary* actual occurrence `target` whose root is the final root and whose current atom is the
branch atom, so they apply to the position occurrences produced by the cut equivalence. -/





theorem referenceState_chiral_iff_physicalMarked (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom a : input.certified.Atom}
    (incomingEdge : input.certified.moleculeGraph.Adj c.1 oAtom)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetRoot : target.1.root = c.1)
    (targetCurrent : target.1.node.current? = some a)
    (aMem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom) :
    (∃ rs : RS, LocalizedUniversalReference.referenceState input target = some (.chiral rs)) ↔
      PhysicalMarkedAtom input ⟨c.1, c.2⟩ a := by
  have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root := by
    rw [targetRoot]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).mp c.2
  have aNe : a ≠ c.1 := AcyclicCutBranchAutomorphism.cutBranch_ne_center
    input.certified.moleculeGraph aMem
  constructor
  · rintro ⟨rs, chiral⟩
    by_cases candidate : a ∈ input.certified.tetrahedralCenterSet
    · refine ⟨aNe, candidate, ?_⟩
      intro twin
      have centerNe : (⟨a, candidate⟩ : input.certified.TetrahedralCenter) ≠ ⟨c.1, c.2⟩ := by
        intro equal
        exact aNe (congrArg Subtype.val equal)
      exact (actualGeneralRigidCandidateCenter_referenceState_chiral_iff_notTwin
        input singleBonded acyclic hcharge noDouble cfg ⟨c.1, c.2⟩ domain
        ⟨a, candidate⟩ centerNe target targetCurrent rootTetrahedral).mp
        ⟨rs, chiral⟩ twin
    · have noncandidate : ActualPhysicalNoncandidate input target :=
        ⟨a, targetCurrent, candidate⟩
      have stateNone := referenceState_eq_none_of_actualPhysicalNoncandidate
        input noDouble target noncandidate
      rw [stateNone] at chiral
      cases chiral
  · rintro ⟨_aNe, candidate, notTwin⟩
    have centerNe : (⟨a, candidate⟩ : input.certified.TetrahedralCenter) ≠ ⟨c.1, c.2⟩ := by
      intro equal
      exact _aNe (congrArg Subtype.val equal)
    exact (actualGeneralRigidCandidateCenter_referenceState_chiral_iff_notTwin
      input singleBonded acyclic hcharge noDouble cfg ⟨c.1, c.2⟩ domain
      ⟨a, candidate⟩ centerNe target targetCurrent rootTetrahedral).mpr notTwin

/-- An unmarked branch atom's actual reference state is not an upper-case chiral descriptor. -/
theorem chiralDescriptorOfLabel_state_eq_none_of_not_physicalMarked
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (incomingEdge : input.certified.moleculeGraph.Adj c.1 oAtom)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetRoot : target.1.root = c.1)
    {a : input.certified.Atom}
    (targetCurrent : target.1.node.current? = some a)
    (aMem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom)
    (notMarked : ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ a) :
    chiralDescriptorOfLabel
      (LocalizedUniversalReference.referenceState input target) = none := by
  rw [chiralDescriptorOfLabel_eq_none_iff]
  intro descriptor chiral
  exact notMarked ((referenceState_chiral_iff_physicalMarked input singleBonded acyclic hcharge
    noDouble cfg c domain incomingEdge target targetRoot targetCurrent aMem).mp
    ⟨descriptor, chiral⟩)

/-- **An unmarked physical branch atom is unmarked by the actual slot mark.** -/
theorem branchMarkedDescriptor_eq_none_of_not_physicalMarked
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {a : input.certified.Atom}
    (aMem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom)
    (notMarked : ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ a) :
    branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved a = none := by
  unfold branchMarkedDescriptor
  rw [dif_pos aMem]
  apply chiralDescriptorOfLabel_state_eq_none_of_not_physicalMarked input singleBonded acyclic
    hcharge noDouble cfg c domain
    (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    (positionSource ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved).symm ⟨a, aMem⟩)).occurrence
  · have rootEq := positionSource_root_eq_of_realized
      (actualSlotTree_realizes input c frame frameComputed slot)
      ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved).symm ⟨a, aMem⟩)
    rw [rootEq, actualSlotTree_source,
      input.certified.localizedOccurrenceFourLigandFrame_cursor_root
        (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
        (frame.cursorAt slot) (List.get_mem frame.cursors _),
      ActualReaderPhysicalBranchInverse.topTarget_root]
  · rw [positionAtom_spec (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      singleBonded acyclic
      ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved).symm ⟨a, aMem⟩),
      actualSlotCutEquiv_symm_apply input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved aMem]
  · exact aMem
  · exact notMarked







/-- The root of the actual occurrence of a cut-branch atom is the final root. -/
theorem actualSlotCutEquiv_symm_root (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {a : input.certified.Atom}
    (aMem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom) :
    (positionSource ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved).symm ⟨a, aMem⟩)).occurrence.1.root = c.1 := by
  have rootEq := positionSource_root_eq_of_realized
    (actualSlotTree_realizes input c frame frameComputed slot)
    ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved).symm ⟨a, aMem⟩)
  rw [rootEq, actualSlotTree_source,
    input.certified.localizedOccurrenceFourLigandFrame_cursor_root
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
      (frame.cursorAt slot) (List.get_mem frame.cursors _),
    ActualReaderPhysicalBranchInverse.topTarget_root]

/-- The current atom of the actual occurrence of a cut-branch atom is that atom. -/
theorem actualSlotCutEquiv_symm_current (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {a : input.certified.Atom}
    (aMem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom) :
    (positionSource ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved).symm ⟨a, aMem⟩)).occurrence.1.node.current? = some a := by
  rw [positionAtom_spec (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      singleBonded acyclic
      ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved).symm ⟨a, aMem⟩),
    actualSlotCutEquiv_symm_apply input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved aMem]

/-- **A read descriptor witnesses the pure physical mark.** -/
theorem physicalMarkedAtom_of_branchMarkedDescriptor_eq_some
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {a : input.certified.Atom}
    (aMem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom)
    {descriptor : RS}
    (marked : branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved a = some descriptor) :
    PhysicalMarkedAtom input ⟨c.1, c.2⟩ a := by
  unfold branchMarkedDescriptor at marked
  rw [dif_pos aMem] at marked
  have state : LocalizedUniversalReference.referenceState input
      (positionSource ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved).symm ⟨a, aMem⟩)).occurrence = some (.chiral descriptor) :=
    (chiralDescriptorOfLabel_eq_some_iff _ descriptor).mp marked
  exact (referenceState_chiral_iff_physicalMarked input singleBonded acyclic hcharge noDouble
    cfg c domain (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    (positionSource ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved).symm ⟨a, aMem⟩)).occurrence
    (actualSlotCutEquiv_symm_root input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved aMem)
    (actualSlotCutEquiv_symm_current input c frame frameComputed slot singleBonded acyclic
      oAtom oObserved aMem) aMem).mp ⟨descriptor, state⟩



theorem exists_branchMarkedDescriptor_eq_some_of_physicalMarked
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {a : input.certified.Atom}
    (aMem : a ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom)
    (marked : PhysicalMarkedAtom input ⟨c.1, c.2⟩ a) :
    ∃ descriptor : RS, branchMarkedDescriptor input c frame frameComputed slot singleBonded
      acyclic oAtom oObserved a = some descriptor := by
  obtain ⟨descriptor, state⟩ :=
    (referenceState_chiral_iff_physicalMarked input singleBonded acyclic hcharge noDouble
      cfg c domain (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      (positionSource ((actualSlotCutEquiv input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved).symm ⟨a, aMem⟩)).occurrence
      (actualSlotCutEquiv_symm_root input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved aMem)
      (actualSlotCutEquiv_symm_current input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved aMem) aMem).mpr marked
  refine ⟨descriptor, ?_⟩
  unfold branchMarkedDescriptor
  rw [dif_pos aMem, state]
  rfl

/-! ## The physical branch domain -/

/-- **Physical unique nearest centre on a cut branch.**  `center` is a marked branch atom at
physical walk distance `distance` from the attachment; no marked branch atom is reached by a
simple walk shorter than `distance`; and every marked branch atom reached at exactly `distance` is
`center`.  `descriptor` is the actual value attached to that nearest centre.  Deeper detected
centres are not constrained. -/
def MarkedBranchUniqueNearest (input : LocalizedUniversalReference.Input)
    (root : input.certified.TetrahedralCenter) (attachment : input.certified.Atom)
    (marked : input.certified.Atom → Option RS)
    (center : input.certified.Atom) (distance : Nat) (descriptor : RS) : Prop :=
  center ∈ ActualSlotCut input root.1 attachment ∧
    marked center = some descriptor ∧
      center ∈ PhysicalSimpleSphere input.certified.moleculeGraph.underlyingSimpleGraph
        attachment distance ∧
        (∀ (y : input.certified.Atom) (r : RS),
          y ∈ ActualSlotCut input root.1 attachment →
            marked y = some r →
              ∀ walk : (input.certified.moleculeGraph.underlyingSimpleGraph).Walk attachment y,
                walk.IsPath → walk.length < distance → False) ∧
          (∀ (y : input.certified.Atom) (r : RS),
            y ∈ ActualSlotCut input root.1 attachment →
              marked y = some r →
                ∀ walk : (input.certified.moleculeGraph.underlyingSimpleGraph).Walk attachment y,
                  walk.IsPath → walk.length = distance → y = center)

/-- **The actual physical branch domain.**  Each physical cut branch either carries no physically
marked atom at all, or carries exactly one uniquely nearest marked centre together with the actual
descriptor attached to it. -/
def MarkedPhysicalBranchDomain (input : LocalizedUniversalReference.Input)
    (root : input.certified.TetrahedralCenter) (attachment : input.certified.Atom)
    (marked : input.certified.Atom → Option RS) : Prop :=
  (∀ y : input.certified.Atom,
      y ∈ ActualSlotCut input root.1 attachment → ¬ PhysicalMarkedAtom input root y) ∨
    ∃ (center : input.certified.Atom) (distance : Nat) (descriptor : RS),
      MarkedBranchUniqueNearest input root attachment marked center distance descriptor








/-- **Pure physical unique nearest centre on a cut branch.**  `center` is a physically marked
branch atom at physical walk distance `distance` from the attachment; no physically marked branch
atom is reached by a simple walk shorter than `distance`; and every physically marked branch atom
reached at exactly `distance` is `center`.  There is no descriptor and no reader parameter.  Deeper
detected centres are unrestricted. -/
def PhysicalBranchUniqueNearest (input : LocalizedUniversalReference.Input)
    (root : input.certified.TetrahedralCenter) (attachment : input.certified.Atom)
    (center : input.certified.Atom) (distance : Nat) : Prop :=
  center ∈ ActualSlotCut input root.1 attachment ∧
    PhysicalMarkedAtom input root center ∧
      center ∈ PhysicalSimpleSphere input.certified.moleculeGraph.underlyingSimpleGraph
        attachment distance ∧
        (∀ y : input.certified.Atom,
          y ∈ ActualSlotCut input root.1 attachment →
            PhysicalMarkedAtom input root y →
              ∀ walk : (input.certified.moleculeGraph.underlyingSimpleGraph).Walk attachment y,
                walk.IsPath → walk.length < distance → False) ∧
          (∀ y : input.certified.Atom,
            y ∈ ActualSlotCut input root.1 attachment →
              PhysicalMarkedAtom input root y →
                ∀ walk : (input.certified.moleculeGraph.underlyingSimpleGraph).Walk attachment y,
                  walk.IsPath → walk.length = distance → y = center)

/-- **The pure physical branch domain.**  Each physical cut branch either carries no physically
marked atom at all, or carries exactly one uniquely nearest physically marked centre.  Neither the
actual reader state nor any descriptor occurs in this predicate. -/
def PhysicalBranchDomain (input : LocalizedUniversalReference.Input)
    (root : input.certified.TetrahedralCenter) (attachment : input.certified.Atom) : Prop :=
  (∀ y : input.certified.Atom,
      y ∈ ActualSlotCut input root.1 attachment → ¬ PhysicalMarkedAtom input root y) ∨
    ∃ (center : input.certified.Atom) (distance : Nat),
      PhysicalBranchUniqueNearest input root attachment center distance




theorem exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ descriptor : RS,
      MarkedBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom
        (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
          oAtom oObserved) center distance descriptor := by
  obtain ⟨centerMem, centerMarked, centerSphere, noEarlier, uniqueAt⟩ := unique
  obtain ⟨descriptor, centerDescriptor⟩ :=
    exists_branchMarkedDescriptor_eq_some_of_physicalMarked input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved centerMem centerMarked
  refine ⟨descriptor, centerMem, centerDescriptor, centerSphere, ?_, ?_⟩
  · intro y r yMem yMarked walk path shorter
    exact noEarlier y yMem
      (physicalMarkedAtom_of_branchMarkedDescriptor_eq_some input c frame frameComputed slot
        singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved yMem yMarked)
      walk path shorter
  · intro y r yMem yMarked walk path exactLen
    exact uniqueAt y yMem
      (physicalMarkedAtom_of_branchMarkedDescriptor_eq_some input c frame frameComputed slot
        singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved yMem yMarked)
      walk path exactLen



theorem markedPhysicalBranchDomain_of_physicalBranchDomain
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (branchDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtom) :
    MarkedPhysicalBranchDomain input ⟨c.1, c.2⟩ oAtom
      (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved) := by
  rcases branchDomain with unmarked | ⟨center, distance, unique⟩
  · exact Or.inl unmarked
  · obtain ⟨descriptor, marked⟩ :=
      exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame frameComputed
        slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved unique
    exact Or.inr ⟨center, distance, descriptor, marked⟩

/-! ## Actual zero-or-one reference selection -/

/-- **Actual singleton selection from an actual physical unique nearest centre.**  The three
conclusions are the actual executable reference list, the actual production `prior` reference
list, and the actual production `readings` shape with the actual descriptor attached to the unique
nearest centre. -/
theorem actualSlot_markedBranchUniqueNearest_references_singleton
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {center : input.certified.Atom} {distance : Nat} {descriptor : RS}
    (unique : MarkedBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom
      (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved) center distance descriptor) :
    localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels =
        [descriptor] ∧
      (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [descriptor] ∧
        ∃ reading : input.certified.LocalizedRerootRule4bcReading,
          (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [reading] ∧
            reading.reference? = some descriptor := by
  let key := actualSlotCompoundKey input c frame frameComputed slot
  have priorBuilt : input.certified.buildLocalizedRerootCompoundRule4bcKey?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      ((frame.cursorAt slot)) = some key.prior :=
    actualSlotPriorBuilt input c frame frameComputed slot
  rcases unique with ⟨centerMember, centerMarked, centerSphere, noEarlier, uniqueAt⟩
  have selection :=
    buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_physicalUniqueNearest
      input.certified
      .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      ((frame.cursorAt slot)) key.prior.rule4aKey
      (actualSlotTree input c frame frameComputed slot)
      (actualSlotTree_labelTable input c frame frameComputed slot)
      (actualSlotRule4aBuilt input c frame frameComputed slot)
      singleBonded acyclic (globalCarrierFuel_adequate input)
      (actualSlotTree_realizes input c frame frameComputed slot)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualSlotTree_previousEq input c frame frameComputed slot)
      (actualSlotTree_valid input c frame frameComputed slot)
      (actualSlotTree_sameRoot input c frame frameComputed slot)
      (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved)
      (actualSlotTree_reader input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved)
      centerMarked centerMember centerSphere noEarlier uniqueAt
  have readings :=
    buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_physicalUniqueNearest
      input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      ((frame.cursorAt slot)) key.prior
      (actualSlotTree input c frame frameComputed slot)
      (actualSlotTree_labelTable input c frame frameComputed slot)
      priorBuilt
      singleBonded acyclic (globalCarrierFuel_adequate input)
      (actualSlotTree_realizes input c frame frameComputed slot)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualSlotTree_previousEq input c frame frameComputed slot)
      (actualSlotTree_valid input c frame frameComputed slot)
      (actualSlotTree_sameRoot input c frame frameComputed slot)
      (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved)
      (actualSlotTree_reader input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved)
      centerMarked centerMember centerSphere noEarlier uniqueAt
  refine ⟨selection, ?_, readings⟩
  rw [input.certified.buildLocalizedRerootCompoundRule4bcKey?_references_eq
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (referenceDependencyView input c) _ ((frame.cursorAt slot)) key.prior priorBuilt]
  exact selection

/-- **Actual empty selection from an actually unmarked physical branch.**  When no cut-branch atom
is physically marked, the actual executable reference list and the actual production `prior`
reference list are empty, and the actual production `readings` is a single no-reference reading. -/
theorem actualSlot_physicalBranchUnmarked_references_nil
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (unmarked : ∀ y : input.certified.Atom,
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ y) :
    localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels = [] ∧
      (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [] ∧
        ∃ reading : input.certified.LocalizedRerootRule4bcReading,
          (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [reading] ∧
            reading.reference? = none := by
  let key := actualSlotCompoundKey input c frame frameComputed slot
  have priorBuilt : input.certified.buildLocalizedRerootCompoundRule4bcKey?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      ((frame.cursorAt slot)) = some key.prior :=
    actualSlotPriorBuilt input c frame frameComputed slot
  have noMarked : ∀ y : input.certified.Atom,
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom →
        branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
          oAtom oObserved y = none := by
    intro y mem
    exact branchMarkedDescriptor_eq_none_of_not_physicalMarked input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved mem (unmarked y mem)
  have free : LocalizedLabelLayersChiralFree key.prior.rule4aKey.labels :=
    labels_chiralFree_of_noPhysicalMarked input.certified
      singleBonded acyclic (globalCarrierFuel_adequate input)
      (actualSlotTree_realizes input c frame frameComputed slot)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualSlotTree_previousEq input c frame frameComputed slot)
      (actualSlotTree_valid input c frame frameComputed slot)
      (actualSlotTree_sameRoot input c frame frameComputed slot)
      (actualSlotTree_oObserved input c frame frameComputed slot oObserved)
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved)
      (actualSlotTree_reader input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved)
      noMarked
      (key := key.prior.rule4aKey)
      (actualSlotTree_labelTable input c frame frameComputed slot)
  have selectionNil : localizedRule4bReferencesFromRankedLabels key.prior.rule4aKey.rankedLabels = [] :=
    (input.certified.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
      .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      ((frame.cursorAt slot)) key.prior.rule4aKey
      (actualSlotRule4aBuilt input c frame frameComputed slot)).mpr free
  have referencesNil : key.prior.references = [] := by
    rw [input.certified.buildLocalizedRerootCompoundRule4bcKey?_references_eq
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c) _ ((frame.cursorAt slot)) key.prior priorBuilt]
    exact selectionNil
  obtain ⟨reading, readings, referenceNone, _built⟩ :=
    input.certified.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_references_eq_nil
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      ((frame.cursorAt slot)) key.prior priorBuilt referencesNil
  exact ⟨selectionNil, referencesNil, reading, readings, referenceNone⟩

/-- **The actual zero-or-one Rule-4b reference selection.**  From the actual physical branch
domain at the final root and a frame slot of the final occurrence, the actual production Rule-4b
reference list is either empty (with a single no-reference reading) or a singleton carrying the
actual descriptor attached to the unique nearest physically marked centre of the branch. -/
theorem actualSlot_markedPhysicalBranchDomain_references_zero_or_singleton
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (branchDomain : MarkedPhysicalBranchDomain input ⟨c.1, c.2⟩ oAtom
      (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
        oAtom oObserved)) :
    (localizedRule4bReferencesFromRankedLabels
          (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels = [] ∧
        (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [] ∧
          ∃ reading : input.certified.LocalizedRerootRule4bcReading,
            (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [reading] ∧
              reading.reference? = none) ∨
      ∃ (center : input.certified.Atom) (distance : Nat) (descriptor : RS),
        MarkedBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom
            (branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
              oAtom oObserved) center distance descriptor ∧
          localizedRule4bReferencesFromRankedLabels
              (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels =
              [descriptor] ∧
            (actualSlotCompoundKey input c frame frameComputed slot).prior.references =
                [descriptor] ∧
              ∃ reading : input.certified.LocalizedRerootRule4bcReading,
                (actualSlotCompoundKey input c frame frameComputed slot).prior.readings =
                    [reading] ∧
                  reading.reference? = some descriptor := by
  rcases branchDomain with unmarked | ⟨center, distance, descriptor, unique⟩
  · exact Or.inl (actualSlot_physicalBranchUnmarked_references_nil input c frame frameComputed
      slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved unmarked)
  · exact Or.inr ⟨center, distance, descriptor, unique,
      actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed
        slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved unique⟩






theorem actualSlot_physicalBranchDomain_references_zero_or_singleton
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (branchDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtom) :
    (localizedRule4bReferencesFromRankedLabels
          (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels = [] ∧
        (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [] ∧
          ∃ reading : input.certified.LocalizedRerootRule4bcReading,
            (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [reading] ∧
              reading.reference? = none) ∨
      ∃ (center : input.certified.Atom) (distance : Nat) (descriptor : RS),
        PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance ∧
          branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
              oAtom oObserved center = some descriptor ∧
            localizedRule4bReferencesFromRankedLabels
                (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels =
                [descriptor] ∧
              (actualSlotCompoundKey input c frame frameComputed slot).prior.references =
                  [descriptor] ∧
                ∃ reading : input.certified.LocalizedRerootRule4bcReading,
                  (actualSlotCompoundKey input c frame frameComputed slot).prior.readings =
                      [reading] ∧
                    reading.reference? = some descriptor := by
  rcases branchDomain with unmarked | ⟨center, distance, unique⟩
  · exact Or.inl (actualSlot_physicalBranchUnmarked_references_nil input c frame frameComputed
      slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved unmarked)
  · obtain ⟨descriptor, marked⟩ :=
      exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input c frame frameComputed
        slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved unique
    obtain ⟨selection, references, reading, readings, referenceSome⟩ :=
      actualSlot_markedBranchUniqueNearest_references_singleton input c frame frameComputed
        slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved marked
    exact Or.inr ⟨center, distance, descriptor, unique, marked.2.1, selection, references,
      reading, readings, referenceSome⟩







theorem actualSlot_physicalBranchDomain_references_zero_or_singleton_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgPhys : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgPhys c)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (branchDomain : PhysicalBranchDomain input ⟨c.1, c.2⟩ oAtom) :
    (localizedRule4bReferencesFromRankedLabels
          (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels = [] ∧
        (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [] ∧
          ∃ reading : input.certified.LocalizedRerootRule4bcReading,
            (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [reading] ∧
              reading.reference? = none) ∨
      ∃ (center : input.certified.Atom) (distance : Nat) (descriptor : RS),
        PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance ∧
          branchMarkedDescriptor input c frame frameComputed slot singleBonded acyclic
              oAtom oObserved center = some descriptor ∧
            localizedRule4bReferencesFromRankedLabels
                (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels =
                [descriptor] ∧
              (actualSlotCompoundKey input c frame frameComputed slot).prior.references =
                  [descriptor] ∧
                ∃ reading : input.certified.LocalizedRerootRule4bcReading,
                  (actualSlotCompoundKey input c frame frameComputed slot).prior.readings =
                      [reading] ∧
                    reading.reference? = some descriptor := by
  have domain : ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration cfgPhys) c :=
    actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfgPhys c physicalDomain
  exact actualSlot_physicalBranchDomain_references_zero_or_singleton input c frame frameComputed
    slot singleBonded acyclic hcharge noDouble
    (input.certified.canonicalReindexConfiguration cfgPhys) domain oAtom oObserved branchDomain

end

end TetraStereo.OneCenter

/-! ## Kernel-only guards -/

assert_kernel_only TetraStereo.OneCenter.chiralDescriptorOfLabel
assert_kernel_only TetraStereo.OneCenter.chiralDescriptorOfLabel_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.chiralDescriptorOfLabel_eq_none_iff
assert_kernel_only TetraStereo.OneCenter.ActualSlotCut
assert_kernel_only TetraStereo.OneCenter.PhysicalMarkedAtom
assert_kernel_only TetraStereo.OneCenter.referenceDependencyView
assert_kernel_only TetraStereo.OneCenter.positionSource_root_eq_of_realized
assert_kernel_only TetraStereo.OneCenter.actualSlotCompoundKey
assert_kernel_only TetraStereo.OneCenter.actualSlotDerived
assert_kernel_only TetraStereo.OneCenter.actualSlotCompoundBuilt
assert_kernel_only TetraStereo.OneCenter.actualSlotPriorBuilt
assert_kernel_only TetraStereo.OneCenter.actualSlotRule4aBuilt
assert_kernel_only TetraStereo.OneCenter.actualSlotTreeExists
assert_kernel_only TetraStereo.OneCenter.actualSlotTree
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_source
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_labelTable
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_realizes
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_previousEq
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_valid
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_sameRoot
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_oObserved
assert_kernel_only TetraStereo.OneCenter.actualSlot_cursor_previousShorter
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_previousShorter
assert_kernel_only TetraStereo.OneCenter.actualSlot_incomingEdge
assert_kernel_only TetraStereo.OneCenter.actualSlotCutEquiv
assert_kernel_only TetraStereo.OneCenter.actualSlotCutEquiv_symm_apply
assert_kernel_only TetraStereo.OneCenter.actualSlotCutEquiv_symm_positionAtom
assert_kernel_only TetraStereo.OneCenter.branchMarkedDescriptor
assert_kernel_only TetraStereo.OneCenter.branchMarkedDescriptor_positionAtom
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_positionNode_label_eq_state
assert_kernel_only TetraStereo.OneCenter.actualSlotTree_reader
assert_kernel_only TetraStereo.OneCenter.referenceState_chiral_iff_physicalMarked
assert_kernel_only TetraStereo.OneCenter.chiralDescriptorOfLabel_state_eq_none_of_not_physicalMarked
assert_kernel_only TetraStereo.OneCenter.branchMarkedDescriptor_eq_none_of_not_physicalMarked
assert_kernel_only TetraStereo.OneCenter.MarkedBranchUniqueNearest
assert_kernel_only TetraStereo.OneCenter.MarkedPhysicalBranchDomain
assert_kernel_only TetraStereo.OneCenter.actualSlot_markedBranchUniqueNearest_references_singleton
assert_kernel_only TetraStereo.OneCenter.actualSlot_physicalBranchUnmarked_references_nil
assert_kernel_only TetraStereo.OneCenter.actualSlot_markedPhysicalBranchDomain_references_zero_or_singleton
assert_kernel_only TetraStereo.OneCenter.actualSlotCutEquiv_symm_root
assert_kernel_only TetraStereo.OneCenter.actualSlotCutEquiv_symm_current
assert_kernel_only TetraStereo.OneCenter.physicalMarkedAtom_of_branchMarkedDescriptor_eq_some
assert_kernel_only TetraStereo.OneCenter.exists_branchMarkedDescriptor_eq_some_of_physicalMarked
assert_kernel_only TetraStereo.OneCenter.PhysicalBranchUniqueNearest
assert_kernel_only TetraStereo.OneCenter.PhysicalBranchDomain
assert_kernel_only TetraStereo.OneCenter.exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest
assert_kernel_only TetraStereo.OneCenter.markedPhysicalBranchDomain_of_physicalBranchDomain
assert_kernel_only TetraStereo.OneCenter.actualSlot_physicalBranchDomain_references_zero_or_singleton
assert_kernel_only TetraStereo.OneCenter.actualSlot_physicalBranchDomain_references_zero_or_singleton_of_physicalDomain
