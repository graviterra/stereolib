



































































import TetraStereo.OneCenter.Source2013ParentTerminalKeySeparation
import TetraStereo.OneCenter.Source2013ParentDuplicateStructuralSeparation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo
namespace OneCenter

open Rule1bSourceProfileCompiler

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The first component of the official atomic label -/

namespace MoleculeGraph

/-- The first component of the official atomic label of an atom-bearing node is the atomic number
of its current atom, for **every** provenance class.  The real branch reads the raw CIP label; the
duplicate and placeholder branches use the same atomic number with zero Rule-2 mass.  Provenance
therefore never changes the Rule-1a first component. -/
theorem officialNodeAtomLabel_first_eq_atomZ_of_current
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (current : V)
    (hcurrent : node.current? = some current) :
    (ofLex (m.officialNodeAtomLabel node)).1 = m.atomZ current := by
  cases hprov : node.provenance with
  | realAtom =>
      simp [MoleculeGraph.officialNodeAtomLabel, MoleculeGraph.rawCIPAtomLabel,
        hcurrent, hprov]
  | multipleBondDuplicate distance =>
      simp [MoleculeGraph.officialNodeAtomLabel, hcurrent, hprov]
  | ringDuplicate distance =>
      simp [MoleculeGraph.officialNodeAtomLabel, hcurrent, hprov]
  | placeholder kind distance =>
      simp [MoleculeGraph.officialNodeAtomLabel, hcurrent, hprov]

end MoleculeGraph

/-! ## The actual parent-cut join -/

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput) {fuel : Nat}

/-- The actual parent's remaining expansion depth is positive even when the target sits at the
carrier frontier: the certificate gives `parent.remaining = target.remaining + 1`, so the parent
side always has room to emit its positive-copy child without inventing a carrier element. -/
theorem LocalizedParentFrameHistory.parent_remaining_positive
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    0 < certificate.parent.1.remaining := by
  rw [certificate.parent_remaining]
  omega

/-- **Actual join of the two sibling constructions.**  From an active target occurrence, its actual
parent certificate, the parent's actual current atom, bond order at least two, and positive target
remaining depth, the two actual outward reroot cursors exist:

* the backward multiple-bond duplicate of the parent atom, which is a terminal cursor;
* the actual parent rerooted away from the target, whose actual reroot child list is nonempty.

Their node labels have equal first atomic component and their 2013 root observations tie.  All
history facts are derived from `LocalizedParentFrameHistory.history_shape`; the parent's positive
remaining depth is derived from `parent_remaining` inside the structural construction. -/
theorem actualBackwardDuplicate_parentCut_structure
    {target : input.LocalizedCIPOccurrence fuel}
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (parentCurrent : input.Atom)
    (parentCurrentEq : certificate.parent.1.node.current? = some parentCurrent)
    (hdouble : 1 < input.moleculeGraph.bond certificate.current parentCurrent)
    (positive : 0 < target.1.remaining) :
    ∃ (backwardCursor parentCursor : input.LocalizedRerootCursor fuel),
      parentCursor = input.outwardCursor target certificate.parent ∧
      input.LocalizedRerootCursorValid parentCursor ∧
      input.LocalizedRerootCursorValid backwardCursor ∧
      (∃ slot : Nat, ∃ occurrence : input.LocalizedCIPOccurrence fuel,
        backwardCursor = input.outwardCursor target occurrence ∧
        occurrence.1.root = target.1.root ∧
        occurrence.1.address = target.1.address ++ [slot] ∧
        occurrence.1.node = target.1.node.extend parentCurrent 1 ∧
        occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate target.1.node.depth) ∧
      input.localizedRerootChildren? backwardCursor = some [] ∧
      (∃ leftChildren : List (input.LocalizedRerootCursor fuel),
        input.localizedRerootChildren? parentCursor = some leftChildren ∧
        leftChildren ≠ []) ∧
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
          parentCursor.occurrence.1.node)).1 =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          backwardCursor.occurrence.1.node)).1 ∧
      sourceObservation2013 parentCursor.occurrence.1.node =
        sourceObservation2013 backwardCursor.occurrence.1.node := by
  -- Actual history and current facts, derived from the certificate and its shape.
  obtain ⟨current, parentAtom, tail, htargetCurrent, hparentCurrent,
    htargetHistory, hparentHistory⟩ := certificate.history_shape input
  have currentEq : current = certificate.current :=
    Option.some.inj (htargetCurrent.symm.trans certificate.current_eq)
  subst current
  have parentAtomEq : parentAtom = parentCurrent :=
    Option.some.inj (hparentCurrent.symm.trans parentCurrentEq)
  subst parentAtom
  -- The genuine 2013 tie and the actual positive-copy child of the rerooted parent.
  obtain ⟨tie, slot, child, childMem, _childAddress, _childNode, _childCurrent,
    _childHistory, _childProvenance⟩ :=
    input.source2013_tie_and_actualParent_positiveCopyChild targetActive certificate
      certificate.current parentCurrent tail htargetCurrent htargetHistory
      hparentHistory hdouble
  -- The actual backward duplicate carrier occurrence and its terminal cursor.
  obtain ⟨backwardSlot, occurrence, occurrenceRoot, occurrenceAddress, occurrenceNode,
    occurrenceProvenance, backwardNil, _backwardPrevious⟩ :=
    input.exists_backwardDuplicate_outwardCursor_children_eq_nil target targetActive
      certificate.current parentCurrent htargetCurrent hdouble positive
  refine ⟨input.outwardCursor target occurrence,
    input.outwardCursor target certificate.parent, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The parent cursor is path-valid: the parent lies in the target's uncut neighborhood.
    change certificate.parent.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) target.1
    exact certificate.parent_mem_neighborFrames input
  · -- The backward duplicate cursor is path-valid: its occurrence is the actual carrier child
    -- at the extended address.
    change occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) target.1
    exact (input.mem_localizedRerootNeighborFrames_iff target.1 occurrence.1).mpr
      ⟨occurrence.2, occurrenceRoot,
        Or.inr ⟨by rw [occurrenceAddress]; simp, by rw [occurrenceAddress]; simp⟩⟩
  · -- The backward duplicate node is a duplicate leaf, hence terminal.
    refine ⟨backwardSlot, occurrence, rfl, occurrenceRoot, occurrenceAddress,
      occurrenceNode, occurrenceProvenance⟩
  · -- The actual reroot child list of the duplicate cursor is empty.
    rw [input.localizedRerootChildren?_eq_some_executable
      (input.outwardCursor target occurrence)]
    rw [backwardNil]
  · -- The parent cursor emits at least the actual positive-copy child.
    refine ⟨input.executableLocalizedRerootChildren
      (input.outwardCursor target certificate.parent),
      input.localizedRerootChildren?_eq_some_executable
        (input.outwardCursor target certificate.parent), ?_⟩
    intro empty
    rw [empty] at childMem
    simp at childMem
  · -- Equal root atomic label: both nodes carry `parentCurrent`.
    show (ofLex (input.moleculeGraph.officialNodeAtomLabel
        certificate.parent.1.node)).1 =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel occurrence.1.node)).1
    rw [occurrenceNode]
    have parentLabel :=
      MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current input.moleculeGraph
        certificate.parent.1.node parentCurrent parentCurrentEq
    have backwardLabel :=
      MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current input.moleculeGraph
        (target.1.node.extend parentCurrent 1) parentCurrent rfl
    exact parentLabel.trans backwardLabel.symm
  · -- The 2013 root observations tie.
    show sourceObservation2013 certificate.parent.1.node =
      sourceObservation2013 occurrence.1.node
    rw [occurrenceNode]
    exact tie.symm

/-! ## The actual 2013 comparison for every label reader -/

/-- **The original 2013 parent/backward-duplicate case, closed on actual data.**  From an active
target occurrence, its parent certificate, the parent's actual current atom, bond order at least
two, and positive target remaining depth, the two actual outward cursors are produced together
with their structural facts and, for **every** auxiliary-label reader, both observed cumulative
keys at fuel `2 * (fuel + 1)`:

* the first Rule-1b spheres of both keys are exactly the tied 2013 root observations;
* the Rule-1a comparison is `Ordering.gt` (the terminal duplicate side has exactly one sphere, the
  rerooted parent side has a nonempty merged child tail);
* the constitutional comparator is `Ordering.gt` without consulting Rule 1b;
* the cumulative comparator equals the constitutional one.

No key existence, no observation value, no comparison direction and no exact history is assumed. -/
theorem source2013_actualParentDuplicate_comparison
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    {target : input.LocalizedCIPOccurrence fuel}
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (parentCurrent : input.Atom)
    (parentCurrentEq : certificate.parent.1.node.current? = some parentCurrent)
    (hdouble : 1 < input.moleculeGraph.bond certificate.current parentCurrent)
    (positive : 0 < target.1.remaining) :
    ∃ (backwardCursor parentCursor : input.LocalizedRerootCursor fuel),
      parentCursor = input.outwardCursor target certificate.parent ∧
      input.LocalizedRerootCursorValid parentCursor ∧
      input.LocalizedRerootCursorValid backwardCursor ∧
      (∃ slot : Nat, ∃ occurrence : input.LocalizedCIPOccurrence fuel,
        backwardCursor = input.outwardCursor target occurrence ∧
        occurrence.1.root = target.1.root ∧
        occurrence.1.address = target.1.address ++ [slot] ∧
        occurrence.1.node = target.1.node.extend parentCurrent 1 ∧
        occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate target.1.node.depth) ∧
      input.localizedRerootChildren? backwardCursor = some [] ∧
      (∃ leftChildren : List (input.LocalizedRerootCursor fuel),
        input.localizedRerootChildren? parentCursor = some leftChildren ∧
        leftChildren ≠ []) ∧
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
          parentCursor.occurrence.1.node)).1 =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          backwardCursor.occurrence.1.node)).1 ∧
      sourceObservation2013 parentCursor.occurrence.1.node =
        sourceObservation2013 backwardCursor.occurrence.1.node ∧
      ∀ read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel,
        ∃ leftKey rightKey : input.LocalizedRerootCumulativeRule45Key,
          input.buildLocalizedObservedCumulativeRule45Key? stage
            (fun node => some (sourceObservation2013 node)) read
            (2 * (fuel + 1)) parentCursor = some leftKey ∧
          input.buildLocalizedObservedCumulativeRule45Key? stage
            (fun node => some (sourceObservation2013 node)) read
            (2 * (fuel + 1)) backwardCursor = some rightKey ∧
          leftKey.constitutional.rule1b.head? =
            some [([], sourceObservation2013 parentCursor.occurrence.1.node)] ∧
          rightKey.constitutional.rule1b.head? =
            some [([], sourceObservation2013 backwardCursor.occurrence.1.node)] ∧
          leftKey.constitutional.rule1b.head? = rightKey.constitutional.rule1b.head? ∧
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            leftKey.constitutional.rule1a rightKey.constitutional.rule1a = Ordering.gt ∧
          OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
            Ordering.gt ∧
          input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
            OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional := by
  obtain ⟨backwardCursor, parentCursor, hparentEq, hparentValid, hbackwardValid,
    hstructure, hbackwardChildren, ⟨leftChildren, hleftComputed, hleftNonempty⟩,
    hlabels, htie⟩ :=
    input.actualBackwardDuplicate_parentCut_structure targetActive certificate
      parentCurrent parentCurrentEq hdouble positive
  refine ⟨backwardCursor, parentCursor, hparentEq, hparentValid, hbackwardValid,
    hstructure, hbackwardChildren, ⟨leftChildren, hleftComputed, hleftNonempty⟩,
    hlabels, htie, ?_⟩
  intro read
  exact input.source2013_terminalRight_nonemptyLeft_separation_despite_rootTie
    stage read parentCursor backwardCursor hparentValid hbackwardValid leftChildren
    hleftComputed hleftNonempty hbackwardChildren hlabels htie

/-- **Strict observed comparison for every reader, as a standalone endpoint.**  The same actual
data yields, for every label reader, the two actual cursors, both observed keys, the tied Rule-1b
heads, the strict Rule-1a `gt`, the strict constitutional `gt`, and the cumulative comparison
identity at fuel `2 * (fuel + 1)`. -/
theorem source2013_actualParentDuplicate_strictComparison
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    {target : input.LocalizedCIPOccurrence fuel}
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (parentCurrent : input.Atom)
    (parentCurrentEq : certificate.parent.1.node.current? = some parentCurrent)
    (hdouble : 1 < input.moleculeGraph.bond certificate.current parentCurrent)
    (positive : 0 < target.1.remaining) :
    ∀ read : input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel,
      ∃ (backwardCursor parentCursor : input.LocalizedRerootCursor fuel)
        (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key),
        input.LocalizedRerootCursorValid parentCursor ∧
        input.LocalizedRerootCursorValid backwardCursor ∧
        input.localizedRerootChildren? backwardCursor = some [] ∧
        (∃ leftChildren : List (input.LocalizedRerootCursor fuel),
          input.localizedRerootChildren? parentCursor = some leftChildren ∧
          leftChildren ≠ []) ∧
        input.buildLocalizedObservedCumulativeRule45Key? stage
          (fun node => some (sourceObservation2013 node)) read
          (2 * (fuel + 1)) parentCursor = some leftKey ∧
        input.buildLocalizedObservedCumulativeRule45Key? stage
          (fun node => some (sourceObservation2013 node)) read
          (2 * (fuel + 1)) backwardCursor = some rightKey ∧
        leftKey.constitutional.rule1b.head? = rightKey.constitutional.rule1b.head? ∧
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          leftKey.constitutional.rule1a rightKey.constitutional.rule1a = Ordering.gt ∧
        OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
          Ordering.gt ∧
        input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
          OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional := by
  intro read
  obtain ⟨backwardCursor, parentCursor, _hparentEq, hparentValid, hbackwardValid,
    _hstructure, hbackwardChildren, ⟨leftChildren, hleftComputed, hleftNonempty⟩,
    _hlabels, _htie, hread⟩ :=
    input.source2013_actualParentDuplicate_comparison stage targetActive certificate
      parentCurrent parentCurrentEq hdouble positive
  obtain ⟨leftKey, rightKey, hleftBuilt, hrightBuilt, _hleftHead, _hrightHead,
    hheads, hrule1a, hconstitutional, hcumulative⟩ := hread read
  exact ⟨backwardCursor, parentCursor, leftKey, rightKey, hparentValid, hbackwardValid,
    hbackwardChildren, ⟨leftChildren, hleftComputed, hleftNonempty⟩, hleftBuilt,
    hrightBuilt, hheads, hrule1a, hconstitutional, hcumulative⟩

end CertifiedLocalizedCIPInput

end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_remaining_positive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualBackwardDuplicate_parentCut_structure
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.source2013_actualParentDuplicate_comparison
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.source2013_actualParentDuplicate_strictComparison
