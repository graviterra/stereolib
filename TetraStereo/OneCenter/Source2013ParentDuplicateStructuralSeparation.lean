/-
  Source2013ParentDuplicateStructuralSeparation

  Focused structural separation of the two nodes that tie under the corrected 2013 profile:

  * the *real* parent node of a non-root carrier occurrence, and
  * the backward `multipleBondDuplicate` copy `target.node.extend parentAtom 1`.

  The two nodes have equal `sourceObservation2013` (the existing parent tie), but differ
  structurally: the duplicate copy is a terminal official node and a terminal reroot cursor,
  while the actual parent, rerooted away from the target, still emits a positive-copy duplicate
  of the target's own current atom.  Two distinct mechanisms are involved:

  * the *reroot incoming-address cut* removes the previous occurrence's address from the parent's
    intended neighbor frames;
  * the ordinary official child-copy filter removes only the zero-index copy of the node's stored
    `parent?` atom, not a positive copy of the target's current atom.

  The extra child survives both: its copy index is `1`, so the official zero-copy filter does not
  apply, and its address differs from the cut target address.  The address inequality is proved
  by carrier functionality at the shared root and address: identifying the two frames would force
  the duplicate node to equal the real target node, contradicting their provenances.

  The central existence statement is conditional structural support.  It takes the admitted
  localized input, the carrier parent certificate, the actual target node's `ActiveSimple`
  status, bond order at least two, and the explicit history/current shape
  `target.history = current :: parentAtom :: tail`,
  `parent.history = parentAtom :: tail`, `target.current? = some current`.  Those exact-history
  equations are caller-supplied certificate data; they are not re-derived here and form the
  interface consumed by the history-derived actual-parent join sibling.  No successful key or
  comparison result is assumed.

  Positivity of the first atomic label component is derived from the admission certificate
  (`SemanticMolecule.toLocalizedMoleculeGraph_atomicNumber_supported`); the general form is also
  stated with an explicit `0 < atomZ` hypothesis for reuse outside admission.
-/

import TetraStereo.OneCenter.Source2013AuxiliaryDependencyRoute

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open Rule1bSourceProfile
open Rule1bSourceProfileCompiler

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## First component of the official atomic label

For a real (non-duplicate, non-placeholder) node the first component of the official CIP atom
label is exactly the raw atomic number of the current atom.  The duplicate and placeholder
branches use the same atomic number, so the equation actually holds for every atom-bearing node;
the real-provenance hypothesis is kept because it is the form consumed below. -/

/-- First component of the official node label at a real node is the current atom's atomic
number. -/
theorem officialNodeAtomLabel_first_eq_atomZ
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (current : V)
    (hcurrent : node.current? = some current)
    (hreal : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    (ofLex (m.officialNodeAtomLabel node)).1 = m.atomZ current := by
  rw [MoleculeGraph.officialNodeAtomLabel, hcurrent, hreal]
  simp [MoleculeGraph.rawCIPAtomLabel]

/-- Positivity of the first official label component from an explicit positive atomic number. -/
theorem officialNodeAtomLabel_first_positive_of_atomZ_pos
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (current : V)
    (hcurrent : node.current? = some current)
    (hreal : node.provenance = OfficialCIPNodeProvenance.realAtom)
    (hpositive : 0 < m.atomZ current) :
    0 < (ofLex (m.officialNodeAtomLabel node)).1 := by
  rw [officialNodeAtomLabel_first_eq_atomZ m node current hcurrent hreal]
  exact hpositive

namespace CertifiedLocalizedCIPInput

/-! ## Outward reroot cursors

The reroot cursor that moves from a source occurrence to an outward neighbor.  It remembers the
source as the incoming cut, so the intended neighbor list of the cursor is the neighbor list of
the occurrence with the source address removed. -/

/-- Reroot cursor whose occurrence is `occurrence` and whose incoming cut is `source`. -/
def outwardCursor (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source occurrence : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedRerootCursor fuel :=
  { occurrence := occurrence, previous? := some source }

/-- The cursor's occurrence coordinate is the supplied occurrence. -/
@[simp] theorem outwardCursor_occurrence
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source occurrence : input.LocalizedCIPOccurrence fuel) :
    (input.outwardCursor source occurrence).occurrence = occurrence :=
  rfl

/-- The cursor records the supplied source as its incoming cut. -/
@[simp] theorem outwardCursor_previous
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source occurrence : input.LocalizedCIPOccurrence fuel) :
    (input.outwardCursor source occurrence).previous? = some source :=
  rfl

/-! ## Atomic positivity from admission

The localized admission certificate stores a semantic molecule whose atomic numbers are positive
and at most 118.  Hence every label emitted for an actual current atom of the localized graph has
positive first component.  This removes the need for a separate positivity premise on the actual
parent node. -/

/-- The first official label component at a real node of an admitted localized input is positive. -/
theorem officialNodeAtomLabel_first_positive
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (current : input.Atom) (hcurrent : node.current? = some current)
    (hreal : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    0 < (ofLex (input.moleculeGraph.officialNodeAtomLabel node)).1 := by
  apply officialNodeAtomLabel_first_positive_of_atomZ_pos input.moleculeGraph node current
    hcurrent hreal
  simpa [CertifiedLocalizedCIPInput.moleculeGraph] using
    (SemanticMolecule.toLocalizedMoleculeGraph_atomicNumber_supported
      input.certified.input.molecule current).1

/-- The actual carrier parent of a non-root occurrence has a positive first atomic label
component, derived from admission and the parent certificate alone. -/
theorem LocalizedParentFrameHistory.parent_atomicNumber_positive
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target) :
    0 < (ofLex (input.moleculeGraph.officialNodeAtomLabel
      certificate.parent.1.node)).1 := by
  obtain ⟨_current, parentCurrent, _tail, _hcurrent, hparentCurrent, _hchild, _hparent⟩ :=
    LocalizedParentFrameHistory.history_shape input certificate
  exact input.officialNodeAtomLabel_first_positive certificate.parent.1.node parentCurrent
    hparentCurrent certificate.parent_active.1

/-! ## The 2013 parent tie, instantiated on the actual parent certificate -/

/-- Under the 2013 profile the backward multiple-bond copy of the actual parent atom ties with the
real parent: both observations equal the sphere of the duplicated parent atom on the pathway. -/
theorem sourceObservation2013_realParent_backwardDuplicate_tie
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (certificate : input.LocalizedParentFrameHistory target)
    (current parentAtom : input.Atom) (tail : List input.Atom)
    (htargetHistory : target.1.node.history = current :: parentAtom :: tail)
    (hparentHistory : certificate.parent.1.node.history = parentAtom :: tail) :
    sourceObservation2013 (target.1.node.extend parentAtom 1) =
      sourceObservation2013 certificate.parent.1.node :=
  sourceObservation2013_backwardParent_tie target.1.node certificate.parent.1.node
    current parentAtom tail 1 htargetHistory certificate.parent_active.1
    certificate.parent_active.2 hparentHistory (by decide)

/-! ## Duplicate terminals

A copy with positive copy index is always a `multipleBondDuplicate`, hence a terminal official
node with no executable children.  Consequently every reroot cursor whose occurrence is such a
duplicate has an empty executable child list: duplicate leaves are terminal in the occurrence
tree, not merely in the atom-level official enumeration. -/

/-- A positive-copy extension is a duplicate leaf and has no executable official children. -/
theorem executableOfficialCIPChildren_extend_pos_eq_nil
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (next : input.Atom) {copyIndex : Nat} (positive : copyIndex ≠ 0) :
    input.executableOfficialCIPChildren (node.extend next copyIndex) = [] := by
  have hduplicate : (node.extend next copyIndex).isDuplicateLeaf = true := by
    rw [OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_copy_pos node next positive]
    rfl
  simp [executableOfficialCIPChildren, hduplicate]

/-- A duplicate-leaf reroot cursor has no executable children. -/
theorem executableLocalizedRerootChildren_eq_nil_of_duplicateLeaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true) :
    input.executableLocalizedRerootChildren cursor = [] := by
  have hintended : input.intendedLocalizedRerootChildFrames cursor = [] := by
    simp [intendedLocalizedRerootChildFrames, duplicate]
  have hmap := input.executableLocalizedRerootChildren_map cursor
  rw [hintended] at hmap
  exact List.map_eq_nil_iff.mp hmap

/-- A cursor whose occurrence is a `multipleBondDuplicate` at any stored distance is terminal. -/
theorem executableLocalizedRerootChildren_eq_nil_of_multipleBondDuplicate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (distance : Nat)
    (duplicate : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate distance) :
    input.executableLocalizedRerootChildren cursor = [] := by
  apply input.executableLocalizedRerootChildren_eq_nil_of_duplicateLeaf cursor
  rw [OfficialCIPNode.isDuplicateLeaf, duplicate]
  rfl

/-! ## The actual parent retains a positive-copy duplicate of the target atom

The sibling module `Source2013AuxiliaryDependencyRoute` proves that the backward multiple-bond
copy `target.node.extend parentAtom 1` is a real executable child of the target and ties with the
real parent under the 2013 observation.  The present section moves to the *actual parent*
occurrence and reroots it away from the target.

Rerooting the parent with `previous? = some target` applies the reroot incoming-address cut: the
target's address is removed from the parent's intended neighbor frames.  Separately, the ordinary
official child-copy filter removes only the zero-index copy of the parent node's stored `parent?`
atom.  The target's current atom is still bonded to the parent atom with order at least two, so
copy `1` of that pair is available; its copy index is positive, so the official zero-copy filter
does not apply.  The emitted duplicate node `parent.node.extend current 1` is not the cut target:
identifying the two frames would force equality of a multiple-bond duplicate node with the real
target node.  Hence the extra child's address differs from the target address and it survives the
incoming-address cut.  This is the structural asymmetry: the 2013 tie node is terminal, while the
real parent rerooted at the same target is not. -/

/-- **Actual-parent extra child.**  From an active-simple target, its actual parent certificate,
the two history equations, and bond order at least two, the actual parent rerooted away from the
target emits a positive-copy duplicate of the target's current atom. -/
theorem actualParent_outwardCursor_positiveCopyChild
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (current parentAtom : input.Atom) (tail : List input.Atom)
    (htargetCurrent : target.1.node.current? = some current)
    (htargetHistory : target.1.node.history = current :: parentAtom :: tail)
    (hparentHistory : certificate.parent.1.node.history = parentAtom :: tail)
    (hdouble : 1 < input.moleculeGraph.bond current parentAtom) :
    ∃ slot child,
      child ∈ input.executableLocalizedRerootChildren
        (input.outwardCursor target certificate.parent) ∧
      child.occurrence.1.address = certificate.parent.1.address ++ [slot] ∧
      child.occurrence.1.node = certificate.parent.1.node.extend current 1 ∧
      child.occurrence.1.node.current? = target.1.node.current? ∧
      child.occurrence.1.node.history = target.1.node.history ∧
      child.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate certificate.parent.1.node.depth := by
  have hparentDerived : input.DeclarativeLocalizedOccurrence fuel certificate.parent.1 :=
    (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
  have htargetDerived : input.DeclarativeLocalizedOccurrence fuel target.1 :=
    (input.mem_localizedOccurrences_iff fuel target.1).mp target.2
  have hparentCurrent : certificate.parent.1.node.current? = some parentAtom := by
    have hhead := input.declarativeLocalizedOccurrence_node_history_head_eq_current hparentDerived
    rw [hparentHistory] at hhead
    exact hhead.symm
  have hparentNotDup : certificate.parent.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real certificate.parent.1.node
      certificate.parent_active.1
  have hparentPositive : 0 < certificate.parent.1.remaining := by
    rw [certificate.parent_remaining]
    exact Nat.succ_pos _
  have hDmem : certificate.parent.1.node.extend current 1 ∈
      input.executableOfficialCIPChildren certificate.parent.1.node := by
    apply input.mem_executableOfficialCIPChildren_of_adjacent certificate.parent.1.node
      parentAtom current 1 hparentNotDup hparentCurrent
    · unfold MoleculeGraph.Adj
      rw [input.moleculeGraph.bond_symm parentAtom current]
      exact Nat.lt_trans Nat.zero_lt_one hdouble
    · rw [input.moleculeGraph.bond_symm parentAtom current]
      exact hdouble
    · exact Or.inl (by decide : (1:ℕ) ≠ 0)
  obtain ⟨slot, hDslot⟩ := List.mem_iff_getElem?.mp hDmem
  have hDAtSlot : (certificate.parent.1.node.extend current 1, slot) ∈
      (input.executableOfficialCIPChildren certificate.parent.1.node).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hDslot
  let frame : input.LocalizedCIPOccurrenceFrame :=
    { root := certificate.parent.1.root
      address := certificate.parent.1.address ++ [slot]
      node := certificate.parent.1.node.extend current 1
      remaining := certificate.parent.1.remaining - 1 }
  have hframeDerived : input.DeclarativeLocalizedOccurrence fuel frame :=
    DeclarativeLocalizedOccurrence.immediateChild input hparentDerived hparentPositive hDAtSlot
  have hcursorNondup :
      (input.outwardCursor target certificate.parent).occurrence.1.node.isDuplicateLeaf =
        false := by
    simpa [outwardCursor] using hparentNotDup
  have hcursorPositive :
      0 < (input.outwardCursor target certificate.parent).occurrence.1.remaining := by
    simpa [outwardCursor] using hparentPositive
  have hcursorChildAtSlot : (certificate.parent.1.node.extend current 1, slot) ∈
      (input.executableOfficialCIPChildren
        (input.outwardCursor target certificate.parent).occurrence.1.node).zipIdx := by
    simpa [outwardCursor] using hDAtSlot
  have notIncoming : ∀ previous,
      (input.outwardCursor target certificate.parent).previous? = some previous →
        (input.outwardCursor target certificate.parent).occurrence.1.address ++ [slot] ≠
          previous.1.address := by
    intro previous hprevious hsame
    have hpreviousEq : previous = target := by
      have hsome : some target = some previous := hprevious
      exact (Option.some.inj hsome).symm
    have hsameTarget :
        (input.outwardCursor target certificate.parent).occurrence.1.address ++ [slot] =
          target.1.address := by
      simpa [hpreviousEq] using hsame
    have hframeAddress : frame.address = target.1.address := hsameTarget
    have hframeRoot : frame.root = target.1.root := certificate.parent_root
    have hframeEq : frame = target.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address
        hframeDerived htargetDerived hframeRoot hframeAddress
    have hnodeEq : certificate.parent.1.node.extend current 1 = target.1.node :=
      congrArg (fun occurrence : input.LocalizedCIPOccurrenceFrame => occurrence.node) hframeEq
    have hprovenanceEq : (certificate.parent.1.node.extend current 1).provenance =
        target.1.node.provenance :=
      congrArg (fun node : OfficialCIPNode input.Atom => node.provenance) hnodeEq
    have hDprovenance : (certificate.parent.1.node.extend current 1).provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate certificate.parent.1.node.depth := by
      rw [OfficialCIPNode.extend_provenance,
        OfficialCIPNode.childProvenance_copy_pos certificate.parent.1.node current
          (by decide : (1:ℕ) ≠ 0)]
    rw [hDprovenance, targetActive.1] at hprovenanceEq
    cases hprovenanceEq
  obtain ⟨children, childCursor, hcomputed, hpresent, hchildFrame⟩ :=
    input.exists_mem_localizedRerootChildren_of_executable_child
      (input.outwardCursor target certificate.parent) hcursorNondup hcursorPositive
      (certificate.parent.1.node.extend current 1) slot hcursorChildAtSlot notIncoming
  have hcomputedExec : input.localizedRerootChildren?
      (input.outwardCursor target certificate.parent) =
      some (input.executableLocalizedRerootChildren
        (input.outwardCursor target certificate.parent)) :=
    input.localizedRerootChildren?_eq_some_executable _
  have hchildrenEq : children =
      input.executableLocalizedRerootChildren
        (input.outwardCursor target certificate.parent) := by
    rw [hcomputedExec] at hcomputed
    exact (Option.some.inj hcomputed).symm
  have hnode : childCursor.occurrence.1.node =
      certificate.parent.1.node.extend current 1 :=
    congrArg (fun occurrence : input.LocalizedCIPOccurrenceFrame => occurrence.node) hchildFrame
  have haddress : childCursor.occurrence.1.address =
      certificate.parent.1.address ++ [slot] :=
    congrArg (fun occurrence : input.LocalizedCIPOccurrenceFrame => occurrence.address)
      hchildFrame
  have hprovenance : childCursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate certificate.parent.1.node.depth := by
    rw [hnode, OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_copy_pos certificate.parent.1.node current
        (by decide : (1:ℕ) ≠ 0)]
  have hcurrent : childCursor.occurrence.1.node.current? = target.1.node.current? := by
    rw [hnode, OfficialCIPNode.extend_current?, htargetCurrent]
  have hhistory : childCursor.occurrence.1.node.history = target.1.node.history := by
    rw [hnode, OfficialCIPNode.extend_history, hparentHistory, ← htargetHistory]
  refine ⟨slot, childCursor, ?_, haddress, hnode, hcurrent, hhistory, hprovenance⟩
  rw [← hchildrenEq]
  exact hpresent

/-- **Nonempty actual-parent reroot children.**  The cut reroot of the actual parent away from
the target is not terminal: it retains the positive-copy duplicate of the target's current atom.
This is the nonemptiness fact consumed by the terminal-separation sibling. -/
theorem actualParent_outwardCursor_children_ne_nil
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (current parentAtom : input.Atom) (tail : List input.Atom)
    (htargetCurrent : target.1.node.current? = some current)
    (htargetHistory : target.1.node.history = current :: parentAtom :: tail)
    (hparentHistory : certificate.parent.1.node.history = parentAtom :: tail)
    (hdouble : 1 < input.moleculeGraph.bond current parentAtom) :
    input.executableLocalizedRerootChildren
      (input.outwardCursor target certificate.parent) ≠ [] := by
  obtain ⟨_slot, child, hchild, _haddress, _hnode, _hcurrent, _hhistory, _hprovenance⟩ :=
    input.actualParent_outwardCursor_positiveCopyChild targetActive certificate current
      parentAtom tail htargetCurrent htargetHistory hparentHistory hdouble
  exact List.ne_nil_of_mem hchild

/-! ## The backward duplicate reroot cursor is terminal

The backward copy is the sibling side of the same bond.  It is a `multipleBondDuplicate` at the
target depth, so its occurrence is a duplicate leaf and the corresponding outward cursor has no
children at all.  The carrier occurrence is constructed from the actual executable child slot, so
the statement is about an occurrence admitted by the same carrier as the target, not about a
hand-written node.  The only side condition is that the target still has positive remaining
expansion depth, which is required for its address to have room for one more sibling slot. -/

/-- **Backward-duplicate terminal cursor.**  For a reachable target with positive remaining depth
there exists the actual backward duplicate occurrence whose address extends the target address,
whose node is `target.node.extend parentAtom 1`, and whose outward reroot cursor (with the target
as incoming cut) has no children. -/
theorem exists_backwardDuplicate_outwardCursor_children_eq_nil
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (targetActive : target.1.node.ActiveSimple)
    (current parentAtom : input.Atom)
    (htargetCurrent : target.1.node.current? = some current)
    (hdouble : 1 < input.moleculeGraph.bond current parentAtom)
    (positive : 0 < target.1.remaining) :
    ∃ slot : Nat, ∃ occurrence : input.LocalizedCIPOccurrence fuel,
      occurrence.1.root = target.1.root ∧
      occurrence.1.address = target.1.address ++ [slot] ∧
      occurrence.1.node = target.1.node.extend parentAtom 1 ∧
      occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate target.1.node.depth ∧
      input.executableLocalizedRerootChildren
        (input.outwardCursor target occurrence) = [] ∧
      (input.outwardCursor target occurrence).previous? = some target := by
  have hmem : target.1.node.extend parentAtom 1 ∈
      input.executableOfficialCIPChildren target.1.node :=
    input.backwardParentDuplicate_mem_executableOfficialCIPChildren target.1.node
      current parentAtom targetActive htargetCurrent hdouble
  obtain ⟨slot, hslot⟩ := List.mem_iff_getElem?.mp hmem
  have hAtSlot : (target.1.node.extend parentAtom 1, slot) ∈
      (input.executableOfficialCIPChildren target.1.node).zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr hslot
  let frame : input.LocalizedCIPOccurrenceFrame :=
    { root := target.1.root
      address := target.1.address ++ [slot]
      node := target.1.node.extend parentAtom 1
      remaining := target.1.remaining - 1 }
  have hframeDerived : input.DeclarativeLocalizedOccurrence fuel frame :=
    DeclarativeLocalizedOccurrence.immediateChild input
      ((input.mem_localizedOccurrences_iff fuel target.1).mp target.2) positive hAtSlot
  let occurrence : input.LocalizedCIPOccurrence fuel :=
    ⟨frame, (input.mem_localizedOccurrences_iff fuel frame).mpr hframeDerived⟩
  have hprovenance : occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate target.1.node.depth := by
    show (target.1.node.extend parentAtom 1).provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate target.1.node.depth
    rw [OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_copy_pos target.1.node parentAtom
        (by decide : (1:ℕ) ≠ 0)]
  have hnil : input.executableLocalizedRerootChildren
      (input.outwardCursor target occurrence) = [] :=
    input.executableLocalizedRerootChildren_eq_nil_of_multipleBondDuplicate
      (input.outwardCursor target occurrence) target.1.node.depth
      (by simpa [outwardCursor] using hprovenance)
  exact ⟨slot, occurrence, rfl, rfl, rfl, hprovenance, hnil, rfl⟩

/-! ## Combined source-level endpoint -/

/-- **Tie plus structural asymmetry in one statement.**  Under the 2013 profile the backward
duplicate copy and the real parent tie, while the actual parent rerooted away from the target
still emits the positive-copy duplicate of the target's current atom. -/
theorem source2013_tie_and_actualParent_positiveCopyChild
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {target : input.LocalizedCIPOccurrence fuel}
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (current parentAtom : input.Atom) (tail : List input.Atom)
    (htargetCurrent : target.1.node.current? = some current)
    (htargetHistory : target.1.node.history = current :: parentAtom :: tail)
    (hparentHistory : certificate.parent.1.node.history = parentAtom :: tail)
    (hdouble : 1 < input.moleculeGraph.bond current parentAtom) :
    sourceObservation2013 (target.1.node.extend parentAtom 1) =
        sourceObservation2013 certificate.parent.1.node ∧
      (∃ slot : Nat, ∃ child : input.LocalizedRerootCursor fuel,
        child ∈ input.executableLocalizedRerootChildren
          (input.outwardCursor target certificate.parent) ∧
        child.occurrence.1.address = certificate.parent.1.address ++ [slot] ∧
        child.occurrence.1.node = certificate.parent.1.node.extend current 1 ∧
        child.occurrence.1.node.current? = target.1.node.current? ∧
        child.occurrence.1.node.history = target.1.node.history ∧
        child.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate certificate.parent.1.node.depth) := by
  refine ⟨?_, ?_⟩
  · exact input.sourceObservation2013_realParent_backwardDuplicate_tie certificate
      current parentAtom tail htargetHistory hparentHistory
  · obtain ⟨slot, child, hchild, haddress, hnode, hcurrent, hhistory, hprovenance⟩ :=
      input.actualParent_outwardCursor_positiveCopyChild targetActive certificate current
        parentAtom tail htargetCurrent htargetHistory hparentHistory hdouble
    exact ⟨slot, child, hchild, haddress, hnode, hcurrent, hhistory, hprovenance⟩

end CertifiedLocalizedCIPInput

end OneCenter
end TetraStereo

/-! ## Kernel-authority assertions -/

assert_kernel_only TetraStereo.OneCenter.officialNodeAtomLabel_first_eq_atomZ
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardCursor_occurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardCursor_previous
assert_kernel_only TetraStereo.OneCenter.officialNodeAtomLabel_first_positive_of_atomZ_pos
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.officialNodeAtomLabel_first_positive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedParentFrameHistory.parent_atomicNumber_positive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sourceObservation2013_realParent_backwardDuplicate_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialCIPChildren_extend_pos_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_eq_nil_of_duplicateLeaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_eq_nil_of_multipleBondDuplicate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualParent_outwardCursor_positiveCopyChild
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualParent_outwardCursor_children_ne_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_backwardDuplicate_outwardCursor_children_eq_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.source2013_tie_and_actualParent_positiveCopyChild
