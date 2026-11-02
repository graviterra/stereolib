/-
  Source2013AuxiliaryDependencyRoute

  Structural route around the *parent-side* Rule-1b dependency under the corrected 2013
  duplicate-only represented-distance observation
  (`Rule1bSourceProfileCompiler.sourceObservation2013`).

  ## The obstruction

  The parent-distance separation used by `LocalizedActualParentComparisonSeparation` rests on the
  implemented *total* Hanson-proposed observation `OfficialCIPNode.rule1bRootDistance`.  For a real
  node that observation is its own sphere, and a backward multiple-bond copy of the parent atom
  stores `parent.depth + 1`, so the two values differ.

  Under the 2013 profile a backward multiple-bond copy is ranked by the sphere of the duplicated
  atom on the exploration pathway -- exactly the parent atom's own sphere.  If the target history
  is `current :: parentAtom :: tail` and the real parent history is `parentAtom :: tail`, the copy
  `target.extend parentAtom copyIndex` (`copyIndex ≠ 0`) has 2013 observation `tail.length`, which
  is also the parent's 2013 observation.  The two **tie**; the stored 2018 values
  (`tail.length + 1` versus `tail.length`) separate.  Hence the parent-distance proof cannot be
  transported blindly.

  ## The route proved here

  * `sourceObservation2013_extend_ne_realParent`: every extension of the target by an atom *other
    than the parent atom* separates from the parent under the 2013 observation.  Under the
    executable child enumeration this identifies the backward parent copy as the only emitted
    child that can tie.
  * `backwardParentDuplicate_mem_executableOfficialCIPChildren` and
    `sourceBound_backwardParent_obstruction`: whenever the target is a real node whose atom is
    doubly bonded to its parent atom, the tied backward copy is an **actual emitted child** of the
    `executableOfficialCIPChildren` enumeration; the tie is therefore source-bound, not merely a
    hand-written node pair.
  * `rule1aRootAtomicNumber_decisive` / `parentSide_outwardChild_rule1a_decisive`: when the two
    cursor nodes carry different root atomic numbers, genuine Rule-1a separation decides the
    constitutional comparator before Rule 1b is consulted, and the cumulative comparator follows.
    This avoids every Rule-1b question, 2013 or 2018.
  * `parentFrame_not_depthDependency` / `parentCursor_dependencyLabel_eq_none` and
    `outwardChild_depthDependency` / `outwardChild_dependencyLabel_eq_state`: the actual parent has
    a strictly *shorter* carrier address, so it is not a depth dependency of the target and its
    restricted dependency label is `none`; an outward executable child has an appended address, so
    it *is* a depth dependency and its restricted label reads the unrestricted earlier stage state.

  ## Honesty

  * The `realAtom` branch of `sourceObservation2013` is a comparison-totality convention; the 2013
    clauses speak only about duplicate nodes.  The 2013 statements below never rank real nodes by
    the duplicate rule; the real-atom values used are the shared `depth` convention documented in
    `SourceProfileRule1bCompiler`.
  * No claim is made that the 2013 duplicate-only rule justifies the ordinary real-node distance
    sorting; the stored attachment coordinates are unchanged.
  * Missing stereo annotation is not treated as nonstereogenic, and finite molecules are not
    asserted to have unique descriptor solutions.
  * The concrete allene fixture is a node-level witness only; it is not wired to a
    `CertifiedLocalizedCIPInput`.
-/

import TetraStereo.OneCenter.LocalizedActualParentComparisonSeparation
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.SourceProfileRule1bCompiler
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open Rule1bSourceProfile
open Rule1bSourceProfileCompiler

variable {V : Type*} [DecidableEq V]

/-! ## The 2013 tie and the stored 2018 contrast -/

/-- The shared real-atom branch of the 2013 observation: a real node reads its own sphere.  This is
the comparison-totality convention, not a normative 2013 clause. -/
private theorem sourceObservation2013_of_real
    (node : OfficialCIPNode V)
    (hreal : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    sourceObservation2013 node = node.depth := by
  simp [sourceObservation2013, hreal]

/-- A zero-index copy of an atom already on the branch is a ring-closure duplicate; its 2013
represented sphere is the existing path index of the duplicated atom. -/
private theorem sourceObservation2013_extend_zero_ring
    (parent : OfficialCIPNode V) (next : V) (hmem : next ∈ parent.history) :
    sourceObservation2013 (parent.extend next 0) = parent.duplicateRootDistance next := by
  rw [sourceObservation2013_extend_ring parent next hmem]
  simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.childProvenance, hmem]

/-- A zero-index copy of a fresh atom is a real child; its 2013 observation is its own sphere. -/
private theorem sourceObservation2013_extend_zero_real
    (parent : OfficialCIPNode V) (next : V) (hnot : next ∉ parent.history) :
    sourceObservation2013 (parent.extend next 0) = (parent.extend next 0).depth := by
  rw [sourceObservation2013_extend_real parent next hnot]
  simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.childProvenance, hnot]

/-- A positive-index copy of a fresh atom is a forward multiple-bond duplicate; its 2013
represented sphere is the sphere of its own occurrence, i.e. the extension's depth. -/
private theorem sourceObservation2013_extend_pos_forward
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) (hnot : next ∉ parent.history) :
    sourceObservation2013 (parent.extend next copyIndex) =
      (parent.extend next copyIndex).depth := by
  rw [sourceObservation2013_extend_multipleBond_forward parent next copyIndex hcopy hnot]
  simp [bb2013Observation, Official.extendedSpheres, OfficialCIPNode.childProvenance,
    hcopy, hnot]

/-- A positive-index copy of an atom already on the branch is a backward multiple-bond duplicate;
its 2013 represented sphere is the existing path index of that atom. -/
private theorem sourceObservation2013_extend_pos_backward
    (parent : OfficialCIPNode V) (next : V) (copyIndex : ℕ)
    (hcopy : copyIndex ≠ 0) (hmem : next ∈ parent.history) :
    sourceObservation2013 (parent.extend next copyIndex) = parent.duplicateRootDistance next :=
  (sourceObservation2013_extend_multipleBond_backward_reads_history
    parent next copyIndex hcopy hmem).1

/-- If an atom occurs in the shared tail, then its first occurrence from the reversed full history
lies strictly inside the reversed tail.  No duplicate-free hypothesis on the full history is
needed: the reversed tail alone supplies an occurrence. -/
private theorem duplicateRootDistance_lt_of_mem_tail
    (parent : OfficialCIPNode V)
    (next current parentAtom : V) (tail : List V)
    (hhistory : parent.history = current :: parentAtom :: tail)
    (hmem : next ∈ tail) :
    parent.duplicateRootDistance next < tail.length := by
  obtain ⟨index, hindex⟩ :=
    firstIndexOf?_eq_some_of_mem next (List.mem_reverse.mpr hmem)
  have hindexLt : index < tail.length := by
    have getElem := firstIndexOf?_eq_some_imp_getElem? next tail.reverse index hindex
    rw [List.getElem?_eq_some_iff] at getElem
    simpa using getElem.1
  have hreverse : parent.history.reverse = (tail.reverse ++ [parentAtom]) ++ [current] := by
    rw [hhistory]
    simp
  have hleft : firstIndexOf? next (tail.reverse ++ [parentAtom]) = some index := by
    rw [firstIndexOf?_append_eq_left_of_found next tail.reverse [parentAtom]
      ⟨index, hindex⟩, hindex]
  have hfound : ∃ position, firstIndexOf? next (tail.reverse ++ [parentAtom]) = some position :=
    ⟨index, hleft⟩
  have hdistance : parent.duplicateRootDistance next = index := by
    rw [OfficialCIPNode.duplicateRootDistance, hreverse,
      firstIndexOf?_append_eq_left_of_found next (tail.reverse ++ [parentAtom]) [current] hfound,
      hleft]
    simp
  rw [hdistance]
  exact hindexLt

/-- If the parent atom is absent from the shared tail, its first occurrence from the reversed
target history is the second entry, at index `tail.length`. -/
private theorem duplicateRootDistance_parentAtom_eq_tail_length
    (parent : OfficialCIPNode V)
    (current parentAtom : V) (tail : List V)
    (hhistory : parent.history = current :: parentAtom :: tail)
    (hnot : parentAtom ∉ tail) :
    parent.duplicateRootDistance parentAtom = tail.length := by
  have hnotReverse : parentAtom ∉ tail.reverse := by
    simpa using hnot
  have hleft :
      firstIndexOf? parentAtom (tail.reverse ++ [parentAtom]) = some tail.reverse.length :=
    firstIndexOf?_append_singleton_of_not_mem parentAtom tail.reverse hnotReverse
  have hreverse : parent.history.reverse = (tail.reverse ++ [parentAtom]) ++ [current] := by
    rw [hhistory]
    simp
  have hfound : ∃ position,
      firstIndexOf? parentAtom (tail.reverse ++ [parentAtom]) = some position :=
    ⟨tail.reverse.length, hleft⟩
  rw [OfficialCIPNode.duplicateRootDistance, hreverse,
    firstIndexOf?_append_eq_left_of_found parentAtom (tail.reverse ++ [parentAtom])
      [current] hfound, hleft]
  simp

/-- The depth of any extension of a target whose history is `current :: fixed :: tail`. -/
private theorem extend_depth_eq_tail_add_two
    (parent : OfficialCIPNode V)
    (current fixed : V) (tail : List V) (next : V) (copyIndex : ℕ)
    (hhistory : parent.history = current :: fixed :: tail) :
    (parent.extend next copyIndex).depth = tail.length + 2 := by
  have hnonempty : 0 < parent.history.length := by
    rw [hhistory]
    simp
  have hdepth : parent.depth = tail.length + 1 := by
    simp [OfficialCIPNode.depth, hhistory]
  rw [Official.extend_depth_eq_attached_add_one parent next copyIndex hnonempty, hdepth]

omit [DecidableEq V] in
/-- A member of the target history other than the target's current atom and the parent atom lies in
the shared tail. -/
private theorem mem_tail_of_mem_history_ne
    (next current parentAtom : V) (tail : List V)
    (hmem : next ∈ current :: parentAtom :: tail)
    (hneCurrent : next ≠ current) (hneParent : next ≠ parentAtom) :
    next ∈ tail := by
  rcases List.mem_cons.mp hmem with head | rest
  · exact (hneCurrent head).elim
  · rcases List.mem_cons.mp rest with second | tailMember
    · exact (hneParent second).elim
    · exact tailMember

/-- **The exact 2013 parent tie.**

For a target history `current :: parentAtom :: tail` and a real, duplicate-free parent history
`parentAtom :: tail`, every backward multiple-bond copy of the parent atom has the *same* 2013
represented observation as the real parent: both are `tail.length`.  The copy is ranked by the
sphere of the duplicated atom on the pathway, which is exactly the parent's own sphere.

This is the case in which the total 2018 parent-distance separation cannot be ported to the 2013
profile. -/
theorem sourceObservation2013_backwardParent_tie
    (target parent : OfficialCIPNode V)
    (current parentAtom : V) (tail : List V) (copyIndex : ℕ)
    (htargetHistory : target.history = current :: parentAtom :: tail)
    (hparentProvenance : parent.provenance = OfficialCIPNodeProvenance.realAtom)
    (hparentNodup : parent.history.Nodup)
    (hparentHistory : parent.history = parentAtom :: tail)
    (hcopy : copyIndex ≠ 0) :
    sourceObservation2013 (target.extend parentAtom copyIndex) =
      sourceObservation2013 parent := by
  have hmem : parentAtom ∈ target.history := by
    rw [htargetHistory]
    simp
  have hbackward :=
    sourceObservation2013_extend_pos_backward target parentAtom copyIndex hcopy hmem
  have hparentNodup' : (parentAtom :: tail).Nodup := by
    simpa [hparentHistory] using hparentNodup
  have hnotTail : parentAtom ∉ tail := (List.nodup_cons.mp hparentNodup').1
  have hduplicate :=
    duplicateRootDistance_parentAtom_eq_tail_length target current parentAtom tail
      htargetHistory hnotTail
  have hparentObservation : sourceObservation2013 parent = tail.length := by
    rw [sourceObservation2013_of_real parent hparentProvenance]
    simp [OfficialCIPNode.depth, hparentHistory]
  rw [hbackward, hduplicate, hparentObservation]

/-- **The stored 2018 parent contrast.**

On the same history shape, a backward multiple-bond copy of the parent atom has stored observation
`target.depth = tail.length + 1`, strictly greater than the real parent's stored observation
`tail.length`.  This is precisely why the existing total-observation parent separation succeeds
where the 2013 duplicate-only observation ties. -/
theorem backwardParent_storedDistance_ne
    (target parent : OfficialCIPNode V)
    (current parentAtom : V) (tail : List V) (copyIndex : ℕ)
    (htargetHistory : target.history = current :: parentAtom :: tail)
    (hparentProvenance : parent.provenance = OfficialCIPNodeProvenance.realAtom)
    (hparentHistory : parent.history = parentAtom :: tail)
    (hcopy : copyIndex ≠ 0) :
    (target.extend parentAtom copyIndex).rule1bRootDistance ≠
      parent.rule1bRootDistance := by
  have hchildStored : (target.extend parentAtom copyIndex).rule1bRootDistance =
      target.depth := by
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, hcopy]
  have hparentStored : parent.rule1bRootDistance = tail.length := by
    simp [OfficialCIPNode.rule1bRootDistance, hparentProvenance, OfficialCIPNode.depth,
      hparentHistory]
  have htargetDepth : target.depth = tail.length + 1 := by
    simp [OfficialCIPNode.depth, htargetHistory]
  rw [hchildStored, hparentStored, htargetDepth]
  omega

/-- **Genuine 2013 separation for every non-parent-atom extension.**

Assume the target history `current :: parentAtom :: tail`, a real parent with history
`parentAtom :: tail`, and that the extended atom `next` is graph-adjacent to the target's current
atom.  If `next` is not the parent atom, then the 2013 observation of the extension differs from the
parent's 2013 observation.

Every case is separated strictly:
* `next ∈ target.history` contributes a ring-closure or backward multiple-bond duplicate whose
  represented index is `< tail.length` (`duplicateRootDistance_lt_of_mem_tail`);
* `next ∉ target.history` contributes a real or forward multiple-bond observation at the
  extension's own depth `tail.length + 2`, one beyond the parent's `tail.length`.

Adjacency removes `next = current` (a self-bond would be an empty bond).  Consequently, among all
extensions of the target, only an extension by the parent atom can tie with the parent under the
2013 observation. -/
theorem sourceObservation2013_extend_ne_realParent
    (input : CertifiedLocalizedCIPInput)
    (target parent : OfficialCIPNode input.Atom)
    (current parentAtom : input.Atom) (tail : List input.Atom)
    (next : input.Atom) (copyIndex : ℕ)
    (htargetHistory : target.history = current :: parentAtom :: tail)
    (hparentProvenance : parent.provenance = OfficialCIPNodeProvenance.realAtom)
    (hparentHistory : parent.history = parentAtom :: tail)
    (hadj : input.moleculeGraph.Adj current next)
    (hneParent : next ≠ parentAtom) :
    sourceObservation2013 (target.extend next copyIndex) ≠
      sourceObservation2013 parent := by
  have hneCurrent : next ≠ current := by
    intro same
    rw [same] at hadj
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at hadj
  have hparentObservation : sourceObservation2013 parent = tail.length := by
    rw [sourceObservation2013_of_real parent hparentProvenance]
    simp [OfficialCIPNode.depth, hparentHistory]
  by_cases hmem : next ∈ target.history
  · have hmemList : next ∈ current :: parentAtom :: tail := by
      simpa [htargetHistory] using hmem
    have hnextTail : next ∈ tail :=
      mem_tail_of_mem_history_ne next current parentAtom tail hmemList hneCurrent hneParent
    have hbound : target.duplicateRootDistance next < tail.length :=
      duplicateRootDistance_lt_of_mem_tail target next current parentAtom tail
        htargetHistory hnextTail
    by_cases hzero : copyIndex = 0
    · subst copyIndex
      have hobservation := sourceObservation2013_extend_zero_ring target next hmem
      rw [hobservation, hparentObservation]
      exact Nat.ne_of_lt hbound
    · have hobservation :=
        sourceObservation2013_extend_pos_backward target next copyIndex hzero hmem
      rw [hobservation, hparentObservation]
      exact Nat.ne_of_lt hbound
  · have hdepth : (target.extend next copyIndex).depth = tail.length + 2 :=
      extend_depth_eq_tail_add_two target current parentAtom tail next copyIndex
        htargetHistory
    by_cases hzero : copyIndex = 0
    · subst copyIndex
      have hobservation := sourceObservation2013_extend_zero_real target next hmem
      rw [hobservation, hdepth, hparentObservation]
      omega
    · have hobservation :=
        sourceObservation2013_extend_pos_forward target next copyIndex hzero hmem
      rw [hobservation, hdepth, hparentObservation]
      omega

namespace CertifiedLocalizedCIPInput

/-- **Executable-child form of the 2013 separation.**

For an actual emitted child `target.extend next copyIndex` of the executable official children,
adjacency of `current` and `next` is recovered from the enumeration itself
(`adj_of_mem_executableOfficialCIPChildren`).  Hence every emitted child whose atom is not the
parent atom separates from the parent under the 2013 observation, in both the zero-copy (real or
ring-closure) and positive-copy (forward or backward multiple-bond) cases. -/
theorem sourceObservation2013_executableChild_ne_realParent
    (input : CertifiedLocalizedCIPInput)
    (target parent : OfficialCIPNode input.Atom)
    (current parentAtom : input.Atom) (tail : List input.Atom)
    (next : input.Atom) (copyIndex : ℕ)
    (htargetCurrent : target.current? = some current)
    (htargetHistory : target.history = current :: parentAtom :: tail)
    (hparentProvenance : parent.provenance = OfficialCIPNodeProvenance.realAtom)
    (hparentHistory : parent.history = parentAtom :: tail)
    (hchild : target.extend next copyIndex ∈ input.executableOfficialCIPChildren target)
    (hneParent : next ≠ parentAtom) :
    sourceObservation2013 (target.extend next copyIndex) ≠
      sourceObservation2013 parent := by
  have hadj : input.moleculeGraph.Adj current next :=
    input.adj_of_mem_executableOfficialCIPChildren target
      (target.extend next copyIndex) current next htargetCurrent rfl hchild
  exact sourceObservation2013_extend_ne_realParent input target parent current parentAtom tail
    next copyIndex htargetHistory hparentProvenance hparentHistory hadj hneParent

/-- **The backward parent duplicate is an actual emitted child.**

If the target is a real node whose current atom is doubly bonded to the parent atom, then the
positive-index copy of the parent atom -- the backward multiple-bond duplicate -- is a member of the
executable official children of the target.  This is source-bound: the copy exists in the same
enumeration the production compiler consumes, not merely as an abstract `extend`. -/
theorem backwardParentDuplicate_mem_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput)
    (target : OfficialCIPNode input.Atom)
    (current parentAtom : input.Atom)
    (htargetActive : target.ActiveSimple)
    (htargetCurrent : target.current? = some current)
    (hdouble : 1 < input.moleculeGraph.bond current parentAtom) :
    target.extend parentAtom 1 ∈ input.executableOfficialCIPChildren target := by
  have hnotDuplicate : target.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real target htargetActive.1
  have hadj : input.moleculeGraph.Adj current parentAtom := by
    unfold MoleculeGraph.Adj
    exact Nat.lt_trans Nat.zero_lt_one hdouble
  exact input.mem_executableOfficialCIPChildren_of_adjacent target current parentAtom 1
    hnotDuplicate htargetCurrent hadj hdouble (Or.inl (by decide))

/-- **Source-bound backward-parent obstruction under the 2013 profile.**

Take a non-root carrier occurrence `target` with its actual parent-frame certificate, and suppose
the target node's current atom is doubly bonded to the parent atom (bond order at least two, as in
an allene branch).  Then:

1. the backward multiple-bond copy `target.extend parentAtom 1` is an actual executable official
   child of the target;
2. its 2013 observation equals the parent's 2013 observation (a genuine tie);
3. its stored 2018 observation differs from the parent's stored observation.

Thus the 2013 tie is not an artefact of a hand-written pair: it is realized by nodes that the
existing executable child enumeration and the existing total observation both see.  The parent-
distance separation therefore cannot be applied under the 2013 profile without an additional
argument (Rule 1a or depth-dependency availability, both supplied below). -/
theorem sourceBound_backwardParent_obstruction
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (current parentAtom : input.Atom) (tail : List input.Atom)
    (htargetCurrent : target.1.node.current? = some current)
    (htargetHistory : target.1.node.history = current :: parentAtom :: tail)
    (hparentHistory : certificate.parent.1.node.history = parentAtom :: tail)
    (hdouble : 1 < input.moleculeGraph.bond current parentAtom) :
    target.1.node.extend parentAtom 1 ∈
        input.executableOfficialCIPChildren target.1.node ∧
      sourceObservation2013 (target.1.node.extend parentAtom 1) =
        sourceObservation2013 certificate.parent.1.node ∧
      (target.1.node.extend parentAtom 1).rule1bRootDistance ≠
        certificate.parent.1.node.rule1bRootDistance := by
  refine ⟨?_, ?_, ?_⟩
  · exact input.backwardParentDuplicate_mem_executableOfficialCIPChildren
      target.1.node current parentAtom targetActive htargetCurrent hdouble
  · exact sourceObservation2013_backwardParent_tie target.1.node
      certificate.parent.1.node current parentAtom tail 1 htargetHistory
      certificate.parent_active.1 certificate.parent_active.2 hparentHistory (by decide)
  · exact backwardParent_storedDistance_ne target.1.node certificate.parent.1.node
      current parentAtom tail 1 htargetHistory certificate.parent_active.1 hparentHistory
      (by decide)

/-! ## Rule-1a decisive route

When the two cursor nodes carry different root atomic numbers, nothing about Rule 1b (2013 or 2018)
needs to be known.  Rule 1a alone decides the constitutional comparison, and the cumulative
comparator is decided at that component before the descriptor projection. -/

/-- A strict constitutional difference propagates from the Rule-1b first sphere to the full
cumulative comparator.  This is the same algebraic fact as
`builtCumulativeKeys_constitutionalCompare_ne_eq`, restated for an arbitrary strict constitutional
decision. -/
theorem compareCumulative_eq_constitutional_of_constitutional_ne_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (constitutionalNe :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.eq) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      OfficialRuleMajorKey.compare left.constitutional right.constitutional := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  simpa [Ordering.byKey] using
    (ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
      (Ordering.byKey
        (fun key : input.LocalizedRerootCumulativeRule45Key => key.constitutional)
        OfficialRuleMajorKey.compare)
      (Ordering.byKey
        (fun key : input.LocalizedRerootCumulativeRule45Key => key.descriptor)
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
      left right
      (by simpa [Ordering.byKey] using constitutionalNe))

/-- **Rule-1a decisive cumulative keys.**

For any cumulative stage, target occurrence, dependency view and any two path-valid cursors whose
root atomic numbers differ, both cumulative keys exist at fuel `2 * (carrierFuel + 1)`, the
constitutional comparison is strict, and the cumulative comparator equals the constitutional
comparator.  No Rule-1b observation (2013 or 2018) is consulted. -/
theorem rule1aRootAtomicNumber_decisive
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid leftCursor)
    (rightValid : input.LocalizedRerootCursorValid rightCursor)
    (different :
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        leftCursor.occurrence.1.node)).1 ≠
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        rightCursor.occurrence.1.node)).1) :
    ∃ leftKey rightKey,
      input.buildLocalizedRerootCumulativeRule45Key? stage target view
          (2 * (carrierFuel + 1)) leftCursor = some leftKey ∧
      input.buildLocalizedRerootCumulativeRule45Key? stage target view
          (2 * (carrierFuel + 1)) rightCursor = some rightKey ∧
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional ≠
        Ordering.eq ∧
      input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
        OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional := by
  obtain ⟨leftKey, leftBuilt⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view leftCursor leftValid
  obtain ⟨rightKey, rightBuilt⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view rightCursor rightValid
  have leftHead :=
    (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rootObservation
      stage target view (2 * (carrierFuel + 1)) leftCursor leftKey leftBuilt).1
  have rightHead :=
    (input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rootObservation
      stage target view (2 * (carrierFuel + 1)) rightCursor rightKey rightBuilt).1
  have decisive :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftKey.constitutional.rule1a rightKey.constitutional.rule1a ≠ Ordering.eq := by
    rcases Nat.lt_or_gt_of_ne different with lower | higher
    · have strict :=
        MoleculeGraph.officialRuleMajorKey_compare_rule1a_lt_of_heads_lt
          leftHead rightHead lower
      rw [strict]
      decide
    · have strict :=
        MoleculeGraph.officialRuleMajorKey_compare_rule1a_gt_of_heads_gt
          leftHead rightHead higher
      rw [strict]
      decide
  have constitutional :=
    OfficialRuleMajorKey.compare_eq_rule1a_of_decisive decisive
  have constitutionalNe :
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional ≠
        Ordering.eq := by
    rw [constitutional]
    exact decisive
  refine ⟨leftKey, rightKey, leftBuilt, rightBuilt, constitutionalNe, ?_⟩
  exact input.compareCumulative_eq_constitutional_of_constitutional_ne_eq
    leftKey rightKey constitutionalNe

/-- **Parent-side versus outward-side Rule-1a route.**

For an active-simple non-root carrier occurrence `target`, its actual parent-frame certificate, and
every outward executable child identified by the appended sibling slot, *if* the parent's root atomic
number differs from the child's, then both cumulative keys exist and are separated strictly already
by Rule 1a; the cumulative comparator equals the constitutional comparison.  This bypasses the 2013
Rule-1b tie entirely whenever Rule 1a is derivable. -/
theorem parentSide_outwardChild_rule1a_decisive
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (_targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (stage : LocalizedCumulativeRule45Stage)
    (view : input.LocalizedDependencyView target) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        certificate.parent.1.node)).1 ≠
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          child.occurrence.1.node)).1 →
      ∃ parentKey childKey,
        input.buildLocalizedRerootCumulativeRule45Key? stage target view
            (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } = some parentKey ∧
        input.buildLocalizedRerootCumulativeRule45Key? stage target view
            (2 * (carrierFuel + 1)) child = some childKey ∧
        OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional ≠
          Ordering.eq ∧
        input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey =
          OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional := by
  intro child slot childPresent _childAddress different
  let targetCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := some certificate.parent }
  have parentValid : input.LocalizedRerootCursorValid
      { occurrence := certificate.parent, previous? := some target } := by
    change certificate.parent.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1
    exact certificate.parent_mem_neighborFrames input
  have childrenDerived :=
    input.executableLocalizedRerootChildren_declarative targetCursor
  have childValid : input.LocalizedRerootCursorValid child :=
    input.localizedRerootChild_valid targetCursor child
      (input.executableLocalizedRerootChildren targetCursor) childrenDerived childPresent
  exact input.rule1aRootAtomicNumber_decisive stage target view
    { occurrence := certificate.parent, previous? := some target } child
    parentValid childValid different

/-! ## Depth-dependency availability

The actual parent frame is not a depth dependency of the target: its carrier address is strictly
shorter.  The restricted dependency label therefore returns `none` on the parent cursor.  An
outward executable child has an appended address, so it *is* a depth dependency and its restricted
label reads the unrestricted earlier-stage state. -/

/-- The actual parent frame is not a `LocalizedDepthDependency` of its child target: the target is
strictly deeper, not the parent. -/
theorem parentFrame_not_depthDependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (certificate : input.LocalizedParentFrameHistory target) :
    ¬ input.LocalizedDepthDependency certificate.parent target := by
  intro dependency
  have length := certificate.parent_address_length input
  have deeper : target.1.address.length < certificate.parent.1.address.length := dependency.2
  omega

/-- The actual parent cursor is never read through the restricted dependency view: its label is
`none`. -/
theorem parentCursor_dependencyLabel_eq_none
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (certificate : input.LocalizedParentFrameHistory target)
    (view : input.LocalizedDependencyView target) :
    input.localizedDependencyLabel target view
      ({ occurrence := certificate.parent, previous? := some target } :
        input.LocalizedRerootCursor fuel) = none := by
  unfold localizedDependencyLabel
  rw [dif_neg (input.parentFrame_not_depthDependency target certificate)]

/-- An outward executable child with appended sibling address is a strict depth dependency of the
context occurrence.  Its root is the context root (`localizedRerootChildren_root_eq`) and its
address is one slot longer. -/
theorem outwardChild_depthDependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (context child : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (derived : input.DeclarativeLocalizedRerootChildren context children)
    (present : child ∈ children)
    (slot : Nat)
    (childAddress : child.occurrence.1.address = context.occurrence.1.address ++ [slot]) :
    input.LocalizedDepthDependency child.occurrence context.occurrence := by
  refine ⟨?_, ?_⟩
  · exact input.localizedRerootChildren_root_eq context child children derived present
  · rw [childAddress, List.length_append]
    simp

/-- On an outward executable child, the restricted dependency label reads the unrestricted state of
the earlier constitutional stage: the child is a genuine depth dependency, so no dependency
information is lost. -/
theorem outwardChild_dependencyLabel_eq_state
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (context : input.LocalizedRerootCursor fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (child : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (derived : input.DeclarativeLocalizedRerootChildren context children)
    (present : child ∈ children)
    (slot : Nat)
    (childAddress : child.occurrence.1.address = context.occurrence.1.address ++ [slot]) :
    input.localizedDependencyLabel context.occurrence
        (input.localizedDependencyView state context.occurrence) child =
      state child.occurrence :=
  localizedDependencyLabel_eq_state_of_dependency input context.occurrence state child
    (input.outwardChild_depthDependency context child children derived present slot
      childAddress)

end CertifiedLocalizedCIPInput

/-! ## Concrete allene witness over `Fin 3`

The graph is the carbon skeleton `0 = 1 = 2` (double bonds 0--1 and 1--2).  Rooting at the
middle carbon 1 and extending to 0 gives the target; extending the target back to 1 with copy index
`1` is the backward multiple-bond duplicate of the parent atom.  Its 2013 observation equals the
root's (both `0`), while the stored observations are `1` and `0`.  This is a node-level witness; it
is not claimed to arise from a `CertifiedLocalizedCIPInput`. -/

namespace Source2013AlleneWitness

abbrev Atom := Fin 3

/-- Bond order of the allene skeleton: `2` exactly on the pairs `{0,1}` and `{1,2}`. -/
def alleneBond (u v : Atom) : ℕ :=
  if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) then 2
  else 0

/-- The concrete finite molecular graph.  All atoms are carbon; all masses are zero. -/
def graph : MoleculeGraph Atom where
  atomZ := fun _ => 6
  atomMass := fun _ => 0
  bond := alleneBond
  bond_symm := by decide
  bond_self := by decide

/-- Root at the middle carbon `1`. -/
def root : OfficialCIPNode Atom := OfficialCIPNode.root 1

/-- Target: the outward carbon `0`, reached from `1` by the zero-index real copy. -/
def target : OfficialCIPNode Atom := root.extend 0 0

/-- Backward multiple-bond duplicate of the parent atom `1`, copy index `1`. -/
def backwardParent : OfficialCIPNode Atom := target.extend 1 1

theorem graph_double : graph.bond 0 1 = 2 := by decide

theorem graph_adjacent : graph.Adj 0 1 := by
  unfold MoleculeGraph.Adj
  decide

theorem root_active : root.ActiveSimple := by
  constructor
  · rfl
  · simp [root, OfficialCIPNode.root]

/-- The 2013 observations tie: both the backward parent duplicate and the real parent root read
sphere `0`. -/
theorem tie :
    sourceObservation2013 backwardParent = sourceObservation2013 root := by
  exact sourceObservation2013_backwardParent_tie target root (0 : Atom) (1 : Atom) [] 1
    rfl root_active.1 root_active.2 rfl (by decide)

theorem source_tie_value : sourceObservation2013 backwardParent = 0 := by decide

theorem parent_source_value : sourceObservation2013 root = 0 := by decide

theorem backwardParent_stored : backwardParent.rule1bRootDistance = 1 := by decide

theorem root_stored : root.rule1bRootDistance = 0 := by decide

/-- The stored (2018) observations separate where the 2013 observations tie. -/
theorem stored_separates :
    backwardParent.rule1bRootDistance ≠ root.rule1bRootDistance := by
  rw [backwardParent_stored, root_stored]
  decide

end Source2013AlleneWitness

end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.sourceObservation2013_backwardParent_tie
assert_kernel_only TetraStereo.OneCenter.backwardParent_storedDistance_ne
assert_kernel_only TetraStereo.OneCenter.sourceObservation2013_extend_ne_realParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sourceObservation2013_executableChild_ne_realParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.backwardParentDuplicate_mem_executableOfficialCIPChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sourceBound_backwardParent_obstruction
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareCumulative_eq_constitutional_of_constitutional_ne_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rule1aRootAtomicNumber_decisive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentSide_outwardChild_rule1a_decisive
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentFrame_not_depthDependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentCursor_dependencyLabel_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardChild_depthDependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardChild_dependencyLabel_eq_state
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.graph_double
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.graph_adjacent
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.root_active
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.tie
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.source_tie_value
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.parent_source_value
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.backwardParent_stored
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.root_stored
assert_kernel_only TetraStereo.OneCenter.Source2013AlleneWitness.stored_separates
