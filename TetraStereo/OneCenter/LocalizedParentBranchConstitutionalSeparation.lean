/-
  Localized parent-branch constitutional separation.

  This module proves the primitive actual-child separation fact needed to justify the omission of
  a locally nondeeper label: for an active-simple official digraph target whose stored history is
  `current :: parentAtom :: tail`, every *actual executable child* of the target carries a Rule-1b
  root distance distinct from the parent's Rule-1b root distance.

  The parent is a real atom with history `parentAtom :: tail`, so its total Rule-1b observation is
  its own depth `tail.length`.  The three executable child cases separate as follows:

  * a fresh zero copy is a real child one sphere beyond the target, hence distance
    `tail.length + 2`;
  * a positive copy is a multiple-bond duplicate attached to the target, hence distance
    `tail.length + 1`;
  * a visited zero copy is a ring duplicate whose stored distance is a reversed-history occurrence
    index.  No self bond excludes `current`, and the zero-copy parent filter excludes `parentAtom`,
    so the represented atom occurs in `tail`; the reversed-history first index therefore lies
    strictly below `tail.length`, which is exactly the parent's distance.

  No direction is claimed for the general child: a ring duplicate is *nearer* than the parent
  (`<`), while fresh and multiple-bond children are farther (`>`).  The exported primitive only
  asserts the strict decision `≠`, which is all the constitutional comparison requires to rule out
  a tie at this Rule-1b coordinate.  This is a constructor invariant over the actual
  `OfficialCIPNode.extend` / `executableOfficialCIPChildren` definitions; it is not a restatement
  of the desired comparison conclusion.

  The distance profile used throughout is the implemented Hanson-proposed total `rule1bRootDistance`
  (`Rule1bSourceProfileFidelity`), not the separate 2013 represented-atom observation.
-/

import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.OneCenter.Rule1bSourceProfileFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace LocalizedParentBranchConstitutionalSeparation

/-! ## Path-index bound lemmas -/

/-- `firstIndexOf?` returns the least index at which its target occurs: any other occurrence index
is at least the returned index. -/
private theorem firstIndexOf?_eq_some_le_of_getElem?_eq_some {α : Type*} [DecidableEq α]
    (target : α) :
    ∀ (values : List α) (i j : ℕ),
      firstIndexOf? target values = some i →
      values[j]? = some target → i ≤ j
  | [], i, j, h, _ => by simp [firstIndexOf?] at h
  | value :: values, i, j, h, hget => by
      unfold firstIndexOf? at h
      by_cases head : value = target
      · simp only [head, ↓reduceIte] at h
        have hi : i = 0 := (Option.some.inj h).symm
        subst i
        exact Nat.zero_le j
      · simp only [head, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨i', htail, rfl⟩ := h
        cases j with
        | zero =>
            have hv : value = target := by
              simpa using hget
            exact (head hv).elim
        | succ j' =>
            have hget' : values[j']? = some target := by
              simpa using hget
            have hle := firstIndexOf?_eq_some_le_of_getElem?_eq_some target
              values i' j' htail hget'
            exact Nat.succ_le_succ hle

/-- If the searched atom occurs inside a prefix, then its first occurrence in `pre ++ suffix`
lies strictly before the prefix ends. -/
private theorem firstIndexOf?_eq_some_lt_prefix_length_of_mem {α : Type*} [DecidableEq α]
    (target : α) (pre suffix : List α) (i : ℕ)
    (hmem : target ∈ pre)
    (hindex : firstIndexOf? target (pre ++ suffix) = some i) :
    i < pre.length := by
  obtain ⟨j, hprefixIndex⟩ := Rule1bSourceProfile.firstIndexOf?_eq_some_of_mem target hmem
  have hprefixGet : pre[j]? = some target :=
    Rule1bSourceProfile.firstIndexOf?_eq_some_imp_getElem? target pre j hprefixIndex
  rcases List.getElem?_eq_some_iff.mp hprefixGet with ⟨hj_lt, _⟩
  have hbigGet : (pre ++ suffix)[j]? = some target := by
    rw [List.getElem?_append_left hj_lt, hprefixGet]
  have hle : i ≤ j :=
    firstIndexOf?_eq_some_le_of_getElem?_eq_some target (pre ++ suffix) i j hindex hbigGet
  exact Nat.lt_of_le_of_lt hle hj_lt

/-! ## Ring-duplicate children read a sphere strictly below the parent -/

/-- A visited zero-copy child of `target` is a ring duplicate whose stored Rule-1b distance is the
reversed-history index of the represented atom.  Under the target history shape
`current :: parentAtom :: tail`, the represented atom lies in `tail`, so that index is strictly
below `tail.length`, which is exactly the real parent's Rule-1b distance. -/
private theorem ringChild_rule1bRootDistance_lt_parent
    (input : CertifiedLocalizedCIPInput)
    (target parent : OfficialCIPNode input.Atom)
    (current parentAtom next : input.Atom)
    (tail : List input.Atom)
    (htargetHistory : target.history = current :: parentAtom :: tail)
    (hparentProvenance : parent.provenance = OfficialCIPNodeProvenance.realAtom)
    (hparentHistory : parent.history = parentAtom :: tail)
    (hnextMem : next ∈ target.history)
    (hnextInTail : next ∈ tail) :
    (target.extend next 0).rule1bRootDistance < parent.rule1bRootDistance := by
  have hparentDepth : parent.depth = tail.length := by
    simp [OfficialCIPNode.depth, hparentHistory]
  have hparentDistance : parent.rule1bRootDistance = tail.length := by
    simp [OfficialCIPNode.rule1bRootDistance, hparentProvenance, hparentDepth]
  obtain ⟨index, hindex⟩ := Rule1bSourceProfile.firstIndexOf?_eq_some_of_mem next
    (List.mem_reverse.mpr hnextMem)
  have hrev : target.history.reverse = tail.reverse ++ [parentAtom, current] := by
    rw [htargetHistory]
    simp
  have hindexBound : index < tail.length := by
    rw [hrev] at hindex
    have hmemReverse : next ∈ tail.reverse := List.mem_reverse.mpr hnextInTail
    simpa using (firstIndexOf?_eq_some_lt_prefix_length_of_mem next tail.reverse
      [parentAtom, current] index hmemReverse hindex)
  have hchildDistance : (target.extend next 0).rule1bRootDistance = index := by
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.duplicateRootDistance,
      hnextMem, hindex]
  rw [hchildDistance, hparentDistance]
  exact hindexBound

/-! ## The primitive: every actual child separates from the parent -/

/-- Primitive parent/child Rule-1b separation.

Given an active-simple target with `target.current? = some current` and
`target.history = current :: parentAtom :: tail`, and a real parent with
`parent.history = parentAtom :: tail`, every actual child emitted by
`executableOfficialCIPChildren target` has a Rule-1b root distance different from the parent's.
Fresh real children and multiple-bond copies sit farther; ring-duplicate children sit strictly
nearer.  Only the strict decision `≠` is asserted. -/
theorem parentRule1bDistance_ne_childRule1bDistance
    (input : CertifiedLocalizedCIPInput)
    (target parent : OfficialCIPNode input.Atom)
    (current parentAtom : input.Atom)
    (tail : List input.Atom)
    (htargetSimple : target.ActiveSimple)
    (htargetCurrent : target.current? = some current)
    (htargetHistory : target.history = current :: parentAtom :: tail)
    (hparentProvenance : parent.provenance = OfficialCIPNodeProvenance.realAtom)
    (hparentHistory : parent.history = parentAtom :: tail) :
    ∀ child, child ∈ input.executableOfficialCIPChildren target →
      child.rule1bRootDistance ≠ parent.rule1bRootDistance := by
  have htargetProvenance : target.provenance = OfficialCIPNodeProvenance.realAtom :=
    htargetSimple.1
  have htargetNondup : target.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, htargetProvenance]
  have htargetParent? : target.parent? = some parentAtom := by
    simp [OfficialCIPNode.parent?, htargetHistory]
  have hparentDepth : parent.depth = tail.length := by
    simp [OfficialCIPNode.depth, hparentHistory]
  have hparentDistance : parent.rule1bRootDistance = tail.length := by
    simp [OfficialCIPNode.rule1bRootDistance, hparentProvenance, hparentDepth]
  have htargetDepth : target.depth = tail.length + 1 := by
    simp [OfficialCIPNode.depth, htargetHistory]
  intro child hchild
  have hchildInMap :
      child ∈ (input.executableOfficialChildCopies target).map
        (fun copy => target.extend copy.1 copy.2) := by
    rw [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
      if_neg (by simpa using htargetNondup)] at hchild
    exact hchild
  rcases List.mem_map.mp hchildInMap with ⟨copy, hcopy, hchildEq⟩
  rcases copy with ⟨next, copyIndex⟩
  subst child
  have hcopyInChildCopies : (next, copyIndex) ∈ input.executableOfficialChildCopies target :=
    hcopy
  simp only [CertifiedLocalizedCIPInput.executableOfficialChildCopies, htargetCurrent,
    htargetParent?] at hcopyInChildCopies
  have hcopyFilter := List.mem_filter.mp hcopyInChildCopies
  have hcopyNeighbor : (next, copyIndex) ∈ input.executableOfficialNeighborCopies current :=
    hcopyFilter.1
  have hadj : input.moleculeGraph.Adj current next :=
    input.adj_of_mem_executableOfficialNeighborCopies current next copyIndex hcopyNeighbor
  have hnextNeCurrent : next ≠ current := by
    intro hnc
    subst next
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at hadj
  by_cases hz : copyIndex = 0
  · subst copyIndex
    have hnextNeParent : next ≠ parentAtom := by
      intro hnp
      subst next
      simp at hcopyInChildCopies
    by_cases hnextMem : next ∈ target.history
    · have hnextInTail : next ∈ tail := by
        have hnextHistory : next ∈ current :: parentAtom :: tail := by
          simpa [htargetHistory] using hnextMem
        rcases List.mem_cons.mp hnextHistory with hc | hpaOrTail
        · exact (hnextNeCurrent hc).elim
        · rcases List.mem_cons.mp hpaOrTail with hpa | htail
          · exact (hnextNeParent hpa).elim
          · exact htail
      exact Nat.ne_of_lt (ringChild_rule1bRootDistance_lt_parent input target parent current
        parentAtom next tail htargetHistory hparentProvenance hparentHistory hnextMem hnextInTail)
    · have hchildProvenance : (target.extend next 0).provenance =
          OfficialCIPNodeProvenance.realAtom := by
        rw [OfficialCIPNode.extend_provenance]
        exact OfficialCIPNode.childProvenance_real target next hnextMem
      have hchildDistance : (target.extend next 0).rule1bRootDistance = tail.length + 2 := by
        rw [OfficialCIPNode.rule1bRootDistance, hchildProvenance]
        simp [OfficialCIPNode.depth, htargetHistory]
      rw [hchildDistance, hparentDistance]
      omega
  · have hchildDistance : (target.extend next copyIndex).rule1bRootDistance = tail.length + 1 := by
      simp [OfficialCIPNode.rule1bRootDistance, hz, htargetDepth]
    rw [hchildDistance, hparentDistance]
    omega

end LocalizedParentBranchConstitutionalSeparation
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.LocalizedParentBranchConstitutionalSeparation.parentRule1bDistance_ne_childRule1bDistance
