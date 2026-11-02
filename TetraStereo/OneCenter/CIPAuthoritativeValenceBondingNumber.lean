import TetraStereo.OneCenter.CIPAuthoritativeMoleculeCursorRanking
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPValenceBondingNumber

open RawMolecule
open AuthoritativeCIPMoleculeCursorRanking

/-!
# Deriving the CIP bonding-number boundary from certified valence

The molecule-level termination theorem is stated using the local canonical-tree form of bonding
number six.  This module proves that the existing parser-level `ValenceOK` certificate implies that
condition.  Multiple-bond duplicates are counted by bond order.  At every non-root occurrence the
single real copy of the incoming bond is removed before forward children are formed, exactly
offsetting the recovered parent occurrence.
-/

/-- The P/S oxido root convention can only lower the raw molecular bond order. -/
theorem canonicalBondOrder_le_bondOrder (mol : RawMolecule) (node : CanonicalBranchNode)
    (next : Nat) (headEq : node.history.head? = some node.atom) :
    mol.canonicalBondOrder node next ≤ mol.bondOrder node.atom next := by
  unfold RawMolecule.canonicalBondOrder
  cases historyEq : node.history with
  | nil => rfl
  | cons current rest =>
      cases rest with
      | nil => rfl
      | cons center tail =>
          cases tail with
          | nil =>
              by_cases suppressed : next == center &&
                  mol.isTrigonalPyramidalOxidoRootEdge center current
              · simp only [suppressed, ↓reduceIte]
                have nextEq : next = center := by
                  have parts : next = center ∧
                      mol.isTrigonalPyramidalOxidoRootEdge center current = true := by
                    simpa only [Bool.and_eq_true, beq_iff_eq] using suppressed
                  exact parts.1
                have edge : mol.bondOrder center current = 2 := by
                  unfold RawMolecule.isTrigonalPyramidalOxidoRootEdge at suppressed
                  split at suppressed <;> simp_all
                have currentEq : node.atom = current := by
                  simpa [historyEq] using headEq.symm
                rw [currentEq, nextEq, mol.bondOrder_symm current center, edge]
                omega
              · simp [suppressed]
          | cons another tail => rfl

/-- Every positive raw incident bond remains positive under the root-edge convention. -/
theorem canonicalBondOrder_pos_of_bondOrder_pos (mol : RawMolecule)
    (node : CanonicalBranchNode) (next : Nat)
    (positive : 0 < mol.bondOrder node.atom next) :
    0 < mol.canonicalBondOrder node next := by
  unfold RawMolecule.canonicalBondOrder
  cases node.history with
  | nil => exact positive
  | cons current rest =>
      cases rest with
      | nil => exact positive
      | cons center tail =>
          cases tail with
          | nil =>
              by_cases suppressed : next == center &&
                  mol.isTrigonalPyramidalOxidoRootEdge center current
              · simp [suppressed]
              · simp [suppressed, positive]
          | cons another tail => exact positive

private def canonicalCopiesForBond (mol : RawMolecule) (node : CanonicalBranchNode)
    (bond : RawBond) : List (Nat × Nat) :=
  let next? :=
    if bond.source == node.atom then some bond.target
    else if bond.target == node.atom then some bond.source
    else none
  match next? with
  | none => []
  | some next =>
      (List.range (mol.canonicalBondOrder node next)).map fun copyIndex => (next, copyIndex)

private def incidentContribution (atom : Nat) (bond : RawBond) : Nat :=
  if bond.source == atom || bond.target == atom then bond.kind.order else 0

private theorem canonicalCopiesForBond_length_le (mol : RawMolecule)
    (node : CanonicalBranchNode) (headEq : node.history.head? = some node.atom)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (bond : RawBond) (bondMember : bond ∈ mol.bonds) :
    (canonicalCopiesForBond mol node bond).length ≤ incidentContribution node.atom bond := by
  unfold canonicalCopiesForBond incidentContribution
  by_cases sourceEq : bond.source == node.atom
  · have connects : bond.connects node.atom bond.target = true := by
      simp [RawBond.connects, sourceEq]
    have orderEq := mol.bondOrder_eq_kind_of_mem_connects wellFormed unique
      bondMember connects
    simp only [sourceEq, ↓reduceIte, Bool.true_or, List.length_map, List.length_range]
    rw [← orderEq]
    exact canonicalBondOrder_le_bondOrder mol node bond.target headEq
  · have sourceFalse : (bond.source == node.atom) = false :=
      Bool.eq_false_of_not_eq_true sourceEq
    by_cases targetEq : bond.target == node.atom
    · have connects : bond.connects node.atom bond.source = true := by
        simp [RawBond.connects, targetEq]
      have orderEq := mol.bondOrder_eq_kind_of_mem_connects wellFormed unique
        bondMember connects
      simp only [sourceFalse, Bool.false_eq_true, ↓reduceIte, targetEq, Bool.or_true,
        List.length_map, List.length_range]
      rw [← orderEq]
      exact canonicalBondOrder_le_bondOrder mol node bond.source headEq
    · have targetFalse : (bond.target == node.atom) = false :=
        Bool.eq_false_of_not_eq_true targetEq
      simp [sourceFalse, targetFalse]

private theorem eraseCanonicalParentCopy_length_le (parent : Nat)
    (copies : List (Nat × Nat)) :
    (eraseCanonicalParentCopy parent copies).length ≤ copies.length := by
  induction copies with
  | nil => simp [eraseCanonicalParentCopy]
  | cons copy copies ih =>
      unfold eraseCanonicalParentCopy
      split
      · simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        exact Nat.succ_le_succ ih

private theorem eraseCanonicalParentCopy_length_lt_of_mem (parent : Nat)
    (copies : List (Nat × Nat)) (member : (parent, 0) ∈ copies) :
    (eraseCanonicalParentCopy parent copies).length < copies.length := by
  induction copies with
  | nil => simp at member
  | cons copy copies ih =>
      unfold eraseCanonicalParentCopy
      by_cases erased : copy.1 == parent && copy.2 == 0
      · simp [erased]
      · have tailMember : (parent, 0) ∈ copies := by
          simp only [List.mem_cons] at member
          rcases member with copyEq | member
          · subst copy
            simp at erased
          · exact member
        simp only [erased, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        exact Nat.succ_lt_succ (ih tailMember)

private theorem flatMap_canonicalCopies_length_le (mol : RawMolecule)
    (node : CanonicalBranchNode) (headEq : node.history.head? = some node.atom)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (bonds : List RawBond) (subset : ∀ bond, bond ∈ bonds → bond ∈ mol.bonds) :
    (bonds.flatMap (canonicalCopiesForBond mol node)).length ≤
      (bonds.map (incidentContribution node.atom)).sum := by
  induction bonds with
  | nil => simp
  | cons bond bonds ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (canonicalCopiesForBond_length_le mol node headEq wellFormed unique bond
          (subset bond (by simp)))
        (ih (fun other member => subset other (by simp [member])))

private theorem foldl_incident_eq (atom : Nat) (bonds : List RawBond) (total : Nat) :
    bonds.foldl
        (fun total bond =>
          if bond.source == atom || bond.target == atom then total + bond.kind.order else total)
        total =
      total + (bonds.map (incidentContribution atom)).sum := by
  induction bonds generalizing total with
  | nil => simp
  | cons bond bonds ih =>
      simp only [List.foldl_cons]
      rw [ih]
      unfold incidentContribution
      split <;> simp_all [Nat.add_assoc]

private theorem incidentBondOrderSum_eq_sum (mol : RawMolecule) (atom : Nat) :
    mol.incidentBondOrderSum atom =
      (mol.bonds.map (incidentContribution atom)).sum := by
  unfold RawMolecule.incidentBondOrderSum
  rw [foldl_incident_eq]
  simp

/-- Canonical duplicate-copy count never exceeds the raw incident bond-order sum. -/
theorem canonicalChildCopies_length_le_incidentBondOrderSum
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (headEq : node.history.head? = some node.atom)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique) :
    (mol.canonicalChildCopies node).length ≤ mol.incidentBondOrderSum node.atom := by
  unfold RawMolecule.canonicalChildCopies
  change (eraseCanonicalParentCopy node.parent
      (mol.bonds.flatMap (canonicalCopiesForBond mol node))).length ≤ _
  exact (eraseCanonicalParentCopy_length_le _ _).trans
    ((flatMap_canonicalCopies_length_le mol node headEq wellFormed unique mol.bonds
      (fun _ member => member)).trans_eq (incidentBondOrderSum_eq_sum mol node.atom).symm)

/-- Every valence admitted by the current parser's element table is at most six. -/
theorem allowedValence_le_six (atom : AtomSpec) (allowed : Nat)
    (member : allowed ∈ atom.allowedValences) : allowed ≤ 6 := by
  cases atom with
  | mk element isotope charge explicit aromatic tetrahedral =>
      cases element <;> cases aromatic <;>
        simp_all [AtomSpec.allowedValences, Element.allowedValences]
      all_goals try split at member
      all_goals try simp_all
      all_goals aesop

/-- The parser valence certificate bounds every real atom's incident bond-order sum by six. -/
theorem incidentBondOrderSum_le_six_of_valence
    (mol : RawMolecule) (valence : mol.ValenceOK) (atom : Fin mol.atomCount) :
    mol.incidentBondOrderSum atom.val ≤ 6 := by
  let spec := mol.atoms.get atom
  have lookup : mol.atomAt? atom.val = some spec := by
    exact listGet?_eq_some_get mol.atoms atom
  rcases valence atom.val spec lookup with ⟨allowed, allowedMember, usedLe⟩
  have allowedLe := allowedValence_le_six spec allowed allowedMember
  unfold RawMolecule.usedValenceAt at usedLe
  simp only [lookup] at usedLe
  exact (Nat.le_add_left _ _).trans (usedLe.trans allowedLe)

private theorem canonicalChildren_parent_eq {mol : RawMolecule}
    {parent child : CanonicalBranchNode}
    (member : child ∈ mol.canonicalChildren parent) : child.parent = parent.atom := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    rcases member with ⟨copy, _copyMember, rfl⟩
    rfl

private theorem child_parent_copy_mem_rawCopies {mol : RawMolecule}
    {parent child : CanonicalBranchNode}
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (member : child ∈ mol.canonicalChildren parent) :
    (child.parent, 0) ∈ mol.bonds.flatMap (canonicalCopiesForBond mol child) := by
  unfold RawMolecule.canonicalChildren at member
  by_cases leaf : parent.forcedLeaf
  · simp [leaf] at member
  · simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map] at member
    rcases member with ⟨copy, copyMember, childEq⟩
    rcases mol.canonicalChildCopies_source parent copy copyMember with
      ⟨bond, bondMember, endpoints, _copyBound⟩
    have childAtom : child.atom = copy.1 := by
      rw [← childEq]
    have childParent : child.parent = parent.atom := canonicalChildren_parent_eq
      (mol := mol) (parent := parent) (child := child) (by
        unfold RawMolecule.canonicalChildren
        simp only [leaf, Bool.false_eq_true, ↓reduceIte, List.mem_map]
        exact ⟨copy, copyMember, childEq⟩)
    have connects : bond.connects child.atom child.parent = true := by
      rw [childAtom, childParent]
      rcases endpoints with forward | reverse
      · simp [RawBond.connects, forward.1, forward.2]
      · simp [RawBond.connects, reverse.1, reverse.2]
    have orderEq := mol.bondOrder_eq_kind_of_mem_connects wellFormed unique
      bondMember connects
    have rawPositive : 0 < mol.bondOrder child.atom child.parent := by
      rw [orderEq]
      cases bond.kind <;> decide
    have canonicalPositive : 0 < mol.canonicalBondOrder child child.parent :=
      canonicalBondOrder_pos_of_bondOrder_pos mol child child.parent rawPositive
    apply List.mem_flatMap.2
    refine ⟨bond, bondMember, ?_⟩
    unfold canonicalCopiesForBond
    by_cases sourceEq : bond.source == child.atom
    · have nextEq : bond.target = child.parent := by
        rcases endpoints with forward | reverse
        · have sourceAtom := beq_iff_eq.mp sourceEq
          have self : bond.source = bond.target :=
            sourceAtom.trans (childAtom.trans forward.2.symm)
          exact False.elim ((wellFormed bond bondMember).2.2 self)
        · rw [reverse.1, childParent]
      simp only [sourceEq, ↓reduceIte]
      rw [nextEq]
      apply List.mem_map.2
      exact ⟨0, List.mem_range.mpr canonicalPositive, rfl⟩
    · have sourceFalse : (bond.source == child.atom) = false :=
        Bool.eq_false_of_not_eq_true sourceEq
      have targetEq : (bond.target == child.atom) = true := by
        rcases endpoints with forward | reverse
        · exact beq_iff_eq.mpr (forward.2.trans childAtom.symm)
        · have sourceAtom : bond.source = child.atom := reverse.2.trans childAtom.symm
          exact False.elim (sourceEq (beq_iff_eq.mpr sourceAtom))
      have nextEq : bond.source = child.parent := by
        rcases endpoints with forward | reverse
        · rw [forward.1, childParent]
        · have sourceAtom : bond.source = child.atom := by
            rw [reverse.2, ← childAtom]
          exact False.elim (sourceEq (beq_iff_eq.mpr sourceAtom))
      simp only [sourceFalse, Bool.false_eq_true, ↓reduceIte, targetEq]
      rw [nextEq]
      apply List.mem_map.2
      exact ⟨0, List.mem_range.mpr canonicalPositive, rfl⟩

/-- Structural admission, unique bond records, and the existing valence certificate imply the
local canonical-tree form of the P-92 bonding-number-six boundary at every center. -/
theorem canonicalCenterBondingNumberSix_of_valence
    (mol : RawMolecule) (center : Nat) (centerBound : center < mol.atomCount)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (valence : mol.ValenceOK) :
    CanonicalCenterBondingNumberSix mol center := by
  intro node generated
  cases generated with
  | root =>
      have headEq : (canonicalCenterRoot center).history.head? =
          some (canonicalCenterRoot center).atom := by
        simp [canonicalCenterRoot]
      have copiesLe := canonicalChildCopies_length_le_incidentBondOrderSum
        mol (canonicalCenterRoot center) headEq wellFormed unique
      have incidentLe := incidentBondOrderSum_le_six_of_valence mol valence
        (⟨center, centerBound⟩ : Fin mol.atomCount)
      change mol.incidentBondOrderSum center ≤ 6 at incidentLe
      simpa [canonicalCenterRoot, canonicalOriginalParent?, RawMolecule.canonicalChildren,
        CanonicalBranchNode.forcedLeaf] using copiesLe.trans incidentLe
  | @child parent node parentGenerated member =>
      have nodeGenerated := CanonicalCenterTreeNode.child parentGenerated member
      have recovered := canonicalOriginalParent?_eq_some_of_child parentGenerated member
      by_cases leaf : node.forcedLeaf = true
      · simp [recovered, RawMolecule.canonicalChildren, leaf]
      · have notLeaf : node.forcedLeaf = false := Bool.eq_false_of_not_eq_true leaf
        have nodeBound : node.atom < mol.atomCount :=
          child_atom_lt_atomCount wellFormed member
        have incidentLe := incidentBondOrderSum_le_six_of_valence mol valence
          (⟨node.atom, nodeBound⟩ : Fin mol.atomCount)
        change mol.incidentBondOrderSum node.atom ≤ 6 at incidentLe
        have headEq := nodeGenerated.history_head
        have rawLe :
            (mol.bonds.flatMap (canonicalCopiesForBond mol node)).length ≤
              mol.incidentBondOrderSum node.atom := by
          exact (flatMap_canonicalCopies_length_le mol node headEq wellFormed unique mol.bonds
            (fun _ bondMember => bondMember)).trans_eq
              (incidentBondOrderSum_eq_sum mol node.atom).symm
        have rawMember : (node.parent, 0) ∈
            mol.bonds.flatMap (canonicalCopiesForBond mol node) :=
          child_parent_copy_mem_rawCopies wellFormed unique member
        have erasedLt :
            (eraseCanonicalParentCopy node.parent
                (mol.bonds.flatMap (canonicalCopiesForBond mol node))).length <
              (mol.bonds.flatMap (canonicalCopiesForBond mol node)).length :=
          eraseCanonicalParentCopy_length_lt_of_mem node.parent _ rawMember
        have childCopiesLt :
            (mol.canonicalChildCopies node).length <
              (mol.bonds.flatMap (canonicalCopiesForBond mol node)).length := by
          unfold RawMolecule.canonicalChildCopies
          exact erasedLt
        simp only [recovered, Option.toList_some, List.length_singleton,
          RawMolecule.canonicalChildren, notLeaf, Bool.false_eq_true, ↓reduceIte,
          List.length_map]
        omega

/-- Every certified normalization result supplies bonding number six at every real center; callers
do not need to provide this applicability proof separately. -/
theorem CertifiedChemistryNormalizationResult.canonicalCenterBondingNumberSix
    (certified : CertifiedChemistryNormalizationResult)
    (center : Nat) (centerBound : center < certified.result.parsed.atomCount) :
    CanonicalCenterBondingNumberSix certified.result.parsed center :=
  canonicalCenterBondingNumberSix_of_valence certified.result.parsed center centerBound
    certified.admissible.1 certified.admissible.2 certified.valenceOK

end TetraStereo.OneCenter.AuthoritativeCIPValenceBondingNumber
