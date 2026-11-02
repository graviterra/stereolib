import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import TetraStereo.KernelOnly
import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeOccurrenceFrame

set_option autoImplicit false

/-!
# Public/localized child-enumeration transport on the shared certified domain

The public source-canonical carrier of `AuthoritativeChemicalInput` expands each official CIP node
by `SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt`: ordinary neighbor copies in
`List.finRange atomCount` order, followed by (at most) one virtual mancude duplicate.

The localized runtime carrier of `CertifiedLocalizedCIPInput` expands the same node by
`CertifiedLocalizedCIPInput.executableOfficialCIPChildren`: graph-neighbor copies in
`Finset.sort` order, with no virtual branch.

This module proves the *exact list equality* of the two enumerations for every certified localized
input and every official CIP node:

```lean
theorem CertifiedLocalizedCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom) :
    input.certified.input.molecule.aromaticCanonicalOfficialCIPChildrenAt
        input.certified.input.molecule.atomCount node
      = input.executableOfficialCIPChildren node
```

Order, not merely permutation, is the claim: occurrence addresses are built from `zipIdx` slots, so
the child enumeration order is semantically observable.

## Proof route (all steps unconditional on the localized admission domain)

1. `input.graphReady.2.2.2.1 : LocalizedCovalentPairsOnly`, hence
   `aromaticPairEdges = []` and `aromaticCanonicalBondOrder = localizedBondOrder` (shipped lemmas),
   so the virtual mancude branch of `aromaticCanonicalOfficialCIPChildrenAt` is `[]`
   (`aromaticCanonicalMancudeRepresentativeAt? = none`).
2. `input.moleculeGraph.bond` is `localizedBondOrder` definitionally, so the per-copy functions of
   the two enumerations agree.
3. The neighbor index list of the localized side,
   `(neighborFinset atom).sort (· ≤ ·) = (Finset.univ.filter (0 < bond atom ·)).sort (· ≤ ·)`,
   is `List.finRange atomCount` filtered to positive-degree neighbors (Mathlib
   `List.toFinset_sort` plus `Fin.sort_univ`; private helper below).
4. Zero-degree `finRange` entries contribute `[]` to the public `flatMap`
   (`List.flatMap_eq_filter_flatMap`; private helper below), so the two `flatMap`s agree exactly.
5. The parent-copy filter `fun copy => !(copy.1 == parent && copy.2 == 0)` is applied identically
   on both sides, including at the root (`parent? = none`).

No assumption about, or construction of, any graph other than `input.moleculeGraph` is used, and no
child equality is postulated.
-/

namespace TetraStereo.OneCenter

/-! ## Two generic enumeration facts (private to this module) -/

/-- A zero-contribution filter can be pushed into a `flatMap` without changing the result. -/
private theorem flatMap_eq_filter_flatMap_f88 {α β : Type*} (l : List α) (p : α → Bool)
    (f : α → List β) (h : ∀ x, p x = false → f x = []) :
    l.flatMap f = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      cases hp : p x with
      | false =>
          have hx : f x = [] := h x hp
          simp [List.flatMap_cons, hp, hx, ih]
      | true =>
          simp [List.flatMap_cons, hp, ih]

/-- Sorting a `Finset` of `Fin n` elements that was obtained by filtering `univ` is the same as
filtering `List.finRange n`, in ascending order.  Both sides enumerate `Fin n` increasingly; the
left is `Finset.sort`, the right `List.filter` of `List.finRange`. -/
private theorem sort_univ_filter_finRange_f88 {n : Nat} (p : Fin n → Bool) :
    (Finset.univ.filter (fun x => p x = true)).sort (fun x y : Fin n => x ≤ y) =
      (List.finRange n).filter p := by
  have hnodup : ((List.finRange n).filter p).Nodup :=
    List.Nodup.filter p (List.nodup_finRange n)
  have htoFinset : ((List.finRange n).filter p).toFinset =
      Finset.univ.filter (fun x => p x = true) := by
    rw [List.toFinset_filter, List.toFinset_finRange]
  have hpair : ((List.finRange n).filter p).Pairwise (fun x y : Fin n => x ≤ y) :=
    List.Pairwise.imp (fun {_ _} h => le_of_lt h)
      (List.Pairwise.filter p
        (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange n)))
  rw [← htoFinset]
  exact (List.toFinset_sort (r := fun x y : Fin n => x ≤ y) hnodup).mpr hpair

namespace CertifiedLocalizedCIPInput

/-! ## Bond-order agreement on the localized admission domain -/

/-- On the shared domain the graph bond order of `input.moleculeGraph` is the source-canonical
aromatic bond order: the graph stores `localizedBondOrder` definitionally, and
`LocalizedCovalentPairsOnly` makes `aromaticCanonicalBondOrder` equal to it. -/
theorem moleculeGraph_bond_eq_aromaticCanonicalBondOrder
    (input : CertifiedLocalizedCIPInput)
    (left right : Fin input.certified.input.molecule.atomCount) :
    input.moleculeGraph.bond left right =
      input.certified.input.molecule.aromaticCanonicalBondOrder left.val right.val := by
  have graphBond :
      input.moleculeGraph.bond left right =
        input.certified.input.molecule.localizedBondOrder left.val right.val := rfl
  rw [graphBond]
  exact (input.certified.input.molecule
    |>.aromaticCanonicalBondOrder_eq_localizedBondOrder_of_localizedCovalentPairsOnly
      input.graphReady.2.2.2.1 left.val right.val).symm

/-! ## Neighbor-copy enumeration equality -/

/-- The public ordinary neighbor-copy enumeration and the localized executable neighbor-copy
enumeration are the *same list*, in the same order, at every atom.

The public side enumerates all of `List.finRange atomCount` and lets zero-degree entries contribute
nothing; the localized side enumerates the positive-degree neighbors sorted increasingly.  Since the
sorted `Finset` enumeration of positive-degree `Fin` indices is exactly the increasing filter of
`List.finRange`, and both per-neighbor copy functions use the same bond order, the lists coincide
entry for entry. -/
theorem aromaticCanonicalOrdinaryNeighborCopiesAt_eq_executableOfficialNeighborCopies
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    input.certified.input.molecule.aromaticCanonicalOrdinaryNeighborCopiesAt
        input.certified.input.molecule.atomCount atom
      = input.executableOfficialNeighborCopies atom := by
  have bondEq : ∀ neighbor : Fin input.certified.input.molecule.atomCount,
      input.moleculeGraph.bond atom neighbor =
        input.certified.input.molecule.aromaticCanonicalBondOrder atom.val neighbor.val :=
    fun neighbor => input.moleculeGraph_bond_eq_aromaticCanonicalBondOrder atom neighbor
  have neighborFinsetEq :
      input.moleculeGraph.neighborFinset atom =
        Finset.univ.filter (fun neighbor : Fin input.certified.input.molecule.atomCount =>
          decide (0 < input.certified.input.molecule.aromaticCanonicalBondOrder
            atom.val neighbor.val)) := by
    ext neighbor
    simp only [MoleculeGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    have adjacentEq :
        input.moleculeGraph.Adj atom neighbor =
          (0 < input.certified.input.molecule.aromaticCanonicalBondOrder
            atom.val neighbor.val) := by
      show (0 < input.moleculeGraph.bond atom neighbor) = _
      rw [bondEq neighbor]
    rw [adjacentEq, decide_eq_true_eq]
  have sortEq :
      (input.moleculeGraph.neighborFinset atom).sort (fun x y : Fin _ => x ≤ y) =
        (List.finRange input.certified.input.molecule.atomCount).filter
          (fun neighbor => decide
            (0 < input.certified.input.molecule.aromaticCanonicalBondOrder
              atom.val neighbor.val)) := by
    rw [neighborFinsetEq]
    exact sort_univ_filter_finRange_f88
      (fun neighbor => decide
        (0 < input.certified.input.molecule.aromaticCanonicalBondOrder atom.val neighbor.val))
  unfold SemanticMolecule.aromaticCanonicalOrdinaryNeighborCopiesAt
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies
  rw [sortEq]
  have functionEq :
      (fun neighbor : Fin input.certified.input.molecule.atomCount =>
          (List.range (input.moleculeGraph.bond atom neighbor)).map
            (fun copyIndex => (neighbor, copyIndex))) =
        (fun neighbor : Fin input.certified.input.molecule.atomCount =>
          (List.range (input.certified.input.molecule.aromaticCanonicalBondOrder
            atom.val neighbor.val)).map
            (fun copyIndex => (neighbor, copyIndex))) := by
    funext neighbor
    rw [bondEq neighbor]
  rw [functionEq]
  exact flatMap_eq_filter_flatMap_f88
    (List.finRange input.certified.input.molecule.atomCount)
    (fun neighbor => decide
      (0 < input.certified.input.molecule.aromaticCanonicalBondOrder atom.val neighbor.val))
    (fun neighbor =>
      (List.range (input.certified.input.molecule.aromaticCanonicalBondOrder
        atom.val neighbor.val)).map (fun copyIndex => (neighbor, copyIndex)))
    (by
      intro x hx
      have notPositive :
          ¬ (0 < input.certified.input.molecule.aromaticCanonicalBondOrder atom.val x.val) := by
        simpa using hx
      have hzero :
          input.certified.input.molecule.aromaticCanonicalBondOrder atom.val x.val = 0 := by
        omega
      simp [hzero])

/-! ## Child-copy enumeration equality -/

/-- Child copies (including the removal of the zero-index parent copy) also agree exactly.  Both
definitions case on `node.current?` and `node.parent?` in the same way and apply the same
`List.filter` to the neighbor copies of the current atom. -/
theorem aromaticCanonicalChildCopiesAt_eq_executableOfficialChildCopies
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom) :
    input.certified.input.molecule.aromaticCanonicalChildCopiesAt
        input.certified.input.molecule.atomCount node
      = input.executableOfficialChildCopies node := by
  have neighborCopies :=
    input.aromaticCanonicalOrdinaryNeighborCopiesAt_eq_executableOfficialNeighborCopies
  unfold SemanticMolecule.aromaticCanonicalChildCopiesAt
    CertifiedLocalizedCIPInput.executableOfficialChildCopies
  cases hcurrent : node.current? with
  | none => rfl
  | some current =>
      cases hparent : node.parent? with
      | none => exact neighborCopies current
      | some parent => simpa only using (congrArg (List.filter (fun copy : input.Atom × Nat => !(copy.1 == parent && copy.2 == 0))) (neighborCopies current))

/-! ## The cross-surface child enumeration theorem -/

/-- **The actual public-runtime child-enumeration bridge.**  For every certified localized CIP input
and every official CIP node, the source-canonical public child enumeration equals the executable
localized child enumeration as a list — same elements, same multiplicities, same order.

This is the exact equality (not a permutation) that occurrence-address transport requires. -/
theorem aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom) :
    input.certified.input.molecule.aromaticCanonicalOfficialCIPChildrenAt
        input.certified.input.molecule.atomCount node
      = input.executableOfficialCIPChildren node := by
  have noEdges : input.certified.input.molecule.aromaticPairEdges = [] :=
    SemanticMolecule.aromaticPairEdges_eq_nil_of_localizedCovalentPairsOnly
      input.certified.input.molecule input.graphReady.2.2.2.1
  have noRepresentative : ∀ atom : input.Atom,
      input.certified.input.molecule.aromaticCanonicalMancudeRepresentativeAt?
        input.certified.input.molecule.atomCount atom = none := by
    intro atom
    rw [SemanticMolecule.aromaticCanonicalMancudeRepresentativeAt?, noEdges]
    rw [List.find?_eq_none]
    intro neighbor _ present
    simp at present
  have childCopies :=
    input.aromaticCanonicalChildCopiesAt_eq_executableOfficialChildCopies node
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt,
      CertifiedLocalizedCIPInput.executableOfficialCIPChildren, duplicate]
  · unfold SemanticMolecule.aromaticCanonicalOfficialCIPChildrenAt
      CertifiedLocalizedCIPInput.executableOfficialCIPChildren
    rw [if_neg duplicate, if_neg duplicate]
    dsimp only
    rw [childCopies]
    cases hcurrent : node.current? with
    | none => simp
    | some current => simp [noRepresentative current]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.moleculeGraph_bond_eq_aromaticCanonicalBondOrder
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.aromaticCanonicalOrdinaryNeighborCopiesAt_eq_executableOfficialNeighborCopies
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.aromaticCanonicalChildCopiesAt_eq_executableOfficialChildCopies
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren
