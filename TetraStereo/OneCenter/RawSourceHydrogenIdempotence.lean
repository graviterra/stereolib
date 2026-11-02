import TetraStereo.OneCenter.RawSourceHydrogenPolicy
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
# Idempotence of source hydrogen freezing

`RawMolecule.freezeSourceHydrogenCounts` rewrites only the `explicitHydrogens?` policy of every
atom, storing the exact `hydrogenCountAt` value read from the molecule supplied to it.  The shared
API in `RawSourceHydrogenPolicy` proves that freezing preserves every source hydrogen count
(`freezeSourceHydrogenCounts_hydrogenCountAt`), and that the frozen atom lookup is the source atom
with only its hydrogen policy replaced (`freezeSourceHydrogenCounts_atomAt?_spec`).

A second freezing pass therefore reads, at every index, exactly the count the first pass stored.
Since the atom inventory, bond records, written-neighbour order, and introduction history are
untouched by either pass, the two resulting records agree in every field:

`freezeSourceHydrogenCounts (freezeSourceHydrogenCounts mol) = freezeSourceHydrogenCounts mol`.

This is the stability fact needed by downstream production wrappers that finish with the freezing
step: such a wrapper is already a fixed point of any further freezing pass.
-/

/-- The index-aware atom map is idempotent when the hydrogen counts are read from the same source
molecule.  The first map has stored `mol.hydrogenCountAt` at every position; the second map reads
the same values because freezing preserves that count exactly, so only the identical policy is
written again. -/
theorem freezeSourceHydrogenCountsAux_freeze_comp (mol : RawMolecule) (offset : Nat)
    (atoms : List AtomSpec) :
    freezeSourceHydrogenCountsAux (freezeSourceHydrogenCounts mol) offset
        (freezeSourceHydrogenCountsAux mol offset atoms) =
      freezeSourceHydrogenCountsAux mol offset atoms := by
  induction atoms generalizing offset with
  | nil => rfl
  | cons atom rest ih =>
      simp only [freezeSourceHydrogenCountsAux, freezeSourceHydrogenCounts_hydrogenCountAt]
      rw [ih (offset + 1)]

/-- The atom inventory of a frozen molecule is unchanged by a second freezing pass. -/
theorem freezeSourceHydrogenCounts_atoms_idempotent (mol : RawMolecule) :
    (freezeSourceHydrogenCounts (freezeSourceHydrogenCounts mol)).atoms =
      (freezeSourceHydrogenCounts mol).atoms := by
  rw [freezeSourceHydrogenCounts_atoms (freezeSourceHydrogenCounts mol),
    freezeSourceHydrogenCounts_atoms mol]
  exact freezeSourceHydrogenCountsAux_freeze_comp mol 0 mol.atoms

/-- **Freezing source hydrogen counts is idempotent** on every raw molecule.

The result is full record equality, not merely equality of hydrogen counts: `bonds`,
`neighborOrder`, and `introductionPredecessors` are carried through unchanged by both passes, and
the `atoms` field is the idempotence just established for the index-aware auxiliary map. -/
theorem freezeSourceHydrogenCounts_idempotent (mol : RawMolecule) :
    freezeSourceHydrogenCounts (freezeSourceHydrogenCounts mol) =
      freezeSourceHydrogenCounts mol := by
  rcases mol with ⟨atoms, bonds, neighborOrder, introductionPredecessors⟩
  change RawMolecule.mk
      (freezeSourceHydrogenCountsAux
        (freezeSourceHydrogenCounts
          ⟨atoms, bonds, neighborOrder, introductionPredecessors⟩) 0
        (freezeSourceHydrogenCountsAux
          ⟨atoms, bonds, neighborOrder, introductionPredecessors⟩ 0 atoms))
      bonds neighborOrder introductionPredecessors =
    RawMolecule.mk
      (freezeSourceHydrogenCountsAux
        ⟨atoms, bonds, neighborOrder, introductionPredecessors⟩ 0 atoms)
      bonds neighborOrder introductionPredecessors
  rw [freezeSourceHydrogenCountsAux_freeze_comp]

/-! ## Downstream wrapper corollaries -/

/-- Any production wrapper whose final stage is `freezeSourceHydrogenCounts` is already a fixed
point of a further freezing pass.  The upstream step is left abstract so the statement instantiates
to any normalizer without depending on its internals. -/
theorem freezeSourceHydrogenCounts_comp_idempotent (step : RawMolecule → RawMolecule)
    (mol : RawMolecule) :
    freezeSourceHydrogenCounts (freezeSourceHydrogenCounts (step mol)) =
      freezeSourceHydrogenCounts (step mol) :=
  freezeSourceHydrogenCounts_idempotent (step mol)

/-- The production default-bond normalizer, followed by the freezing wrapper, is stable under a
further freezing pass.  This is the concrete downstream instance for the repository's
`normalizeUnspecifiedBonds` stage; the two stages need not be commuted, since only the outer
freezing step is iterated. -/
theorem freezeSourceHydrogenCounts_normalizeUnspecifiedBonds_idempotent (mol : RawMolecule) :
    freezeSourceHydrogenCounts
        (freezeSourceHydrogenCounts mol.normalizeUnspecifiedBonds) =
      freezeSourceHydrogenCounts mol.normalizeUnspecifiedBonds :=
  freezeSourceHydrogenCounts_comp_idempotent normalizeUnspecifiedBonds mol

/-- Freezing is an idempotent endofunction of raw molecules. -/
theorem freezeSourceHydrogenCounts_comp_self :
    freezeSourceHydrogenCounts ∘ freezeSourceHydrogenCounts =
      freezeSourceHydrogenCounts :=
  funext freezeSourceHydrogenCounts_idempotent

/-- Pointwise atom-lookup form of idempotence, convenient for downstream proofs that inspect one
index at a time. -/
theorem freezeSourceHydrogenCounts_atomAt?_idempotent (mol : RawMolecule) (index : Nat) :
    (freezeSourceHydrogenCounts (freezeSourceHydrogenCounts mol)).atomAt? index =
      (freezeSourceHydrogenCounts mol).atomAt? index := by
  rw [freezeSourceHydrogenCounts_idempotent]

/-- Pointwise hydrogen-count form of idempotence. -/
theorem freezeSourceHydrogenCounts_hydrogenCountAt_idempotent (mol : RawMolecule) (index : Nat) :
    (freezeSourceHydrogenCounts (freezeSourceHydrogenCounts mol)).hydrogenCountAt index =
      (freezeSourceHydrogenCounts mol).hydrogenCountAt index := by
  rw [freezeSourceHydrogenCounts_idempotent]

/-! ## Kernel-authority guards -/

assert_kernel_only freezeSourceHydrogenCountsAux_freeze_comp
assert_kernel_only freezeSourceHydrogenCounts_atoms_idempotent
assert_kernel_only freezeSourceHydrogenCounts_idempotent
assert_kernel_only freezeSourceHydrogenCounts_comp_idempotent
assert_kernel_only freezeSourceHydrogenCounts_normalizeUnspecifiedBonds_idempotent
assert_kernel_only freezeSourceHydrogenCounts_comp_self
assert_kernel_only freezeSourceHydrogenCounts_atomAt?_idempotent
assert_kernel_only freezeSourceHydrogenCounts_hydrogenCountAt_idempotent

end RawMolecule
end OneCenter
end TetraStereo
