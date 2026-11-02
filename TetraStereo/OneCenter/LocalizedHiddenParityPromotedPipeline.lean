import TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Output-driven composition of the experimental cage recalculation

Every temporary descriptor below comes from the existing marked ranking and coordinate
readback. No joint-sign formula or desired physical classification occurs in the computation.
The proofs connect this composition to the accepted family result.

This still uses the fixed cage graph, chosen off-diagonal visits, empty ordinary state at the
far visits, explicit temporary case choices, and experimental two-mark root consensus.
It is not the production generated state or a general chemically justified recalculation.
-/

namespace TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline

open TetraStereo.OneCenter
open TetraStereo.OneCenter.DeclarativeCIP.ProductionOccurrenceRules456
open TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback

variable (P : List CartesianPoint3) (len : P.length = 15)

/-- Read both visits independently; refusal of either is propagated. -/
def farSnapshot? (far : Nat → RawMolecule.CanonicalBranchNode) (visits : List Nat)
    (mark : Nat) (uppercase : Bool) : Option OccurrenceAuxState :=
  visits.mapM fun o => do
    let letter ← visitReadback? P len (far o) mark
    pure (tempFact (far o) letter uppercase)

/-- Compute the far snapshot before reading the near occurrence. -/
def nearFromFar? (far : Nat → RawMolecule.CanonicalBranchNode) (visits : List Nat)
    (near : RawMolecule.CanonicalBranchNode) (mark : Nat) (uppercase : Bool) : Option RS := do
  let state ← farSnapshot? P len far visits mark uppercase
  readbackWith? P len state near mark

/-- Root temporary facts contain the two computed near results, not physical sign formulas. -/
def rootSnapshot? (rA rB : Nat) (uA uB rootUppercase : Bool) : Option OccurrenceAuxState := do
  let a ← nearFromFar? P len farA (offDiagonalA rA) nearA rA uA
  let b ← nearFromFar? P len farB (offDiagonalB rB) nearB rB uB
  pure (rootTemp a b rootUppercase)

/-- Execute far → near → root for both arm marks, requiring agreement of the raw readings. -/
def pipeline? (rA rB : Nat) (uA uB rootUppercase : Bool) : Option RS := do
  let state ← rootSnapshot? P len rA rB uA uB rootUppercase
  let a ← readbackWith? P len state root0 3
  let b ← readbackWith? P len state root0 9
  if a = b then some a else none

theorem farSnapshotA_eq (nondeg : Nondegenerate P len)
    (r : Nat) (hr : r ∈ [5, 6, 7]) (u : Bool) :
    farSnapshot? P len farA (offDiagonalA r) r u = some (computedStateA P len r u) := by
  rcases farReadbackA_letters P len nondeg with ⟨h65, h75, h56, h76, h57, h67⟩
  have cases : r = 5 ∨ r = 6 ∨ r = 7 := by simpa using hr
  rcases cases with rfl | rfl | rfl <;>
    simp [farSnapshot?, offDiagonalA, computedStateA, tempStateA,
      h65, h75, h56, h76, h57, h67]

theorem farSnapshotB_eq (nondeg : Nondegenerate P len)
    (r : Nat) (hr : r ∈ [11, 12, 13]) (u : Bool) :
    farSnapshot? P len farB (offDiagonalB r) r u = some (computedStateB P len r u) := by
  rcases farReadbackB_letters P len nondeg with ⟨h1211, h1311, h1112, h1312, h1113, h1213⟩
  have cases : r = 11 ∨ r = 12 ∨ r = 13 := by simpa using hr
  rcases cases with rfl | rfl | rfl <;>
    simp [farSnapshot?, offDiagonalB, computedStateB, tempStateB,
      h1211, h1311, h1112, h1312, h1113, h1213]

theorem nearFromFarA_eq (nondeg : Nondegenerate P len)
    (r : Nat) (hr : r ∈ [5, 6, 7]) (u : Bool) :
    nearFromFar? P len farA (offDiagonalA r) nearA r u = some (jointLetterA P len) := by
  unfold nearFromFar?
  rw [farSnapshotA_eq P len nondeg r hr u]
  exact nearRecalcA P len nondeg r hr u

theorem nearFromFarB_eq (nondeg : Nondegenerate P len)
    (r : Nat) (hr : r ∈ [11, 12, 13]) (u : Bool) :
    nearFromFar? P len farB (offDiagonalB r) nearB r u = some (jointLetterB P len) := by
  unfold nearFromFar?
  rw [farSnapshotB_eq P len nondeg r hr u]
  exact nearRecalcB P len nondeg r hr u

theorem rootSnapshot_eq (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13])
    (uA uB rootUppercase : Bool) :
    rootSnapshot? P len rA rB uA uB rootUppercase =
      some (rootTemp (jointLetterA P len) (jointLetterB P len) rootUppercase) := by
  simp [rootSnapshot?, nearFromFarA_eq P len nondeg rA hA uA,
    nearFromFarB_eq P len nondeg rB hB uB]

theorem pipeline_eq_rootConsensus (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13])
    (uA uB rootUppercase : Bool) :
    pipeline? P len rA rB uA uB rootUppercase = rootConsensus? P len rootUppercase := by
  unfold pipeline?
  rw [rootSnapshot_eq P len nondeg rA rB hA hB uA uB rootUppercase]
  simp only [Option.bind_eq_bind, Option.bind_some]
  unfold rootConsensus?
  cases readbackWith? P len (rootTemp (jointLetterA P len) (jointLetterB P len)
      rootUppercase) root0 3 <;>
    cases readbackWith? P len (rootTemp (jointLetterA P len) (jointLetterB P len)
      rootUppercase) root0 9 <;> rfl

/-- Actual output-driven composition succeeds exactly on physically distinguishable roots
in the accepted nondegenerate cage family. This does not choose a final descriptor case. -/
theorem pipeline_isSome_iff_pairwise (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13])
    (uA uB rootUppercase : Bool) :
    (pipeline? P len rA rB uA uB rootUppercase).isSome = true ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  rw [pipeline_eq_rootConsensus P len nondeg rA rB hA hB uA uB rootUppercase]
  exact rootConsensus_isSome_iff_pairwise P len nondeg rootUppercase

end TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline.farSnapshotA_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline.farSnapshotB_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline.nearFromFarA_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline.nearFromFarB_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline.rootSnapshot_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline.pipeline_eq_rootConsensus
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline.pipeline_isSome_iff_pairwise
