import TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Mirror-derived temporary facts through the experimental cage pipeline

No letter or case bit is supplied by a caller. Each far fact comes from actual original/mirrored
far computations; each near fact comes from recomputed far snapshots in both inputs; the root
consensus and final case consume those near facts. The comparison with the earlier explicit-case
pipeline is proved, not used to implement these functions.

This remains a fixed-cage experimental constructor with prescribed marks/visits and empty
ordinary far state. It does not establish a production fixed point or general chemical priority.
-/

namespace TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedHiddenParityMarkedProbe
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection

/-- Pack the computed descriptor faithfully into a temporary occurrence fact. -/
def factOfDescriptor (node : RawMolecule.CanonicalBranchNode) :
    LocalizedTetrahedralRSPseudoDescriptor → OccurrenceAuxFact
  | .chiral raw => tempFact node raw true
  | .pseudoasymmetric .r => tempFact node .R false
  | .pseudoasymmetric .s => tempFact node .S false

theorem factOfDescriptor_pseudo (node : RawMolecule.CanonicalBranchNode) (raw : RS) :
    factOfDescriptor node (.pseudoasymmetric (pseudoRSOfRS raw)) = tempFact node raw false := by
  cases raw <;> rfl

def observedFact? (node : RawMolecule.CanonicalBranchNode) (original reflected : Option RS) :
    Option OccurrenceAuxFact :=
  (descriptorFromMirror? original reflected).map (factOfDescriptor node)

variable (P : List CartesianPoint3) (len : P.length = 15)

def farFact? (node : RawMolecule.CanonicalBranchNode) (mark : Nat) : Option OccurrenceAuxFact :=
  observedFact? node (visitReadback? P len node mark)
    (visitReadback? (mirrorPoints P) (mirrorLength P len) node mark)

def farState? (far : Nat → RawMolecule.CanonicalBranchNode) (visits : List Nat) (mark : Nat) :
    Option OccurrenceAuxState :=
  visits.mapM fun o => farFact? P len (far o) mark

def nearRaw? (far : Nat → RawMolecule.CanonicalBranchNode) (visits : List Nat)
    (near : RawMolecule.CanonicalBranchNode) (mark : Nat) : Option RS := do
  let state ← farState? P len far visits mark
  readbackWith? P len state near mark

def nearFact? (far : Nat → RawMolecule.CanonicalBranchNode) (visits : List Nat)
    (near : RawMolecule.CanonicalBranchNode) (mark : Nat) : Option OccurrenceAuxFact :=
  observedFact? near (nearRaw? P len far visits near mark)
    (nearRaw? (mirrorPoints P) (mirrorLength P len) far visits near mark)

def rootState? (rA rB : Nat) : Option OccurrenceAuxState := do
  let a ← nearFact? P len farA (offDiagonalA rA) nearA rA
  let b ← nearFact? P len farB (offDiagonalB rB) nearB rB
  some [a, b]

def rootRaw? (rA rB : Nat) : Option RS := do
  let state ← rootState? P len rA rB
  let a ← readbackWith? P len state root0 3
  let b ← readbackWith? P len state root0 9
  if a = b then some a else none

/-- Complete mirror-derived calculation: no externally supplied descriptor or case policy. -/
def assign? (rA rB : Nat) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorFromMirror? (rootRaw? P len rA rB)
    (rootRaw? (mirrorPoints P) (mirrorLength P len) rA rB)

theorem farFact_eq (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    farFact? P len node mark =
      (visitReadback? P len node mark).map (fun raw => tempFact node raw true) := by
  unfold farFact? observedFact?
  rw [visitReadback_mirror P len node mark]
  cases visitReadback? P len node mark with
  | none => rfl
  | some raw => simp [descriptorFromMirror_swap, factOfDescriptor]

theorem farState_eq (far : Nat → RawMolecule.CanonicalBranchNode) (visits : List Nat)
    (mark : Nat) :
    farState? P len far visits mark = farSnapshot? P len far visits mark true := by
  unfold farState? farSnapshot?
  apply congrArg (fun f : Nat → Option OccurrenceAuxFact => visits.mapM f)
  funext o
  rw [farFact_eq P len]
  cases visitReadback? P len (far o) mark <;> rfl

theorem nearRaw_eq (far : Nat → RawMolecule.CanonicalBranchNode) (visits : List Nat)
    (near : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    nearRaw? P len far visits near mark = nearFromFar? P len far visits near mark true := by
  unfold nearRaw? nearFromFar?
  rw [farState_eq P len]

theorem nearFactA_eq (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [5, 6, 7]) :
    nearFact? P len farA (offDiagonalA r) nearA r =
      some (tempFact nearA (jointLetterA P len) false) := by
  unfold nearFact? observedFact?
  rw [nearRaw_eq P len, nearRaw_eq (mirrorPoints P) (mirrorLength P len),
    nearA_case P len nondeg r hr true]
  simp [factOfDescriptor_pseudo]

theorem nearFactB_eq (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [11, 12, 13]) :
    nearFact? P len farB (offDiagonalB r) nearB r =
      some (tempFact nearB (jointLetterB P len) false) := by
  unfold nearFact? observedFact?
  rw [nearRaw_eq P len, nearRaw_eq (mirrorPoints P) (mirrorLength P len),
    nearB_case P len nondeg r hr true]
  simp [factOfDescriptor_pseudo]

theorem rootState_eq (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13]) :
    rootState? P len rA rB = rootSnapshot? P len rA rB true true false := by
  rw [rootSnapshot_eq P len nondeg rA rB hA hB true true false]
  simp [rootState?, nearFactA_eq P len nondeg rA hA,
    nearFactB_eq P len nondeg rB hB, rootTemp]

theorem rootRaw_eq (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13]) :
    rootRaw? P len rA rB = pipeline? P len rA rB true true false := by
  unfold rootRaw? pipeline?
  rw [rootState_eq P len nondeg rA rB hA hB]

theorem assign_eq (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13]) :
    assign? P len rA rB = casedPipeline? P len rA rB true true false := by
  unfold assign? casedPipeline?
  rw [rootRaw_eq P len nondeg rA rB hA hB,
    rootRaw_eq _ _ (nondegenerate_mirror P len nondeg) rA rB hA hB]

/-- The result is uppercase whenever the experimental pipeline succeeds. -/
theorem assign_eq_chiral (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13]) :
    assign? P len rA rB =
      (pipeline? P len rA rB true true false).map LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  rw [assign_eq P len nondeg rA rB hA hB]
  exact casedPipeline_eq P len nondeg rA rB hA hB true true false

/-- Actual case-generating computation succeeds exactly on the physically distinguishable roots
of the accepted nondegenerate family; no successful label or chosen case is assumed. -/
theorem assign_isSome_iff_pairwise (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13]) :
    (assign? P len rA rB).isSome = true ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  rw [assign_eq P len nondeg rA rB hA hB]
  exact casedPipeline_isSome_iff_pairwise P len nondeg rA rB hA hB true true false

end TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.farFact_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.farState_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.nearRaw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.nearFactA_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.nearFactB_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.rootState_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.rootRaw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.assign_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.assign_eq_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityMirrorDerivedPipeline.assign_isSome_iff_pairwise
