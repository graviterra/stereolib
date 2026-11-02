import TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline
import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Reflection-derived case for the experimental cage recalculation

Reflect the actual coordinate table and recompute. A raw letter that changes is uppercase;
an unchanged raw letter is lowercase. This is the reflection criterion stated in Blue Book
P-91.2.1.1 and the alternative mirrored-input test in Hanson et al. (2018), p. 1761.

The test does not endorse experimental recalculation as a general chemical rule. The accepted
fixed-graph, chosen-mark and temporary-state restrictions remain. It supplies a case test based
on actual mirror behavior, rather than on the desired physical root answer or marker counts.
-/

namespace TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedReadback
open TetraStereo.OneCenter.LocalizedHiddenParityPromotedPipeline
open TetraStereo.OneCenter.CartesianPoint3

def mirrorPoints (P : List CartesianPoint3) : List CartesianPoint3 := P.map reflectX

theorem mirrorLength (P : List CartesianPoint3) (len : P.length = 15) :
    (mirrorPoints P).length = 15 := by simpa [mirrorPoints] using len

variable (P : List CartesianPoint3) (len : P.length = 15)

theorem posWith_mirror (atom : Fin 15) :
    posWith (mirrorPoints P) (mirrorLength P len) atom = reflectX (posWith P len atom) := by
  simp [posWith, mirrorPoints]

theorem volume_mirror (c : cageCanon.Center) :
    ligandVolumeWith (mirrorPoints P) (mirrorLength P len) c = - ligandVolumeWith P len c := by
  simp only [ligandVolumeWith, posWith_mirror P len]
  exact orientedVolume_reflectX _ _ _ _

theorem nondegenerate_mirror (nondeg : Nondegenerate P len) :
    Nondegenerate (mirrorPoints P) (mirrorLength P len) := by
  intro c
  rw [volume_mirror P len]
  exact neg_ne_zero.mpr (nondeg c)

theorem pointOf_mirror (atom : Nat) :
    pointOf? (mirrorPoints P) (mirrorLength P len) atom =
      (pointOf? P len atom).map reflectX := by
  unfold pointOf?
  split_ifs <;> simp [posWith_mirror P len]

theorem pointsOf_mirror (atoms : List Nat) :
    atoms.mapM (pointOf? (mirrorPoints P) (mirrorLength P len)) =
      (atoms.mapM (pointOf? P len)).map (List.map reflectX) := by
  induction atoms with
  | nil => rfl
  | cons atom tail ih =>
      simp only [List.mapM_cons, pointOf_mirror P len, ih]
      cases pointOf? P len atom <;> cases tail.mapM (pointOf? P len) <;> rfl

/-- Every successful marked far readback changes raw letter under the actual spatial mirror. -/
theorem visitReadback_mirror (node : RawMolecule.CanonicalBranchNode) (mark : Nat) :
    visitReadback? (mirrorPoints P) (mirrorLength P len) node mark =
      (visitReadback? P len node mark).map RS.swap := by
  unfold visitReadback?
  cases ha : visitRankedAtoms? node mark with
  | none => simp
  | some atoms =>
      simp only [Option.bind_eq_bind, Option.bind_some, pointsOf_mirror P len]
      cases hp : atoms.mapM (pointOf? P len) with
      | none => simp
      | some points =>
          simpa using descriptorOfPriorityOrderedPoints?_reflectX points

theorem jointA_mirror :
    jointLetterA (mirrorPoints P) (mirrorLength P len) = jointLetterA P len := by
  simp [jointLetterA, volume_mirror P len]

theorem jointB_mirror :
    jointLetterB (mirrorPoints P) (mirrorLength P len) = jointLetterB P len := by
  simp [jointLetterB, volume_mirror P len]

/-- Both stages are recomputed, including their temporary far snapshots. -/
theorem nearA_mirror (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [5, 6, 7])
    (uppercase : Bool) :
    nearFromFar? (mirrorPoints P) (mirrorLength P len)
        LocalizedHiddenParityMarkedProbe.farA (offDiagonalA r)
        LocalizedHiddenParityMarkedProbe.nearA r uppercase =
      nearFromFar? P len LocalizedHiddenParityMarkedProbe.farA (offDiagonalA r)
        LocalizedHiddenParityMarkedProbe.nearA r uppercase := by
  rw [nearFromFarA_eq _ _ (nondegenerate_mirror P len nondeg) r hr uppercase,
    nearFromFarA_eq P len nondeg r hr uppercase, jointA_mirror P len]

theorem nearB_mirror (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [11, 12, 13])
    (uppercase : Bool) :
    nearFromFar? (mirrorPoints P) (mirrorLength P len) farB (offDiagonalB r) nearB r uppercase =
      nearFromFar? P len farB (offDiagonalB r) nearB r uppercase := by
  rw [nearFromFarB_eq _ _ (nondegenerate_mirror P len nondeg) r hr uppercase,
    nearFromFarB_eq P len nondeg r hr uppercase, jointB_mirror P len]

theorem rootConsensus_mirror (nondeg : Nondegenerate P len) (uppercase : Bool) :
    rootConsensus? (mirrorPoints P) (mirrorLength P len) uppercase =
      (rootConsensus? P len uppercase).map RS.swap := by
  have nm := nondegenerate_mirror P len nondeg
  by_cases different : jointLetterA P len ≠ jointLetterB P len
  · have dm : jointLetterA (mirrorPoints P) (mirrorLength P len) ≠
        jointLetterB (mirrorPoints P) (mirrorLength P len) := by
      simpa [jointA_mirror P len, jointB_mirror P len] using different
    rw [(rootConsensus_cases _ _ nm uppercase).1 dm,
      (rootConsensus_cases P len nondeg uppercase).1 different]
    simp only [Option.map_some, jointA_mirror P len, volume_mirror P len]
    by_cases first : jointLetterA P len = RS.R
    · simp only [first, ↓reduceIte, neg_neg]
      rw [letterOfVolume_neg (nondeg k0)]
      cases letterOfVolume (ligandVolumeWith P len k0) <;> rfl
    · simp only [first, ↓reduceIte]
      rw [letterOfVolume_neg (nondeg k0)]
  · have same : jointLetterA P len = jointLetterB P len := not_ne_iff.mp different
    have sm : jointLetterA (mirrorPoints P) (mirrorLength P len) =
        jointLetterB (mirrorPoints P) (mirrorLength P len) := by
      simpa [jointA_mirror P len, jointB_mirror P len] using same
    rw [(rootConsensus_cases _ _ nm uppercase).2 sm,
      (rootConsensus_cases P len nondeg uppercase).2 same]
    rfl

theorem pipeline_mirror (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13])
    (uA uB rootUppercase : Bool) :
    pipeline? (mirrorPoints P) (mirrorLength P len) rA rB uA uB rootUppercase =
      (pipeline? P len rA rB uA uB rootUppercase).map RS.swap := by
  rw [pipeline_eq_rootConsensus _ _ (nondegenerate_mirror P len nondeg)
      rA rB hA hB uA uB rootUppercase,
    pipeline_eq_rootConsensus P len nondeg rA rB hA hB uA uB rootUppercase]
  exact rootConsensus_mirror P len nondeg rootUppercase

/-- Refuse if either computation refuses. Otherwise determine case from mirror behavior. -/
def descriptorFromMirror? (original reflected : Option RS) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let a ← original
  let b ← reflected
  some (if b = a then .pseudoasymmetric (pseudoRSOfRS a) else .chiral a)

theorem descriptorFromMirror_same (raw : RS) :
    descriptorFromMirror? (some raw) (some raw) = some (.pseudoasymmetric (pseudoRSOfRS raw)) := by
  simp [descriptorFromMirror?]

theorem descriptorFromMirror_swap (raw : RS) :
    descriptorFromMirror? (some raw) (some raw.swap) = some (.chiral raw) := by
  simp [descriptorFromMirror?, swap_ne_self]

theorem far_case (node : RawMolecule.CanonicalBranchNode) (mark : Nat) (raw : RS)
    (computed : visitReadback? P len node mark = some raw) :
    descriptorFromMirror? (visitReadback? P len node mark)
      (visitReadback? (mirrorPoints P) (mirrorLength P len) node mark) = some (.chiral raw) := by
  rw [visitReadback_mirror P len node mark, computed]
  exact descriptorFromMirror_swap raw

theorem nearA_case (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [5, 6, 7])
    (uppercase : Bool) :
    descriptorFromMirror?
        (nearFromFar? P len LocalizedHiddenParityMarkedProbe.farA (offDiagonalA r)
          LocalizedHiddenParityMarkedProbe.nearA r uppercase)
        (nearFromFar? (mirrorPoints P) (mirrorLength P len)
          LocalizedHiddenParityMarkedProbe.farA (offDiagonalA r)
          LocalizedHiddenParityMarkedProbe.nearA r uppercase) =
      some (.pseudoasymmetric (pseudoRSOfRS (jointLetterA P len))) := by
  rw [nearA_mirror P len nondeg r hr uppercase,
    nearFromFarA_eq P len nondeg r hr uppercase]
  exact descriptorFromMirror_same _

theorem nearB_case (nondeg : Nondegenerate P len) (r : Nat) (hr : r ∈ [11, 12, 13])
    (uppercase : Bool) :
    descriptorFromMirror? (nearFromFar? P len farB (offDiagonalB r) nearB r uppercase)
      (nearFromFar? (mirrorPoints P) (mirrorLength P len) farB (offDiagonalB r) nearB r uppercase) =
      some (.pseudoasymmetric (pseudoRSOfRS (jointLetterB P len))) := by
  rw [nearB_mirror P len nondeg r hr uppercase,
    nearFromFarB_eq P len nondeg r hr uppercase]
  exact descriptorFromMirror_same _

/-- Recompute the complete output-driven pipeline on both actual spatial inputs. -/
def casedPipeline? (rA rB : Nat) (uA uB rootUppercase : Bool) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  descriptorFromMirror? (pipeline? P len rA rB uA uB rootUppercase)
    (pipeline? (mirrorPoints P) (mirrorLength P len) rA rB uA uB rootUppercase)

theorem casedPipeline_eq (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13])
    (uA uB rootUppercase : Bool) :
    casedPipeline? P len rA rB uA uB rootUppercase =
      (pipeline? P len rA rB uA uB rootUppercase).map
        LocalizedTetrahedralRSPseudoDescriptor.chiral := by
  unfold casedPipeline?
  rw [pipeline_mirror P len nondeg rA rB hA hB uA uB rootUppercase]
  cases pipeline? P len rA rB uA uB rootUppercase with
  | none => rfl
  | some raw => exact descriptorFromMirror_swap raw

theorem casedPipeline_isSome_iff_pairwise (nondeg : Nondegenerate P len)
    (rA rB : Nat) (hA : rA ∈ [5, 6, 7]) (hB : rB ∈ [11, 12, 13])
    (uA uB rootUppercase : Bool) :
    (casedPipeline? P len rA rB uA uB rootUppercase).isSome = true ↔
      MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
        (rootWith P len) := by
  rw [casedPipeline_eq P len nondeg rA rB hA hB uA uB rootUppercase]
  simpa using pipeline_isSome_iff_pairwise P len nondeg rA rB hA hB uA uB rootUppercase

end TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection

assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.volume_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.nondegenerate_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.visitReadback_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.nearA_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.nearB_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.rootConsensus_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.pipeline_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.far_case
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.nearA_case
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.nearB_case
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.casedPipeline_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedHiddenParityPromotedReflection.casedPipeline_isSome_iff_pairwise
