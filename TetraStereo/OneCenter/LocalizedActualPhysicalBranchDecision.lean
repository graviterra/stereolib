import TetraStereo.OneCenter.FinitePhysicalBranchTransport
import TetraStereo.OneCenter.LocalizedPhysicalDomainReindexing
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The physical branch decision on actual molecular source

`FinitePhysicalBranchTransport` decides the existing branch relations for any explicitly
represented `MultiCenterMolecule`. The accepted molecules of a certified input are declared
`noncomputable`, so this module supplies the executable source frame.

* `actualCanonicalMolecule input`: the certified graph, the detected centre inventory and the
  sorted-neighbour ligand frames, with computable data. It **is** the accepted
  `canonicalDetectedMultiCenterMolecule` (`actualCanonicalMolecule_eq`, by `rfl`).
* `coordinateCfg input`: a computable physical configuration read from the certified spatial
  table (sign of the oriented ligand volume in canonical order). It is calibrated wherever the four
  ligand positions exist with nonzero volume (`coordinateCfg_calibrated`).
* **Frame correspondence.** For any frame reindexing `τ` carrying the canonical frames to the
  accepted detected molecule (`exists_reindexFrames_detectedMultiCenterMolecule`), the computed
  canonical count equals the physical count of the detected molecule in the reindexed
  configuration (`computedPairCount_canonical_eq_detected`).
-/

namespace TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision

open RootedTetrahedralBranchSymmetry FinitePhysicalBranchTransport CartesianPoint3

/-- The canonical detected molecule of an actual certified input, with executable data. -/
def actualCanonicalMolecule (input : CertifiedLocalizedCIPInput) :
    MultiCenterMolecule input.Atom where
  mol := input.moleculeGraph
  centers := input.tetrahedralCenterSet
  ligandAtom := fun c hc i => input.canonicalLigandAtom ⟨c, hc⟩ i
  ligandAtom_adj := input.canonicalDetectedMultiCenterMolecule.ligandAtom_adj
  ligandAtom_injective := input.canonicalDetectedMultiCenterMolecule.ligandAtom_injective
  ligandAtom_surjective := input.canonicalDetectedMultiCenterMolecule.ligandAtom_surjective

theorem actualCanonicalMolecule_eq (input : CertifiedLocalizedCIPInput) :
    actualCanonicalMolecule input = input.canonicalDetectedMultiCenterMolecule := rfl

/-! ## A configuration read from the certified coordinates -/

/-- Oriented volume of the four canonical ligand positions, when all are present. -/
def coordinateVolume? (input : CertifiedLocalizedCIPInput)
    (c : (actualCanonicalMolecule input).Center) : Option ℚ := do
  let p0 ← input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 0)
  let p1 ← input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 1)
  let p2 ← input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 2)
  let p3 ← input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 3)
  pure (orientedVolume p0 p1 p2 p3)

/-- The physical configuration read from coordinates (identity frame when coordinates are
absent; such a centre is simply not calibrated). -/
def coordinateCfg (input : CertifiedLocalizedCIPInput) :
    (actualCanonicalMolecule input).Configuration := fun c =>
  match coordinateVolume? input c with
  | some v => if v < 0 then Equiv.swap 0 1 else 1
  | none => 1

theorem coordinateCfg_calibrated (input : CertifiedLocalizedCIPInput)
    (c : (actualCanonicalMolecule input).Center) (points : Fin 4 → CartesianPoint3)
    (observed : ∀ k, input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c k) =
      some (points k))
    (nonzero : orientedVolume (points 0) (points 1) (points 2) (points 3) ≠ 0) :
    LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates input
      (actualCanonicalMolecule input) (coordinateCfg input) c := by
  have volume : coordinateVolume? input c =
      some (orientedVolume (points 0) (points 1) (points 2) (points 3)) := by
    simp [coordinateVolume?, observed]
  refine ⟨points, observed, nonzero, ?_⟩
  simp only [MultiCenterMolecule.configurationSign, coordinateCfg, volume]
  split_ifs with negative
  · rw [rationalVolumeSign_of_neg negative]
    simp [permHandedness, Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide)]
  · rw [rationalVolumeSign_of_pos (lt_of_le_of_ne (not_lt.mp negative) nonzero.symm)]
    simp [permHandedness]

/-! ## Frame correspondence with the accepted detected molecule -/

theorem physicalPairCount_congr {V : Type*} [Fintype V] [DecidableEq V]
    {m n : MultiCenterMolecule V} (h : m = n) (cfg : m.Configuration) (center : m.Center) :
    physicalEnantiomorphicPairCount n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) center) =
      physicalEnantiomorphicPairCount m cfg center := by
  cases h
  rfl

/-- **The computed canonical count is the physical count of the detected molecule.** -/
theorem computedPairCount_canonical_eq_detected (input : CertifiedLocalizedCIPInput)
    (τ : (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4))
    (hτ : (actualCanonicalMolecule input).reindexFrames τ = input.detectedMultiCenterMolecule)
    (cfg : (actualCanonicalMolecule input).Configuration)
    (c : (actualCanonicalMolecule input).Center) :
    computedPairCount (actualCanonicalMolecule input) cfg c =
      physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule
        (Eq.mp (congrArg MultiCenterMolecule.Configuration hτ)
          ((actualCanonicalMolecule input).reindexConfiguration τ cfg))
        (Eq.mp (congrArg MultiCenterMolecule.Center hτ) c) := by
  rw [computedPairCount_eq, physicalPairCount_congr hτ,
    physicalEnantiomorphicPairCount_reindexFrames]

/-- Such a reindexing always exists. -/
theorem exists_canonical_reindex (input : CertifiedLocalizedCIPInput) :
    ∃ τ : (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4),
      (actualCanonicalMolecule input).reindexFrames τ = input.detectedMultiCenterMolecule :=
  input.exists_reindexFrames_detectedMultiCenterMolecule rfl rfl

/-- The decision is exact on the accepted detected molecule itself (proof-level use; that
molecule's data are not compiled). -/
theorem computedPairCount_detected (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center) :
    computedPairCount input.detectedMultiCenterMolecule cfg c =
      physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg c :=
  computedPairCount_eq _ cfg c

/-! ## The executable coordinate count on the original recursive domain

No configuration is supplied to the executor: `coordinateCfg` is read from the certified spatial
table. The join below shows it gives the physical count of **any** physical configuration of the
detected molecule satisfying the original `RecursiveAuxiliaryPhysicalDomain` at the root. Every
non-root centre is a physical terminal twin or carries calibrated actual coordinates. Root geometry
is not needed: the root's own sign never enters the branch relation. -/

open LocalizedRecursiveAuxiliaryPhysicalDomain RootedBranchTerminalTwinCompletion
open CertifiedLocalizedCIPInput (rationalVolumeSign_eq_zero_iff terminalTwinPair_centerPerm)

/-- Calibration in reindexed frames fixes the coordinate-read sign in canonical frames. -/
theorem coordinateSign_of_reindexedCalibration (input : CertifiedLocalizedCIPInput)
    (τ : (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4))
    (cfg : ((actualCanonicalMolecule input).reindexFrames τ).Configuration)
    (d : (actualCanonicalMolecule input).Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input
      ((actualCanonicalMolecule input).reindexFrames τ) cfg d) :
    (actualCanonicalMolecule input).configurationSign (coordinateCfg input) d =
      permHandedness (cfg d) * permHandedness (τ d) := by
  obtain ⟨p, observed, _nonzero, sign⟩ := calibrated
  let q : Fin 4 → CartesianPoint3 := fun k => p ((τ d)⁻¹ k)
  have hp : ∀ i, p i = q (τ d i) := fun i => by simp [q]
  have qObserved : ∀ k, input.spatialPointAt?
      ((actualCanonicalMolecule input).ligandAtomAt d k) = some (q k) := by
    intro k
    have h := observed ((τ d)⁻¹ k)
    simp only [MultiCenterMolecule.reindexFrames_ligandAtomAt] at h
    rw [show τ d ((τ d)⁻¹ k) = k by simp] at h
    exact h
  have hvec : ∀ k : Fin 4,
      RationalTetrahedralPermutation.pointVector (q 0) (q 1) (q 2) (q 3) k = q k := by
    intro k
    fin_cases k <;> rfl
  have hperm : RationalTetrahedralPermutation.permutedOrientedVolume (q 0) (q 1) (q 2) (q 3) (τ d) =
      orientedVolume (p 0) (p 1) (p 2) (p 3) := by
    simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec, hp]
  have permuted := rationalVolumeSign_permutedOrientedVolume (q 0) (q 1) (q 2) (q 3) (τ d)
  rw [hperm, sign] at permuted
  have hh := permHandedness_mul_self (τ d)
  have qSign : rationalVolumeSign (orientedVolume (q 0) (q 1) (q 2) (q 3)) =
      permHandedness (cfg d) * permHandedness (τ d) := by
    have base : permHandedness (cfg d) =
        rationalVolumeSign (orientedVolume (q 0) (q 1) (q 2) (q 3)) * permHandedness (τ d) :=
      permuted
    rw [base, mul_assoc, hh, mul_one]
  have qNonzero : orientedVolume (q 0) (q 1) (q 2) (q 3) ≠ 0 := by
    intro zero
    have zeroSign := (rationalVolumeSign_eq_zero_iff _).mpr zero
    rw [qSign] at zeroSign
    rcases permHandedness_eq_one_or_eq_neg_one (cfg d) with h1 | h1 <;>
      rcases permHandedness_eq_one_or_eq_neg_one (τ d) with h2 | h2 <;>
      rw [h1, h2] at zeroSign <;> norm_num at zeroSign
  obtain ⟨q', observed', _, sign'⟩ := coordinateCfg_calibrated input d q qObserved qNonzero
  have hq' : ∀ k, q' k = q k := fun k =>
    Option.some.inj ((observed' k).symm.trans (qObserved k))
  rw [← sign', hq' 0, hq' 1, hq' 2, hq' 3, qSign]

private theorem computedPairCount_coordinateCfg_reindexed (input : CertifiedLocalizedCIPInput)
    (τ : (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4))
    (cfg : ((actualCanonicalMolecule input).reindexFrames τ).Configuration)
    (root : (actualCanonicalMolecule input).Center)
    (cases : ∀ center : ((actualCanonicalMolecule input).reindexFrames τ).Center, center ≠ root →
      CertifiedLocalizedCIPInput.ActualPhysicalTerminalTwinCenter input
          ((actualCanonicalMolecule input).reindexFrames τ) center ∨
        ActualPhysicalCalibratedCoordinates input
          ((actualCanonicalMolecule input).reindexFrames τ) cfg center) :
    computedPairCount (actualCanonicalMolecule input) (coordinateCfg input) root =
      physicalEnantiomorphicPairCount ((actualCanonicalMolecule input).reindexFrames τ) cfg
        root := by
  let cfgC : (actualCanonicalMolecule input).Configuration := fun c => cfg c * τ c
  have hcfg : (actualCanonicalMolecule input).reindexConfiguration τ cfgC = cfg := by
    funext c
    simp [cfgC, MultiCenterMolecule.reindexConfiguration_apply]
  rw [computedPairCount_eq, ← hcfg, physicalEnantiomorphicPairCount_reindexFrames]
  apply physicalPairCount_congr_nonTwin
  intro d dRoot twin
  rcases cases d dRoot with twinCase | calibrated
  · obtain ⟨a, b, pair⟩ := twinCase
    exact absurd ⟨a, b, ⟨pair.ne, pair.neighbor_a, pair.neighbor_b, pair.z_eq, pair.mass_eq,
      pair.charge_eq, pair.bond_eq⟩⟩ twin
  · rw [coordinateSign_of_reindexedCalibration input τ cfg d calibrated]
    simp [MultiCenterMolecule.configurationSign, cfgC, permHandedness_mul]

/-- The reindexed form, generalized over the equal target molecule. -/
theorem computedPairCount_coordinateCfg_eq_of_reindex (input : CertifiedLocalizedCIPInput)
    (τ : (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4))
    (M : MultiCenterMolecule input.Atom)
    (hM : (actualCanonicalMolecule input).reindexFrames τ = M)
    (cfg : M.Configuration) (root : M.Center)
    (cases : ∀ center : M.Center, center ≠ root →
      CertifiedLocalizedCIPInput.ActualPhysicalTerminalTwinCenter input M center ∨
        ActualPhysicalCalibratedCoordinates input M cfg center)
    (rootC : (actualCanonicalMolecule input).Center) (sameRoot : rootC.1 = root.1) :
    computedPairCount (actualCanonicalMolecule input) (coordinateCfg input) rootC =
      physicalEnantiomorphicPairCount M cfg root := by
  subst hM
  have rootEq : rootC = root := Subtype.ext sameRoot
  subst rootEq
  exact computedPairCount_coordinateCfg_reindexed input τ cfg rootC cases

/-- **Actual-coordinate join.** The executable count `computedPairCount (actualCanonicalMolecule
input) (coordinateCfg input)` equals the physical enantiomorphic-pair count of every physical
configuration of the accepted detected molecule on the original recursive domain at that root. -/
theorem computedPairCount_coordinateCfg_eq_physical (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : RecursiveAuxiliaryPhysicalDomain input cfg root) :
    computedPairCount (actualCanonicalMolecule input) (coordinateCfg input) ⟨root.1, root.2⟩ =
      physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg root := by
  obtain ⟨τ, hτ⟩ := exists_canonical_reindex input
  exact computedPairCount_coordinateCfg_eq_of_reindex input τ _ hτ cfg root domain.centerCase
    ⟨root.1, root.2⟩ rfl

end TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision

assert_kernel_only TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.actualCanonicalMolecule_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.coordinateCfg_calibrated
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.computedPairCount_canonical_eq_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.exists_canonical_reindex
assert_kernel_only TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.computedPairCount_detected
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.coordinateSign_of_reindexedCalibration
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.computedPairCount_coordinateCfg_eq_of_reindex
assert_kernel_only
  TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision.computedPairCount_coordinateCfg_eq_physical
