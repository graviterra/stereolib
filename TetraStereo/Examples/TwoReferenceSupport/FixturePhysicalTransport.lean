import TetraStereo.Examples.TwoReferenceSupport.FixturePhysicalSymmetry
import TetraStereo.Examples.TwoReferenceSupport.FixtureCalibration
import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.Examples.TwoReferenceSupport.FixtureRootGeometry
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FixturePhysicalTransport

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.MultiCenterMolecule
open FixtureInventory
open FixtureRootGeometry
open FixturePhysicalSymmetry

abbrev Input := FixturePhysicalSymmetry.Input
abbrev Atom := FixturePhysicalSymmetry.Atom
abbrev Graph := Input.moleculeGraph
noncomputable abbrev Physical := FixturePhysicalSymmetry.Physical
noncomputable abbrev Canonical := FixturePhysicalSymmetry.Canonical

/-- The center at atom 7 lies in the root's branch whose canonical attachment is atom 3. -/
theorem center7_reaches_root_slot2 :
    LigandBranchReaches Canonical rootCenter 2 center7.1 := by
  have h34 : Canonical.mol.underlyingSimpleGraph.Adj (fixtureAtom 3) (fixtureAtom 4) := by
    rw [MoleculeGraph.underlyingSimpleGraph_adj]
    decide +kernel
  have h47 : Canonical.mol.underlyingSimpleGraph.Adj (fixtureAtom 4) (fixtureAtom 7) := by
    rw [MoleculeGraph.underlyingSimpleGraph_adj]
    decide +kernel
  have hstart : Canonical.ligandAtomAt rootCenter 2 = fixtureAtom 3 := by
    rw [canonicalizedLigandAt, canonicalLigandAtom_two]
  unfold LigandBranchReaches
  rw [hstart]
  let p : Canonical.mol.underlyingSimpleGraph.Walk (fixtureAtom 3) (fixtureAtom 7) :=
    SimpleGraph.Walk.cons h34 (SimpleGraph.Walk.cons h47 SimpleGraph.Walk.nil)
  refine ⟨p, ?_⟩
  change fixtureAtom 0 ∉ p.support
  simp [p]
  decide +kernel

private theorem canonicalSign7_value :
    Canonical.configurationSign canonicalConfiguration center7 = 1 := by
  change permHandedness (canonicalConfiguration center7) = 1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center7, fixtureAtom]

private theorem canonicalSign4_value :
    Canonical.configurationSign canonicalConfiguration center4 = 1 := by
  change permHandedness (canonicalConfiguration center4) = 1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center4, fixtureAtom]

private theorem canonicalSign11_value :
    Canonical.configurationSign canonicalConfiguration center11 = -1 := by
  change permHandedness (canonicalConfiguration center11) = -1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center11, fixtureAtom,
    FixtureCalibration.reverseFrame]

private theorem canonicalSign14_value :
    Canonical.configurationSign canonicalConfiguration center14 = 1 := by
  change permHandedness (canonicalConfiguration center14) = 1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center14, fixtureAtom]

private theorem canonicalSign19_value :
    Canonical.configurationSign canonicalConfiguration center19 = -1 := by
  change permHandedness (canonicalConfiguration center19) = -1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center19, fixtureAtom,
    FixtureCalibration.reverseFrame]

private theorem canonicalSign22_value :
    Canonical.configurationSign canonicalConfiguration center22 = -1 := by
  change permHandedness (canonicalConfiguration center22) = -1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center22, fixtureAtom,
    FixtureCalibration.reverseFrame]

private theorem canonicalSign26_value :
    Canonical.configurationSign canonicalConfiguration center26 = 1 := by
  change permHandedness (canonicalConfiguration center26) = 1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center26, fixtureAtom]

private theorem canonicalSign29_value :
    Canonical.configurationSign canonicalConfiguration center29 = -1 := by
  change permHandedness (canonicalConfiguration center29) = -1
  rw [canonicalConfiguration_eq_calibrated]
  simp [FixtureCalibration.canonicalConfiguration, center29, fixtureAtom,
    FixtureCalibration.reverseFrame]

private theorem canonicalMirror_sign4 :
    Canonical.configurationSign canonicalConfiguration center4 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center4) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center4) := by
  rw [canonicalMirror_ligandPerm4, canonicalMirror_center4,
    canonicalSign4_value, canonicalSign19_value]
  norm_num

private theorem canonicalMirror_sign7 :
    Canonical.configurationSign canonicalConfiguration center7 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center7) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center7) := by
  rw [canonicalMirror_ligandPerm7, canonicalMirror_center7,
    canonicalSign7_value, canonicalSign22_value]
  norm_num

private theorem canonicalMirror_sign11 :
    Canonical.configurationSign canonicalConfiguration center11 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center11) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center11) := by
  rw [canonicalMirror_ligandPerm11, canonicalMirror_center11,
    canonicalSign11_value, canonicalSign26_value]
  norm_num

private theorem canonicalMirror_sign14 :
    Canonical.configurationSign canonicalConfiguration center14 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center14) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center14) := by
  rw [canonicalMirror_ligandPerm14, canonicalMirror_center14,
    canonicalSign14_value, canonicalSign29_value]
  norm_num

private theorem canonicalMirror_sign19 :
    Canonical.configurationSign canonicalConfiguration center19 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center19) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center19) := by
  rw [canonicalMirror_ligandPerm19, canonicalMirror_center19,
    canonicalSign19_value, canonicalSign4_value]
  norm_num

private theorem canonicalMirror_sign22 :
    Canonical.configurationSign canonicalConfiguration center22 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center22) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center22) := by
  rw [canonicalMirror_ligandPerm22, canonicalMirror_center22,
    canonicalSign22_value, canonicalSign7_value]
  norm_num

private theorem canonicalMirror_sign26 :
    Canonical.configurationSign canonicalConfiguration center26 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center26) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center26) := by
  rw [canonicalMirror_ligandPerm26, canonicalMirror_center26,
    canonicalSign26_value, canonicalSign11_value]
  norm_num

private theorem canonicalMirror_sign29 :
    Canonical.configurationSign canonicalConfiguration center29 *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut center29) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut center29) := by
  rw [canonicalMirror_ligandPerm29, canonicalMirror_center29,
    canonicalSign29_value, canonicalSign14_value]
  norm_num

/-- Every detected nonroot center obeys the calibrated mirror sign relation. -/
private theorem canonicalMirror_sign_at_reached_center (d : Canonical.Center)
    (reaches : LigandBranchReaches Canonical rootCenter 2 d.1) :
    Canonical.configurationSign canonicalConfiguration d *
        permHandedness (Canonical.ligandPermAt canonicalMirrorAut d) =
      -Canonical.configurationSign canonicalConfiguration
        (Canonical.centerPerm canonicalMirrorAut d) := by
  have hmem : d.1 ∈ Input.tetrahedralCenterSet := d.2
  rw [detectedCenterSet] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h0 | h4 | h7 | h11 | h14 | h19 | h22 | h26 | h29
  · exfalso
    have heq : d = rootCenter := by
      apply Subtype.ext
      simpa [rootCenter] using h0
    subst d
    unfold LigandBranchReaches at reaches
    rcases reaches with ⟨p, avoidsRoot⟩
    exact avoidsRoot (SimpleGraph.Walk.end_mem_support p)
  · have heq : d = center4 := Subtype.ext h4
    subst d
    exact canonicalMirror_sign4
  · have heq : d = center7 := Subtype.ext h7
    subst d
    exact canonicalMirror_sign7
  · have heq : d = center11 := Subtype.ext h11
    subst d
    exact canonicalMirror_sign11
  · have heq : d = center14 := Subtype.ext h14
    subst d
    exact canonicalMirror_sign14
  · have heq : d = center19 := Subtype.ext h19
    subst d
    exact canonicalMirror_sign19
  · have heq : d = center22 := Subtype.ext h22
    subst d
    exact canonicalMirror_sign22
  · have heq : d = center26 := Subtype.ext h26
    subst d
    exact canonicalMirror_sign26
  · have heq : d = center29 := Subtype.ext h29
    subst d
    exact canonicalMirror_sign29

/-- The source arm exchange is a mirror transport between the actual canonical N-root slots. -/
theorem mirrorTransport_canonical_root_2_3 :
    MirrorTransport Canonical canonicalConfiguration rootCenter 2 3 := by
  refine ⟨canonicalMirrorAut, canonicalMirror_root_fixed, canonicalMirror_root_N_slots, ?_⟩
  intro d reaches
  simpa using canonicalMirror_sign_at_reached_center d reaches

/-- The N3 to N18 branch exchange cannot be proper: at the reached carbon center, the distinct
neighbor labels force identity local order while the calibrated canonical signs oppose. -/
theorem not_properTransport_canonical_root_2_3 :
    ¬ ProperTransport Canonical canonicalConfiguration rootCenter 2 3 := by
  rintro ⟨e, hroot, hslot, hsign⟩
  have himage := canonicalAut_atom7_image e hroot hslot
  have hlocal := canonicalAut_ligandPerm7_eq_one e hroot hslot
  have hbranch := hsign center7 center7_reaches_root_slot2
  rw [hlocal] at hbranch
  rcases himage with h22 | h29
  · have hcenter : Canonical.centerPerm e center7 = center22 := Subtype.ext h22
    rw [hcenter, canonicalSign7_value, canonicalSign22_value] at hbranch
    norm_num [permHandedness_one] at hbranch
  · have hcenter : Canonical.centerPerm e center7 = center29 := Subtype.ext h29
    rw [hcenter, canonicalSign7_value, canonicalSign29_value] at hbranch
    norm_num [permHandedness_one] at hbranch

theorem not_properTransport_canonical_root_3_2 :
    ¬ ProperTransport Canonical canonicalConfiguration rootCenter 3 2 := by
  intro h
  have hinv := RootedTetrahedralBranchSymmetry.branchTransport_inverse
    Canonical canonicalConfiguration rootCenter (by simpa [ProperTransport] using h)
  exact not_properTransport_canonical_root_2_3 (by simpa [ProperTransport] using hinv)

private def canonicalRootZProfile : Fin 4 → Nat
  | 0 => 1
  | 1 => 17
  | _ => 7

private theorem canonicalRootZ (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt rootCenter i) = canonicalRootZProfile i := by
  rw [canonicalizedLigandAt]
  fin_cases i
  · change Graph.atomZ (Input.canonicalLigandAtom FixtureRootGeometry.rootCenter (0 : Fin 4)) = 1
    rw [FixtureRootGeometry.canonicalLigandAtom_zero]
    decide +kernel
  · change Graph.atomZ (Input.canonicalLigandAtom FixtureRootGeometry.rootCenter (1 : Fin 4)) = 17
    rw [FixtureRootGeometry.canonicalLigandAtom_one]
    decide +kernel
  · change Graph.atomZ (Input.canonicalLigandAtom FixtureRootGeometry.rootCenter (2 : Fin 4)) = 7
    rw [FixtureRootGeometry.canonicalLigandAtom_two]
    decide +kernel
  · change Graph.atomZ (Input.canonicalLigandAtom FixtureRootGeometry.rootCenter (3 : Fin 4)) = 7
    rw [FixtureRootGeometry.canonicalLigandAtom_three]
    decide +kernel

private def graphAutOfCanonical (e : Canonical.Aut) : Graph.Aut :=
  ⟨(e : Equiv.Perm Atom), MultiCenterMolecule.Aut.mem_molAut (m := Canonical) e⟩

private theorem canonicalAut_atomZ_eq (e : Canonical.Aut) (a : Atom) :
    Graph.atomZ ((e : Equiv.Perm Atom) a) = Graph.atomZ a :=
  MoleculeGraph.Aut.atomZ_eq (m := Graph) (graphAutOfCanonical e) a

private theorem canonicalRootZProfile_pair_classification :
    ∀ i j : Fin 4, i ≠ j → canonicalRootZProfile i = canonicalRootZProfile j →
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  decide +kernel

/-- Every pair of distinct root slots is proper-distinguishable. The only equal-Z atom pair is
N3/N18, and that pair was excluded by the reached-center sign contradiction. -/
theorem pairwiseProperDistinguishable_canonical_root :
    PairwiseProperDistinguishable Canonical canonicalConfiguration rootCenter := by
  intro i j hij hproper
  rcases hproper with ⟨e, hroot, hslot, hsign⟩
  have hcanonical : ProperTransport Canonical canonicalConfiguration rootCenter i j :=
    ⟨e, hroot, hslot, hsign⟩
  have hmove := Canonical.ligandAtomAt_ligandPermAt (e := e) (c := rootCenter) (i := i)
  rw [hroot, hslot] at hmove
  have hZ := congrArg Graph.atomZ hmove
  rw [canonicalAut_atomZ_eq] at hZ
  rw [canonicalRootZ j, canonicalRootZ i] at hZ
  have hpair := canonicalRootZProfile_pair_classification i j hij hZ.symm
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact not_properTransport_canonical_root_2_3 hcanonical
  · exact not_properTransport_canonical_root_3_2 hcanonical

/-- Transfer the all-pairs proper-distinguishability fact back to the detector's actual local
ligand tables and calibrated physical configuration. -/
theorem pairwiseProperDistinguishable_actual_root :
    PairwiseProperDistinguishable Physical FixtureCalibration.actualConfiguration rootCenter := by
  apply (pairwiseProperDistinguishable_reindexFrames_iff Physical canonicalFrames
    FixtureCalibration.actualConfiguration rootCenter).mp
  exact pairwiseProperDistinguishable_canonical_root

/-- The canonical mirror transport transports back to the actual detector-indexed ligand slots. -/
theorem mirrorTransport_actual_root :
    MirrorTransport Physical FixtureCalibration.actualConfiguration rootCenter
      (canonicalFrames rootCenter 2) (canonicalFrames rootCenter 3) := by
  exact (branchTransport_reindexFrames_iff Physical canonicalFrames
    FixtureCalibration.actualConfiguration rootCenter 2 3 true).1
    mirrorTransport_canonical_root_2_3

/-- The canonical root's enantiomorphic relation consists exactly of the N3/N18 pair and its
reverse. Mirror transport identifies the only possible equal-Z pair; the forward pair is the
constructed mirror with the proper transport ruled out above, and symmetry supplies its reverse. -/
theorem enantiomorphic_canonical_root_iff (i j : Fin 4) :
    Enantiomorphic Canonical canonicalConfiguration rootCenter i j ↔
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  constructor
  · rintro ⟨different, mirror, _⟩
    rcases mirror with ⟨e, rootFixed, slotMove, _⟩
    have hmove := Canonical.ligandAtomAt_ligandPermAt
      (e := e) (c := rootCenter) (i := i)
    rw [rootFixed, slotMove] at hmove
    have hZ := congrArg Graph.atomZ hmove
    rw [canonicalAut_atomZ_eq] at hZ
    rw [canonicalRootZ j, canonicalRootZ i] at hZ
    exact canonicalRootZProfile_pair_classification i j different hZ.symm
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by decide, mirrorTransport_canonical_root_2_3,
        not_properTransport_canonical_root_2_3⟩
    · exact RootedTetrahedralBranchSymmetry.enantiomorphic_symm
        Canonical canonicalConfiguration rootCenter
        ⟨by decide, mirrorTransport_canonical_root_2_3,
          not_properTransport_canonical_root_2_3⟩

/-- There is exactly one unordered enantiomorphic pair at the canonical root. -/
theorem physicalEnantiomorphicPairCount_canonical_root_eq_one :
    physicalEnantiomorphicPairCount Canonical canonicalConfiguration rootCenter = 1 := by
  rw [physicalEnantiomorphicPairCount_eq_one_iff]
  refine ⟨2, 3, by decide, ?_, ?_⟩
  · exact (enantiomorphic_canonical_root_iff 2 3).2 (Or.inl ⟨rfl, rfl⟩)
  · intro a b _different enantiomorphic
    rcases (enantiomorphic_canonical_root_iff a b).mp enantiomorphic with pair | pair
    · exact Or.inl pair
    · exact Or.inr pair

/-- Reindexing invariance transfers the exactly-one count from canonical source-index slots to
the actual detector's physical ligand enumeration. -/
theorem physicalEnantiomorphicPairCount_actual_root_eq_one :
    physicalEnantiomorphicPairCount Physical FixtureCalibration.actualConfiguration rootCenter = 1 := by
  calc
    physicalEnantiomorphicPairCount Physical FixtureCalibration.actualConfiguration rootCenter =
        physicalEnantiomorphicPairCount Canonical canonicalConfiguration rootCenter := by
      exact (physicalEnantiomorphicPairCount_reindexFrames Physical canonicalFrames
        FixtureCalibration.actualConfiguration rootCenter).symm
    _ = 1 := physicalEnantiomorphicPairCount_canonical_root_eq_one

end FixturePhysicalTransport

assert_kernel_only FixturePhysicalTransport.center7_reaches_root_slot2
assert_kernel_only FixturePhysicalTransport.not_properTransport_canonical_root_2_3
assert_kernel_only FixturePhysicalTransport.not_properTransport_canonical_root_3_2
assert_kernel_only FixturePhysicalTransport.mirrorTransport_canonical_root_2_3
assert_kernel_only FixturePhysicalTransport.pairwiseProperDistinguishable_canonical_root
assert_kernel_only FixturePhysicalTransport.pairwiseProperDistinguishable_actual_root
assert_kernel_only FixturePhysicalTransport.mirrorTransport_actual_root
assert_kernel_only FixturePhysicalTransport.enantiomorphic_canonical_root_iff
assert_kernel_only FixturePhysicalTransport.physicalEnantiomorphicPairCount_canonical_root_eq_one
assert_kernel_only FixturePhysicalTransport.physicalEnantiomorphicPairCount_actual_root_eq_one
