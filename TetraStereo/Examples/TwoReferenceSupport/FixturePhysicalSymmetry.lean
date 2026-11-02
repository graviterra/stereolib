import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.Examples.TwoReferenceSupport.FixtureMirror
import TetraStereo.Examples.TwoReferenceSupport.FixtureRootGeometry
import TetraStereo.Examples.TwoReferenceSupport.FixtureCalibration
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FixturePhysicalSymmetry

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open FixtureInventory
open FixtureMirror
open FixtureRootGeometry

abbrev Input := FixtureInventory.Input
abbrev Atom := FixtureInventory.Atom
abbrev Graph := Input.moleculeGraph
noncomputable abbrev Physical := Input.detectedMultiCenterMolecule

/-- Reindex each detected center's original ligand table into the actual canonical
ascending-source-index ligand table. -/
noncomputable def canonicalFrames : Physical.Center → Equiv.Perm (Fin 4) :=
  fun c => (Input.canonicalLigandReindex c)⁻¹

noncomputable abbrev Canonical := Physical.reindexFrames canonicalFrames

noncomputable def canonicalConfiguration : Canonical.Configuration :=
  Physical.reindexConfiguration canonicalFrames FixtureCalibration.actualConfiguration

theorem canonicalConfiguration_eq_calibrated :
    canonicalConfiguration = FixtureCalibration.canonicalConfiguration := by
  funext c
  have h := congrFun FixtureCalibration.canonicalReindex_actualConfiguration c
  simpa [canonicalConfiguration, canonicalFrames,
    MultiCenterMolecule.reindexConfiguration,
    CertifiedLocalizedCIPInput.canonicalReindexConfiguration] using h

theorem canonicalizedLigandAt (c : Canonical.Center) (i : Fin 4) :
    Canonical.ligandAtomAt c i = Input.canonicalLigandAtom ⟨c.1, c.2⟩ i := by
  rw [MultiCenterMolecule.reindexFrames_ligandAtomAt,
    Input.canonicalLigandReindex_spec]
  simp [canonicalFrames]

/-- The accepted graph automorphism, lifted to the molecule with the canonical detected ligand
frames. -/
noncomputable def canonicalMirrorAut : Canonical.Aut :=
  Physical.autReindex canonicalFrames FixtureMirror.mirrorDetectedAut

theorem canonicalMirrorAut_apply (a : Atom) :
    (canonicalMirrorAut : Equiv.Perm Atom) a = FixtureMirror.mirrorPerm a := rfl

/-- The canonical root is fixed by the source arm exchange. -/
theorem canonicalMirror_root_fixed : Canonical.centerPerm canonicalMirrorAut rootCenter = rootCenter := by
  rw [RootedTetrahedralBranchSymmetry.centerPerm_eq_iff]
  change FixtureMirror.mirrorPerm (fixtureAtom 0) = fixtureAtom 0
  decide +kernel

/-- At the canonical root, the mirror exchanges exactly the two nitrogen ligand slots. -/
theorem canonicalMirror_root_N_slots :
    Canonical.ligandPermAt canonicalMirrorAut rootCenter 2 = 3 := by
  apply Canonical.ligandAtomAt_injective rootCenter
  have hmove := Canonical.ligandAtomAt_ligandPermAt
    (e := canonicalMirrorAut) (c := rootCenter) (i := 2)
  rw [canonicalMirror_root_fixed] at hmove
  rw [canonicalizedLigandAt rootCenter 2, canonicalLigandAtom_two] at hmove
  have hmirror : FixtureMirror.mirrorPerm (fixtureAtom 3) = fixtureAtom 18 := by
    decide +kernel
  rw [canonicalMirrorAut_apply, hmirror] at hmove
  rw [canonicalizedLigandAt rootCenter 3, canonicalLigandAtom_three]
  exact hmove

private def graphAutOfCanonical (e : Canonical.Aut) : Graph.Aut :=
  ⟨(e : Equiv.Perm Atom), MultiCenterMolecule.Aut.mem_molAut (m := Canonical) e⟩

private theorem atomZ_eq_of_canonicalAut (e : Canonical.Aut) (a : Atom) :
    Graph.atomZ ((e : Equiv.Perm Atom) a) = Graph.atomZ a :=
  MoleculeGraph.Aut.atomZ_eq (m := Graph) (graphAutOfCanonical e) a

private theorem adj_iff_of_canonicalAut (e : Canonical.Aut) (a b : Atom) :
    Graph.Adj ((e : Equiv.Perm Atom) a) ((e : Equiv.Perm Atom) b) ↔ Graph.Adj a b :=
  MoleculeGraph.Aut.adj_iff (m := Graph) (graphAutOfCanonical e) a b

private theorem carbonNeighborOf18 (a : Atom)
    (adjacent : Graph.Adj (fixtureAtom 18) a)
    (carbon : Graph.atomZ a = 6)
    (notRoot : a ≠ fixtureAtom 0) :
    a = fixtureAtom 19 ∨ a = fixtureAtom 26 := by
  revert adjacent carbon notRoot
  fin_cases a <;> decide +kernel

private theorem carbonNeighborOf19or26 (c a : Atom)
    (center : c = fixtureAtom 19 ∨ c = fixtureAtom 26)
    (adjacent : Graph.Adj c a)
    (carbon : Graph.atomZ a = 6) :
    a = fixtureAtom 22 ∨ a = fixtureAtom 29 := by
  rcases center with rfl | rfl
  · revert adjacent carbon
    fin_cases a <;> decide +kernel
  · revert adjacent carbon
    fin_cases a <;> decide +kernel

/-- Any root-fixing graph automorphism that sends root slot 2 to slot 3 sends atom 3 to atom 18. -/
theorem canonicalAut_rootN_map (e : Canonical.Aut)
    (rootFixed : Canonical.centerPerm e rootCenter = rootCenter)
    (Nslot : Canonical.ligandPermAt e rootCenter 2 = 3) :
    (e : Equiv.Perm Atom) (fixtureAtom 3) = fixtureAtom 18 := by
  have h := Canonical.ligandAtomAt_ligandPermAt (e := e) (c := rootCenter) (i := 2)
  rw [rootFixed, Nslot] at h
  rw [canonicalizedLigandAt rootCenter 2, canonicalizedLigandAt rootCenter 3] at h
  rw [canonicalLigandAtom_two, canonicalLigandAtom_three] at h
  exact h.symm

/-- Under a root-fixing automorphism that sends the first nitrogen to the second, the adjacent
tetrahedral center at atom 4 must land at atom 19 or 26. -/
theorem canonicalAut_atom4_image (e : Canonical.Aut)
    (rootFixed : Canonical.centerPerm e rootCenter = rootCenter)
    (Nslot : Canonical.ligandPermAt e rootCenter 2 = 3) :
    (e : Equiv.Perm Atom) (fixtureAtom 4) = fixtureAtom 19 ∨
      (e : Equiv.Perm Atom) (fixtureAtom 4) = fixtureAtom 26 := by
  have e3 := canonicalAut_rootN_map e rootFixed Nslot
  have hAdj : Graph.Adj (fixtureAtom 18) ((e : Equiv.Perm Atom) (fixtureAtom 4)) := by
    have h := (adj_iff_of_canonicalAut e (fixtureAtom 3) (fixtureAtom 4)).2 (by decide)
    simpa [e3] using h
  have hZ : Graph.atomZ ((e : Equiv.Perm Atom) (fixtureAtom 4)) = 6 := by
    rw [atomZ_eq_of_canonicalAut]
    decide +kernel
  have he0 : (e : Equiv.Perm Atom) (fixtureAtom 0) = fixtureAtom 0 :=
    (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff Canonical e rootCenter).mp rootFixed
  have hne : (e : Equiv.Perm Atom) (fixtureAtom 4) ≠ fixtureAtom 0 := by
    intro h
    have h' : (e : Equiv.Perm Atom) (fixtureAtom 4) =
        (e : Equiv.Perm Atom) (fixtureAtom 0) := by
      simpa [he0] using h
    have := (e : Equiv.Perm Atom).injective h'
    exact (by decide : fixtureAtom 4 ≠ fixtureAtom 0) this
  simpa using carbonNeighborOf18 _ hAdj hZ hne

/-- The corresponding downstream carbon center must land at atom 22 or 29. -/
theorem canonicalAut_atom7_image (e : Canonical.Aut)
    (rootFixed : Canonical.centerPerm e rootCenter = rootCenter)
    (Nslot : Canonical.ligandPermAt e rootCenter 2 = 3) :
    (e : Equiv.Perm Atom) (fixtureAtom 7) = fixtureAtom 22 ∨
      (e : Equiv.Perm Atom) (fixtureAtom 7) = fixtureAtom 29 := by
  obtain h4 | h4 := canonicalAut_atom4_image e rootFixed Nslot
  · have hadj : Graph.Adj (fixtureAtom 19) ((e : Equiv.Perm Atom) (fixtureAtom 7)) := by
      have h := (adj_iff_of_canonicalAut e (fixtureAtom 4) (fixtureAtom 7)).2 (by decide)
      simpa [h4] using h
    have hz : Graph.atomZ ((e : Equiv.Perm Atom) (fixtureAtom 7)) = 6 := by
      rw [atomZ_eq_of_canonicalAut]
      decide +kernel
    exact carbonNeighborOf19or26 _ _ (Or.inl rfl) hadj hz
  · have hadj : Graph.Adj (fixtureAtom 26) ((e : Equiv.Perm Atom) (fixtureAtom 7)) := by
      have h := (adj_iff_of_canonicalAut e (fixtureAtom 4) (fixtureAtom 7)).2 (by decide)
      simpa [h4] using h
    have hz : Graph.atomZ ((e : Equiv.Perm Atom) (fixtureAtom 7)) = 6 := by
      rw [atomZ_eq_of_canonicalAut]
      decide +kernel
    exact carbonNeighborOf19or26 _ _ (Or.inr rfl) hadj hz

def nitrogenCenterZProfile : Fin 4 → Nat
  | 0 => 7
  | 1 => 1
  | 2 => 9
  | _ => 6

def carbonCenterZProfile : Fin 4 → Nat
  | 0 => 6
  | 1 => 1
  | 2 => 17
  | _ => 35

private theorem canonicalZ4 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center4 i) = nitrogenCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands4]
  fin_cases i <;> decide +kernel

private theorem canonicalZ11 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center11 i) = nitrogenCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands11]
  fin_cases i <;> decide +kernel

private theorem canonicalZ19 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center19 i) = nitrogenCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands19]
  fin_cases i <;> decide +kernel

private theorem canonicalZ26 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center26 i) = nitrogenCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands26]
  fin_cases i <;> decide +kernel

private theorem canonicalZ7 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center7 i) = carbonCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands7]
  fin_cases i <;> decide +kernel

private theorem canonicalZ14 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center14 i) = carbonCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands14]
  fin_cases i <;> decide +kernel

private theorem canonicalZ22 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center22 i) = carbonCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands22]
  fin_cases i <;> decide +kernel

private theorem canonicalZ29 (i : Fin 4) :
    Graph.atomZ (Canonical.ligandAtomAt center29 i) = carbonCenterZProfile i := by
  rw [canonicalizedLigandAt, FixtureCalibration.canonicalLigands29]
  fin_cases i <;> decide +kernel

private theorem nitrogenCenterZProfile_injective :
    Function.Injective nitrogenCenterZProfile := by
  decide +kernel

private theorem carbonCenterZProfile_injective :
    Function.Injective carbonCenterZProfile := by
  decide +kernel

private theorem canonicalLigandZ_injective (d : Canonical.Center)
    (hprofile : ∀ i, Graph.atomZ (Canonical.ligandAtomAt d i) =
      (if d.1 = fixtureAtom 4 ∨ d.1 = fixtureAtom 11 ∨
          d.1 = fixtureAtom 19 ∨ d.1 = fixtureAtom 26
       then nitrogenCenterZProfile i else carbonCenterZProfile i)) :
    Function.Injective fun i => Graph.atomZ (Canonical.ligandAtomAt d i) := by
  intro i j h
  have h' : (if d.1 = fixtureAtom 4 ∨ d.1 = fixtureAtom 11 ∨
      d.1 = fixtureAtom 19 ∨ d.1 = fixtureAtom 26
      then nitrogenCenterZProfile i else carbonCenterZProfile i) =
      (if d.1 = fixtureAtom 4 ∨ d.1 = fixtureAtom 11 ∨
      d.1 = fixtureAtom 19 ∨ d.1 = fixtureAtom 26
      then nitrogenCenterZProfile j else carbonCenterZProfile j) := by
    rw [← hprofile i, ← hprofile j]
    exact h
  split at h'
  · exact nitrogenCenterZProfile_injective h'
  · exact carbonCenterZProfile_injective h'

/-- A graph automorphism that preserves each ligand-slot atomic number at the image center has
identity local ligand permutation there. -/
private theorem ligandPerm_identity_of_slotZ
    (e : Canonical.Aut) (source target : Canonical.Center)
    (hcenter : Canonical.centerPerm e source = target)
    (slotZ : ∀ i : Fin 4,
      Graph.atomZ (Canonical.ligandAtomAt source i) =
        Graph.atomZ (Canonical.ligandAtomAt target i))
    (targetZInjective : Function.Injective fun i : Fin 4 =>
      Graph.atomZ (Canonical.ligandAtomAt target i)) :
    Canonical.ligandPermAt e source = 1 := by
  apply Equiv.ext
  intro i
  have hmove := Canonical.ligandAtomAt_ligandPermAt (e := e) (c := source) (i := i)
  rw [hcenter] at hmove
  have hZ := congrArg Graph.atomZ hmove
  have hZ' : Graph.atomZ (Canonical.ligandAtomAt target
      (Canonical.ligandPermAt e source i)) =
      Graph.atomZ (Canonical.ligandAtomAt target i) := by
    calc
      Graph.atomZ (Canonical.ligandAtomAt target (Canonical.ligandPermAt e source i)) =
          Graph.atomZ ((e : Equiv.Perm Atom) (Canonical.ligandAtomAt source i)) := hZ
      _ = Graph.atomZ (Canonical.ligandAtomAt source i) := atomZ_eq_of_canonicalAut e _
      _ = Graph.atomZ (Canonical.ligandAtomAt target i) := slotZ i
  have hi := targetZInjective hZ'
  simpa using hi

private theorem center7_image (e : Canonical.Aut)
    (rootFixed : Canonical.centerPerm e rootCenter = rootCenter)
    (Nslot : Canonical.ligandPermAt e rootCenter 2 = 3) :
    Canonical.centerPerm e center7 = center22 ∨ Canonical.centerPerm e center7 = center29 := by
  obtain h22 | h29 := canonicalAut_atom7_image e rootFixed Nslot
  · exact Or.inl (Subtype.ext h22)
  · exact Or.inr (Subtype.ext h29)

/-- At atom 7, every root automorphism carrying N3 to N18 has identity local ligand order, even
if it sends the carbon stereocenter to either corresponding B center. -/
theorem canonicalAut_ligandPerm7_eq_one (e : Canonical.Aut)
    (rootFixed : Canonical.centerPerm e rootCenter = rootCenter)
    (Nslot : Canonical.ligandPermAt e rootCenter 2 = 3) :
    Canonical.ligandPermAt e center7 = 1 := by
  rcases center7_image e rootFixed Nslot with h22 | h29
  · exact ligandPerm_identity_of_slotZ e center7 center22 h22
      (fun i => by rw [canonicalZ7, canonicalZ22])
      (by
        intro i j h
        change Graph.atomZ (Canonical.ligandAtomAt center22 i) =
          Graph.atomZ (Canonical.ligandAtomAt center22 j) at h
        rw [canonicalZ22 i, canonicalZ22 j] at h
        exact carbonCenterZProfile_injective h)
  · exact ligandPerm_identity_of_slotZ e center7 center29 h29
      (fun i => by rw [canonicalZ7, canonicalZ29])
      (by
        intro i j h
        change Graph.atomZ (Canonical.ligandAtomAt center29 i) =
          Graph.atomZ (Canonical.ligandAtomAt center29 j) at h
        rw [canonicalZ29 i, canonicalZ29 j] at h
        exact carbonCenterZProfile_injective h)

theorem canonicalMirror_center4 : Canonical.centerPerm canonicalMirrorAut center4 = center19 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_center7 : Canonical.centerPerm canonicalMirrorAut center7 = center22 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_center11 : Canonical.centerPerm canonicalMirrorAut center11 = center26 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_center14 : Canonical.centerPerm canonicalMirrorAut center14 = center29 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_center19 : Canonical.centerPerm canonicalMirrorAut center19 = center4 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_center22 : Canonical.centerPerm canonicalMirrorAut center22 = center7 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_center26 : Canonical.centerPerm canonicalMirrorAut center26 = center11 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_center29 : Canonical.centerPerm canonicalMirrorAut center29 = center14 := by
  apply Subtype.ext
  decide +kernel

theorem canonicalMirror_ligandPerm4 : Canonical.ligandPermAt canonicalMirrorAut center4 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center4 center19 canonicalMirror_center4
    (fun i => by rw [canonicalZ4, canonicalZ19])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center19 i) =
        Graph.atomZ (Canonical.ligandAtomAt center19 j) at h
      rw [canonicalZ19 i, canonicalZ19 j] at h
      exact nitrogenCenterZProfile_injective h)

theorem canonicalMirror_ligandPerm7 : Canonical.ligandPermAt canonicalMirrorAut center7 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center7 center22 canonicalMirror_center7
    (fun i => by rw [canonicalZ7, canonicalZ22])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center22 i) =
        Graph.atomZ (Canonical.ligandAtomAt center22 j) at h
      rw [canonicalZ22 i, canonicalZ22 j] at h
      exact carbonCenterZProfile_injective h)

theorem canonicalMirror_ligandPerm11 : Canonical.ligandPermAt canonicalMirrorAut center11 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center11 center26 canonicalMirror_center11
    (fun i => by rw [canonicalZ11, canonicalZ26])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center26 i) =
        Graph.atomZ (Canonical.ligandAtomAt center26 j) at h
      rw [canonicalZ26 i, canonicalZ26 j] at h
      exact nitrogenCenterZProfile_injective h)

theorem canonicalMirror_ligandPerm14 : Canonical.ligandPermAt canonicalMirrorAut center14 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center14 center29 canonicalMirror_center14
    (fun i => by rw [canonicalZ14, canonicalZ29])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center29 i) =
        Graph.atomZ (Canonical.ligandAtomAt center29 j) at h
      rw [canonicalZ29 i, canonicalZ29 j] at h
      exact carbonCenterZProfile_injective h)

theorem canonicalMirror_ligandPerm19 : Canonical.ligandPermAt canonicalMirrorAut center19 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center19 center4 canonicalMirror_center19
    (fun i => by rw [canonicalZ19, canonicalZ4])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center4 i) =
        Graph.atomZ (Canonical.ligandAtomAt center4 j) at h
      rw [canonicalZ4 i, canonicalZ4 j] at h
      exact nitrogenCenterZProfile_injective h)

theorem canonicalMirror_ligandPerm22 : Canonical.ligandPermAt canonicalMirrorAut center22 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center22 center7 canonicalMirror_center22
    (fun i => by rw [canonicalZ22, canonicalZ7])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center7 i) =
        Graph.atomZ (Canonical.ligandAtomAt center7 j) at h
      rw [canonicalZ7 i, canonicalZ7 j] at h
      exact carbonCenterZProfile_injective h)

theorem canonicalMirror_ligandPerm26 : Canonical.ligandPermAt canonicalMirrorAut center26 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center26 center11 canonicalMirror_center26
    (fun i => by rw [canonicalZ26, canonicalZ11])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center11 i) =
        Graph.atomZ (Canonical.ligandAtomAt center11 j) at h
      rw [canonicalZ11 i, canonicalZ11 j] at h
      exact nitrogenCenterZProfile_injective h)

theorem canonicalMirror_ligandPerm29 : Canonical.ligandPermAt canonicalMirrorAut center29 = 1 := by
  exact ligandPerm_identity_of_slotZ canonicalMirrorAut center29 center14 canonicalMirror_center29
    (fun i => by rw [canonicalZ29, canonicalZ14])
    (by
      intro i j h
      change Graph.atomZ (Canonical.ligandAtomAt center14 i) =
        Graph.atomZ (Canonical.ligandAtomAt center14 j) at h
      rw [canonicalZ14 i, canonicalZ14 j] at h
      exact carbonCenterZProfile_injective h)

end FixturePhysicalSymmetry

assert_kernel_only FixturePhysicalSymmetry.canonicalMirrorAut
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_root_fixed
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_root_N_slots
assert_kernel_only FixturePhysicalSymmetry.canonicalAut_rootN_map
assert_kernel_only FixturePhysicalSymmetry.canonicalAut_atom4_image
assert_kernel_only FixturePhysicalSymmetry.canonicalAut_atom7_image
assert_kernel_only FixturePhysicalSymmetry.canonicalAut_ligandPerm7_eq_one
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center4
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center7
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center11
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center14
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center19
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center22
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center26
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_center29
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm4
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm7
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm11
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm14
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm19
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm22
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm26
assert_kernel_only FixturePhysicalSymmetry.canonicalMirror_ligandPerm29
