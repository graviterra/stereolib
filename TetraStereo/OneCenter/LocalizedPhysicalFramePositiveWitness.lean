import TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.OneCenter.LocalizedRootZLabelSignEquivalence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



































namespace TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity

/-! ## The fixture and its four ligand atoms -/

/-- The admitted five-atom fixture of `LocalizedWholeStateModelNonvacuity`. -/
abbrev fixture : LocalizedUniversalReference.Input :=
  LocalizedWholeStateModelNonvacuity.input

/-- The four ligand atoms `1, 2, 3, 4` (F, Cl, Br, I), in slot order. -/
def slotAtom (i : Fin 4) : fixture.certified.Atom :=
  match i.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨2, by decide⟩
  | 2 => ⟨3, by decide⟩
  | _ => ⟨4, by decide⟩

/-! ## The physical graph of the fixture: bonds, single-bondedness, acyclicity -/

/-- The exact adjacency of the fixture: atom `0` is bonded precisely to the other four atoms and
there are no further bonds. -/
theorem adj_iff (u v : fixture.certified.Atom) :
    fixture.certified.moleculeGraph.Adj u v ↔
      (u = centerAtom ∧ v ≠ centerAtom) ∨ (v = centerAtom ∧ u ≠ centerAtom) := by
  fin_cases u <;> fin_cases v <;> decide +kernel

/-- A neighbor of a non-center atom is the center. -/
theorem eq_center_of_adj_of_ne_left {u v : fixture.certified.Atom}
    (h : fixture.certified.moleculeGraph.Adj u v) (hu : u ≠ centerAtom) :
    v = centerAtom := by
  rcases (adj_iff u v).mp h with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact absurd rfl hu
  · rfl

/-- The center is not adjacent to itself. -/
theorem not_adj_center_center :
    ¬ fixture.certified.moleculeGraph.underlyingSimpleGraph.Adj centerAtom centerAtom := by
  intro h
  have h' : fixture.certified.moleculeGraph.Adj centerAtom centerAtom :=
    (MoleculeGraph.underlyingSimpleGraph_adj fixture.certified.moleculeGraph centerAtom
      centerAtom).mp h
  rcases (adj_iff centerAtom centerAtom).mp h' with ⟨-, hne⟩ | ⟨-, hne⟩
  · exact hne rfl
  · exact hne rfl

/-- Each ligand slot atom is adjacent to the center. -/
theorem adj_center_slot (i : Fin 4) :
    fixture.certified.moleculeGraph.Adj centerAtom (slotAtom i) := by
  fin_cases i <;> decide +kernel

/-- Every non-center atom is singly bonded to the center. -/
theorem bond_center_of_ne {v : fixture.certified.Atom} (hv : v ≠ centerAtom) :
    fixture.certified.moleculeGraph.bond centerAtom v = 1 := by
  fin_cases v
  · exact absurd rfl hv
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The fixture graph has only single bonds on its positive adjacencies. -/
theorem simpleBonded : fixture.certified.moleculeGraph.SimpleBonded := by
  intro u v h
  rcases (adj_iff u v).mp h with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
  · exact bond_center_of_ne hv
  · rw [MoleculeGraph.bond_symm]
    exact bond_center_of_ne hu

/-- The fixture graph (a five-vertex star) is acyclic.  The proof alternates between the center and
its complement along any putative cycle: a closed walk of even length returns to its starting side,
so the center case forces vertex `2` to equal the endpoint, and the leaf case forces vertex `1` to
equal vertex `3`. -/
theorem acyclic : fixture.certified.moleculeGraph.Acyclic := by
  intro v c hc
  have hthree : 3 ≤ c.length := hc.three_le_length
  by_cases hv : v = centerAtom
  · -- The base point is the center: vertices `0` and `2` are both the center.
    have h0 : c.getVert 0 = centerAtom := by simp [hv]
    have h1ne : c.getVert 1 ≠ centerAtom := by
      intro h1
      have a0 : fixture.certified.moleculeGraph.underlyingSimpleGraph.Adj
          (c.getVert 0) (c.getVert 1) :=
        c.adj_getVert_succ (i := 0) (by omega)
      rw [h0, h1] at a0
      exact not_adj_center_center a0
    have h2 : c.getVert 2 = centerAtom :=
      eq_center_of_adj_of_ne_left
        (by simpa using c.adj_getVert_succ (i := 1) (by omega)) h1ne
    have hlen : c.getVert c.length = centerAtom := by simp [hv]
    have heq : 2 = c.length :=
      hc.getVert_injOn
        (show (2 : ℕ) ∈ {i : ℕ | 1 ≤ i ∧ i ≤ c.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (show c.length ∈ {i : ℕ | 1 ≤ i ∧ i ≤ c.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (h2.trans hlen.symm)
    omega
  · -- The base point is a leaf: vertices `1` and `3` are both the center.
    have h0 : c.getVert 0 = v := by simp
    have h1 : c.getVert 1 = centerAtom :=
      eq_center_of_adj_of_ne_left
        (by simpa using c.adj_getVert_succ (i := 0) (by omega))
        (fun h => hv (h0.symm.trans h))
    have h2ne : c.getVert 2 ≠ centerAtom := by
      intro h2
      have a1 : fixture.certified.moleculeGraph.underlyingSimpleGraph.Adj
          (c.getVert 1) (c.getVert 2) :=
        c.adj_getVert_succ (i := 1) (by omega)
      rw [h1, h2] at a1
      exact not_adj_center_center a1
    have h3 : c.getVert 3 = centerAtom :=
      eq_center_of_adj_of_ne_left
        (by simpa using c.adj_getVert_succ (i := 2) (by omega)) h2ne
    have heq : 1 = 3 :=
      hc.getVert_injOn
        (show (1 : ℕ) ∈ {i : ℕ | 1 ≤ i ∧ i ≤ c.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (show (3 : ℕ) ∈ {i : ℕ | 1 ≤ i ∧ i ≤ c.length} by
          simp only [Set.mem_setOf_eq]; omega)
        (h1.trans h3.symm)
    omega

/-! ## Atomic numbers of the four ligand atoms -/

/-- The graph atomic numbers of the four ligand atoms, in slot order. -/
theorem atomZ_slot (i : Fin 4) :
    fixture.certified.moleculeGraph.atomZ (slotAtom i) =
      match i.val with
      | 0 => 9
      | 1 => 17
      | 2 => 35
      | _ => 53 := by
  rw [CertifiedLocalizedCIPInput.moleculeGraph,
    SemanticMolecule.toLocalizedMoleculeGraph_atomZ]
  fin_cases i <;> rfl

@[simp] theorem atomZ_slot_zero :
    fixture.certified.moleculeGraph.atomZ (slotAtom 0) = 9 := by
  simpa using atomZ_slot 0

@[simp] theorem atomZ_slot_one :
    fixture.certified.moleculeGraph.atomZ (slotAtom 1) = 17 := by
  simpa using atomZ_slot 1

@[simp] theorem atomZ_slot_two :
    fixture.certified.moleculeGraph.atomZ (slotAtom 2) = 35 := by
  simpa using atomZ_slot 2

@[simp] theorem atomZ_slot_three :
    fixture.certified.moleculeGraph.atomZ (slotAtom 3) = 53 := by
  simpa using atomZ_slot 3

/-- A neighbor of the center is one of the four ligand atoms. -/
theorem eq_slot_of_adj_center {a : fixture.certified.Atom}
    (h : fixture.certified.moleculeGraph.Adj centerAtom a) :
    ∃ i : Fin 4, slotAtom i = a := by
  fin_cases a
  · exact absurd h (by decide +kernel)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- Distinct neighbors of the center have distinct atomic numbers. -/
theorem atomZ_injective_of_adj_center {a b : fixture.certified.Atom}
    (ha : fixture.certified.moleculeGraph.Adj centerAtom a)
    (hb : fixture.certified.moleculeGraph.Adj centerAtom b)
    (h : fixture.certified.moleculeGraph.atomZ a = fixture.certified.moleculeGraph.atomZ b) :
    a = b := by
  obtain ⟨i, rfl⟩ := eq_slot_of_adj_center ha
  obtain ⟨j, rfl⟩ := eq_slot_of_adj_center hb
  fin_cases i <;> fin_cases j <;>
    simp_all [atomZ_slot_zero, atomZ_slot_one, atomZ_slot_two, atomZ_slot_three]

/-! ## Root atomic number of an actual frame cursor -/

/-- The root atomic number of a frame cursor whose node has a current atom is the molecular graph's
atomic number of that atom, for *either* real or duplicate provenance. -/
theorem rootAtomicNumberAt_eq_atomZ_of_current
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (index : Fin 4) (atom : input.Atom)
    (current : (frame.cursorAt index).occurrence.1.node.current? = some atom) :
    frame.rootAtomicNumberAt input index = input.moleculeGraph.atomZ atom := by
  unfold CertifiedLocalizedCIPInput.LocalizedOccurrenceFourLigandFrame.rootAtomicNumberAt
    CertifiedLocalizedCIPInput.localizedRerootCursorRootAtomicNumber
  rw [MoleculeGraph.officialNodeAtomLabel, current]
  cases (frame.cursorAt index).occurrence.1.node.provenance <;> rfl

/-! ## The canonical ligand slot enumeration of the four center neighbors -/

/-- The four ligand atoms package as the four neighbors of the center. -/
def slotNeighbor (i : Fin 4) : fixture.certified.moleculeGraph.Neighbor centerAtom :=
  ⟨slotAtom i, adj_center_slot i⟩

theorem slotNeighbor_injective : Function.Injective slotNeighbor := by
  intro i j h
  have h' : slotAtom i = slotAtom j := congrArg Subtype.val h
  fin_cases i <;> fin_cases j <;> simp_all [slotAtom]

theorem slotNeighbor_surjective : Function.Surjective slotNeighbor := by
  intro n
  obtain ⟨i, hi⟩ := eq_slot_of_adj_center n.2
  exact ⟨i, Subtype.ext hi⟩

/-- The canonical enumeration `Fin 4 ≃ Neighbor centerAtom` by the four ligand atoms. -/
noncomputable def slotEquiv : Fin 4 ≃ fixture.certified.moleculeGraph.Neighbor centerAtom :=
  Equiv.ofBijective slotNeighbor ⟨slotNeighbor_injective, slotNeighbor_surjective⟩

/-! ## Physical coordinates and the nondegenerate base determinant -/

/-- The fixture's exact rational tetrahedral coordinates at the four ligand atoms. -/
def physicalPointAt (i : Fin 4) : CartesianPoint3 :=
  match i.val with
  | 0 => { x := -1, y := -1, z := 1 }
  | 1 => { x := -1, y := 1, z := -1 }
  | 2 => { x := 1, y := -1, z := -1 }
  | _ => { x := 1, y := 1, z := 1 }

/-- The four ligand coordinates span a nondegenerate tetrahedron. -/
theorem physicalPointAt_volume_ne_zero :
    CartesianPoint3.orientedVolume
      (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3) ≠ 0 := by
  norm_num [physicalPointAt, CartesianPoint3.orientedVolume]

/-- The executable spatial lookup at each ligand slot reads its fixture coordinate. -/
theorem spatialPointAt_slot (i : Fin 4) :
    fixture.certified.spatialPointAt? (slotAtom i) = some (physicalPointAt i) := by
  fin_cases i <;> decide +kernel

/-! ## The actual frame permutation and the physical points written by it -/

/-- The actual frame permutation relative to the canonical ligand slot enumeration. -/
noncomputable def framePermutation
    (ligand : Fin 4 ≃ fixture.certified.moleculeGraph.Neighbor centerAtom) :
    Equiv.Perm (Fin 4) :=
  ligand.trans slotEquiv.symm

/-- The frame's `index`-th cursor reads the canonical slot selected by the frame permutation. -/
theorem ligand_eq_slot
    (ligand : Fin 4 ≃ fixture.certified.moleculeGraph.Neighbor centerAtom) (i : Fin 4) :
    (ligand i).1 = slotAtom (framePermutation ligand i) := by
  have h : slotEquiv (framePermutation ligand i) = ligand i := by
    rw [framePermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  simpa using congrArg Subtype.val h.symm

/-- The physical points written in actual frame order. -/
noncomputable def pointsAt
    (ligand : Fin 4 ≃ fixture.certified.moleculeGraph.Neighbor centerAtom)
    (i : Fin 4) : CartesianPoint3 :=
  physicalPointAt (framePermutation ligand i)

/-! ## Frame-level physical facts -/

/-- The actual frame's written-order determinant is nonzero.  The fixed rational base frame has a
nonzero determinant and any frame ordering only changes its sign. -/
theorem pointsAt_volume_nonzero
    (ligand : Fin 4 ≃ fixture.certified.moleculeGraph.Neighbor centerAtom) :
    CartesianPoint3.orientedVolume
      (pointsAt ligand 0) (pointsAt ligand 1) (pointsAt ligand 2) (pointsAt ligand 3) ≠ 0 := by
  have calibrated : ∀ index : Fin 4,
      pointsAt ligand index = physicalPointAt (framePermutation ligand index) := fun _ => rfl
  rw [orientedVolume_calibrated_eq (pointsAt ligand) physicalPointAt
      (framePermutation ligand) calibrated,
    RationalTetrahedralPermutation.permutedOrientedVolume_eq_if_permutationIsEven]
  have base : CartesianPoint3.orientedVolume
      (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3) ≠ 0 :=
    physicalPointAt_volume_ne_zero
  cases RawMolecule.permutationIsEven
      (Rule6HandednessSemantics.finFourPermutationList (framePermutation ligand)) with
  | false => simpa using neg_ne_zero.mpr base
  | true => simpa using base

/-- The actual frame's four root atomic numbers are pairwise distinct. -/
theorem frame_separated
    (frame : fixture.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel fixture))
    (ligand : Fin 4 ≃ fixture.certified.moleculeGraph.Neighbor centerAtom)
    (ligandSpec : ∀ i : Fin 4,
      (frame.cursorAt i).occurrence.1.node.current? = some (ligand i).1) :
    fixture.certified.ConstitutionallyAtomicNumberSeparatedFrame frame := by
  intro left right _different equalRoot
  have equalZ : fixture.certified.moleculeGraph.atomZ (ligand left).1 =
      fixture.certified.moleculeGraph.atomZ (ligand right).1 := by
    rw [← rootAtomicNumberAt_eq_atomZ_of_current fixture.certified frame left
        (ligand left).1 (ligandSpec left),
      ← rootAtomicNumberAt_eq_atomZ_of_current fixture.certified frame right
        (ligand right).1 (ligandSpec right)]
    exact equalRoot
  have equalAtom : (ligand left).1 = (ligand right).1 :=
    atomZ_injective_of_adj_center (ligand left).2 (ligand right).2 equalZ
  exact _different (ligand.injective (Subtype.ext equalAtom))

/-- Each actual frame cursor reads its fixture coordinate. -/
theorem frame_spatial
    (frame : fixture.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel fixture))
    (ligand : Fin 4 ≃ fixture.certified.moleculeGraph.Neighbor centerAtom)
    (ligandSpec : ∀ i : Fin 4,
      (frame.cursorAt i).occurrence.1.node.current? = some (ligand i).1)
    (i : Fin 4) :
    fixture.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
      some (pointsAt ligand i) := by
  have slot := spatialPointAt_slot (framePermutation ligand i)
  simpa [CertifiedLocalizedCIPInput.localizedRerootCursorSpatialPoint?,
    ligandSpec i, pointsAt, ligand_eq_slot ligand i, Option.bind_some] using slot



/-- The carrier fuel of the five-atom fixture is sufficient. -/
theorem fixture_enough :
    fixture.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel fixture := by
  rw [LocalizedWholeStateModelNonvacuity.carrierFuel_eq]
  decide +kernel

/-- Atom `0` of the fixture is a tetrahedral center. -/
theorem fixture_tetrahedral :
    fixture.certified.moleculeGraph.IsTetrahedralCenter centerAtom :=
  (fixture.certified.moleculeGraph.mem_tetrahedralCenterSet centerAtom).1
    LocalizedWholeStateModelNonvacuity.centerAtom_mem

/-- The final occurrence's node is the real center node. -/
theorem fixture_oObserved :
    target.1.node.current? = some centerAtom :=
  LocalizedWholeStateModelNonvacuity.target_realCenterNode.2

/-! ## The actual positive endpoint -/

/-- **Positive actual reference state at the physical tetrahedral center.**  The generated
reference state at the final occurrence of the fixture's center is chiral. -/
theorem exists_chiral_referenceState :
    ∃ rs : RS,
      LocalizedUniversalReference.referenceState fixture target = some (.chiral rs) := by
  classical
  obtain ⟨frame, ligand, frameComputed, ligandSpec⟩ :=
    fixture.certified.exists_localizedOccurrenceFourLigandFrame_and_neighborEquiv
      simpleBonded acyclic fixture_enough target fixture_oObserved fixture_tetrahedral
  have derived : fixture.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    fixture.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  exact exists_chiral_referenceState_of_nondegenerateFrame fixture
    LocalizedWholeStateModelNonvacuity.input_noDoubleRecords target frame derived
    (frame_separated frame ligand ligandSpec)
    LocalizedWholeStateModelNonvacuity.center
    LocalizedWholeStateModelNonvacuity.target_realCenterNode
    (pointsAt ligand) (frame_spatial frame ligand ligandSpec)
    (pointsAt_volume_nonzero ligand)

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.fixture
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.slotAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.adj_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.eq_center_of_adj_of_ne_left
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.not_adj_center_center
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.adj_center_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.bond_center_of_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.acyclic
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.atomZ_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.atomZ_slot_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.atomZ_slot_one
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.atomZ_slot_two
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.atomZ_slot_three
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.eq_slot_of_adj_center
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.atomZ_injective_of_adj_center
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.rootAtomicNumberAt_eq_atomZ_of_current
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.slotNeighbor
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.slotNeighbor_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.slotNeighbor_surjective
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.slotEquiv
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.physicalPointAt
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.physicalPointAt_volume_ne_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.spatialPointAt_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.framePermutation
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.ligand_eq_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.pointsAt
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.pointsAt_volume_nonzero
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.frame_separated
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.frame_spatial
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.fixture_enough
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.fixture_tetrahedral
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.fixture_oObserved
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness.exists_chiral_referenceState

end TetraStereo.OneCenter.LocalizedPhysicalFramePositiveWitness
