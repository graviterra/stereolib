import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FixtureRigidity

open TetraStereo.OneCenter
open FixtureInventory

noncomputable abbrev Physical := Input.detectedMultiCenterMolecule

/-- The graph's atomic-number accessor is the source atom's semantic atomic number. -/
theorem graphAtomZ_eq_source (a : Atom) :
    Input.moleculeGraph.atomZ a =
      (TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture.source.molecule.atoms.get a).element.atomicNumber := by
  rfl

/-- Convert a source-derived number map to the graph's actual atomic-number map. -/
theorem graphAtomZ_map_eq_atomicNumbers (xs : List Atom) :
    xs.map Input.moleculeGraph.atomZ = atomicNumbers xs := by
  unfold atomicNumbers
  apply List.map_congr_left
  intro a _ha
  exact graphAtomZ_eq_source a


/-- Atomic number is injective across every actual neighbor of center 4. -/
theorem atomZ_injective_neighbors4 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 4) a →
      Input.moleculeGraph.Adj (fixtureAtom 4) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors4.toFinset := by
    rw [priorityNeighbors4_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 4) a).2 ha
  have hbSet : b ∈ priorityNeighbors4.toFinset := by
    rw [priorityNeighbors4_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 4) b).2 hb
  have haList : a ∈ priorityNeighbors4 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors4 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors4.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers4_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid4 : ConstitutionallyRigid Physical center4 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 4) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 4) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors4 a b ha hb hz

/-- Atomic number is injective across every actual neighbor of center 7. -/
theorem atomZ_injective_neighbors7 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 7) a →
      Input.moleculeGraph.Adj (fixtureAtom 7) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors7.toFinset := by
    rw [priorityNeighbors7_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 7) a).2 ha
  have hbSet : b ∈ priorityNeighbors7.toFinset := by
    rw [priorityNeighbors7_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 7) b).2 hb
  have haList : a ∈ priorityNeighbors7 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors7 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors7.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers7_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid7 : ConstitutionallyRigid Physical center7 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 7) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 7) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors7 a b ha hb hz

/-- Atomic number is injective across every actual neighbor of center 11. -/
theorem atomZ_injective_neighbors11 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 11) a →
      Input.moleculeGraph.Adj (fixtureAtom 11) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors11.toFinset := by
    rw [priorityNeighbors11_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 11) a).2 ha
  have hbSet : b ∈ priorityNeighbors11.toFinset := by
    rw [priorityNeighbors11_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 11) b).2 hb
  have haList : a ∈ priorityNeighbors11 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors11 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors11.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers11_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid11 : ConstitutionallyRigid Physical center11 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 11) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 11) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors11 a b ha hb hz

/-- Atomic number is injective across every actual neighbor of center 14. -/
theorem atomZ_injective_neighbors14 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 14) a →
      Input.moleculeGraph.Adj (fixtureAtom 14) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors14.toFinset := by
    rw [priorityNeighbors14_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 14) a).2 ha
  have hbSet : b ∈ priorityNeighbors14.toFinset := by
    rw [priorityNeighbors14_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 14) b).2 hb
  have haList : a ∈ priorityNeighbors14 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors14 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors14.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers14_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid14 : ConstitutionallyRigid Physical center14 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 14) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 14) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors14 a b ha hb hz

/-- Atomic number is injective across every actual neighbor of center 19. -/
theorem atomZ_injective_neighbors19 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 19) a →
      Input.moleculeGraph.Adj (fixtureAtom 19) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors19.toFinset := by
    rw [priorityNeighbors19_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 19) a).2 ha
  have hbSet : b ∈ priorityNeighbors19.toFinset := by
    rw [priorityNeighbors19_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 19) b).2 hb
  have haList : a ∈ priorityNeighbors19 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors19 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors19.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers19_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid19 : ConstitutionallyRigid Physical center19 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 19) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 19) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors19 a b ha hb hz

/-- Atomic number is injective across every actual neighbor of center 22. -/
theorem atomZ_injective_neighbors22 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 22) a →
      Input.moleculeGraph.Adj (fixtureAtom 22) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors22.toFinset := by
    rw [priorityNeighbors22_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 22) a).2 ha
  have hbSet : b ∈ priorityNeighbors22.toFinset := by
    rw [priorityNeighbors22_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 22) b).2 hb
  have haList : a ∈ priorityNeighbors22 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors22 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors22.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers22_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid22 : ConstitutionallyRigid Physical center22 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 22) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 22) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors22 a b ha hb hz

/-- Atomic number is injective across every actual neighbor of center 26. -/
theorem atomZ_injective_neighbors26 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 26) a →
      Input.moleculeGraph.Adj (fixtureAtom 26) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors26.toFinset := by
    rw [priorityNeighbors26_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 26) a).2 ha
  have hbSet : b ∈ priorityNeighbors26.toFinset := by
    rw [priorityNeighbors26_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 26) b).2 hb
  have haList : a ∈ priorityNeighbors26 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors26 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors26.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers26_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid26 : ConstitutionallyRigid Physical center26 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 26) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 26) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors26 a b ha hb hz

/-- Atomic number is injective across every actual neighbor of center 29. -/
theorem atomZ_injective_neighbors29 :
    ∀ a b : Atom, Input.moleculeGraph.Adj (fixtureAtom 29) a →
      Input.moleculeGraph.Adj (fixtureAtom 29) b →
      Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b → a = b := by
  intro a b ha hb hz
  have haSet : a ∈ priorityNeighbors29.toFinset := by
    rw [priorityNeighbors29_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 29) a).2 ha
  have hbSet : b ∈ priorityNeighbors29.toFinset := by
    rw [priorityNeighbors29_neighbors]
    exact (MoleculeGraph.mem_neighborFinset Input.moleculeGraph
      (fixtureAtom 29) b).2 hb
  have haList : a ∈ priorityNeighbors29 := by simpa using haSet
  have hbList : b ∈ priorityNeighbors29 := by simpa using hbSet
  have graphNumbersNodup :
      (priorityNeighbors29.map Input.moleculeGraph.atomZ).Nodup := by
    rw [graphAtomZ_map_eq_atomicNumbers]
    exact ligandAtomicNumbers29_nodup
  exact List.inj_on_of_nodup_map graphNumbersNodup haList hbList hz

theorem rigid29 : ConstitutionallyRigid Physical center29 := by
  apply TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
  intro a b ha hb hz
  change Input.moleculeGraph.Adj (fixtureAtom 29) a at ha
  change Input.moleculeGraph.Adj (fixtureAtom 29) b at hb
  change Input.moleculeGraph.atomZ a = Input.moleculeGraph.atomZ b at hz
  exact atomZ_injective_neighbors29 a b ha hb hz

/-- Every detected nonroot tetrahedral center is constitutionally rigid. This case split uses
the accepted exact detector inventory; the root is deliberately excluded. -/
theorem all_nonroot_centers_constitutionallyRigid
    (center : Physical.Center)
    (notRoot : center.1 ≠ fixtureAtom 0) :
    ConstitutionallyRigid Physical center := by
  have detected : center.1 ∈ Input.tetrahedralCenterSet := by
    change center.1 ∈ Physical.centers
    exact center.2
  rw [detectedCenterSet] at detected
  simp only [Finset.mem_insert, Finset.mem_singleton] at detected
  rcases detected with h0 | h4 | h7 | h11 | h14 | h19 | h22 | h26 | h29
  · exact False.elim (notRoot h0)
  · have hcenter : center = center4 := Subtype.ext h4
    rw [hcenter]
    exact rigid4
  · have hcenter : center = center7 := Subtype.ext h7
    rw [hcenter]
    exact rigid7
  · have hcenter : center = center11 := Subtype.ext h11
    rw [hcenter]
    exact rigid11
  · have hcenter : center = center14 := Subtype.ext h14
    rw [hcenter]
    exact rigid14
  · have hcenter : center = center19 := Subtype.ext h19
    rw [hcenter]
    exact rigid19
  · have hcenter : center = center22 := Subtype.ext h22
    rw [hcenter]
    exact rigid22
  · have hcenter : center = center26 := Subtype.ext h26
    rw [hcenter]
    exact rigid26
  · have hcenter : center = center29 := Subtype.ext h29
    rw [hcenter]
    exact rigid29

end FixtureRigidity

assert_kernel_only FixtureRigidity.graphAtomZ_eq_source
assert_kernel_only FixtureRigidity.graphAtomZ_map_eq_atomicNumbers
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors4
assert_kernel_only FixtureRigidity.rigid4
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors7
assert_kernel_only FixtureRigidity.rigid7
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors11
assert_kernel_only FixtureRigidity.rigid11
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors14
assert_kernel_only FixtureRigidity.rigid14
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors19
assert_kernel_only FixtureRigidity.rigid19
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors22
assert_kernel_only FixtureRigidity.rigid22
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors26
assert_kernel_only FixtureRigidity.rigid26
assert_kernel_only FixtureRigidity.atomZ_injective_neighbors29
assert_kernel_only FixtureRigidity.rigid29
assert_kernel_only FixtureRigidity.all_nonroot_centers_constitutionallyRigid
