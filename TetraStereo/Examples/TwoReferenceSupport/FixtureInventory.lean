import TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FixtureInventory

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture

abbrev Input := localizedSource
abbrev Atom := CertifiedLocalizedCIPInput.Atom Input
abbrev Center := CertifiedLocalizedCIPInput.TetrahedralCenter Input

def fixtureAtom (n : Fin 33) : Atom :=
  ⟨n.val, by change n.val < 33; exact n.isLt⟩

def atomList (ns : List (Fin 33)) : List Atom := ns.map fixtureAtom

theorem atomCount : source.molecule.atomCount = 33 := by decide +kernel

/-- Exact finite detector output as a set of source atom indices. -/
theorem detectedCenterSet :
    Input.tetrahedralCenterSet =
      ({fixtureAtom 0, fixtureAtom 4, fixtureAtom 7, fixtureAtom 11,
        fixtureAtom 14, fixtureAtom 19, fixtureAtom 22, fixtureAtom 26,
        fixtureAtom 29} : Finset Atom) := by
  ext c
  fin_cases c <;> decide +kernel

def center4 : Center := ⟨fixtureAtom (4 : Fin 33), by decide +kernel⟩
def center7 : Center := ⟨fixtureAtom (7 : Fin 33), by decide +kernel⟩
def center11 : Center := ⟨fixtureAtom (11 : Fin 33), by decide +kernel⟩
def center14 : Center := ⟨fixtureAtom (14 : Fin 33), by decide +kernel⟩
def center19 : Center := ⟨fixtureAtom (19 : Fin 33), by decide +kernel⟩
def center22 : Center := ⟨fixtureAtom (22 : Fin 33), by decide +kernel⟩
def center26 : Center := ⟨fixtureAtom (26 : Fin 33), by decide +kernel⟩
def center29 : Center := ⟨fixtureAtom (29 : Fin 33), by decide +kernel⟩

/-- Raw detector adjacency, proved against the actual localized source graph. -/
theorem graphNeighbors4 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 4) =
      ({fixtureAtom 3, fixtureAtom 5, fixtureAtom 6, fixtureAtom 7} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

theorem graphNeighbors7 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 7) =
      ({fixtureAtom 4, fixtureAtom 8, fixtureAtom 9, fixtureAtom 10} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

theorem graphNeighbors11 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 11) =
      ({fixtureAtom 3, fixtureAtom 12, fixtureAtom 13, fixtureAtom 14} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

theorem graphNeighbors14 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 14) =
      ({fixtureAtom 11, fixtureAtom 15, fixtureAtom 16, fixtureAtom 17} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

theorem graphNeighbors19 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 19) =
      ({fixtureAtom 18, fixtureAtom 20, fixtureAtom 21, fixtureAtom 22} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

theorem graphNeighbors22 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 22) =
      ({fixtureAtom 19, fixtureAtom 23, fixtureAtom 24, fixtureAtom 25} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

theorem graphNeighbors26 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 26) =
      ({fixtureAtom 18, fixtureAtom 27, fixtureAtom 28, fixtureAtom 29} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

theorem graphNeighbors29 :
    Input.moleculeGraph.neighborFinset (fixtureAtom 29) =
      ({fixtureAtom 26, fixtureAtom 30, fixtureAtom 31, fixtureAtom 32} : Finset Atom) := by
  ext u
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases u <;> decide +kernel

/-- Descending atomic-number priority, verified as an ordering of the actual detector neighbors. -/
def priorityNeighbors4 : List Atom := atomList ([6, 3, 7, 5] : List (Fin 33))
def priorityNeighbors7 : List Atom := atomList ([10, 9, 4, 8] : List (Fin 33))
def priorityNeighbors11 : List Atom := atomList ([13, 3, 14, 12] : List (Fin 33))
def priorityNeighbors14 : List Atom := atomList ([17, 16, 11, 15] : List (Fin 33))
def priorityNeighbors19 : List Atom := atomList ([21, 18, 22, 20] : List (Fin 33))
def priorityNeighbors22 : List Atom := atomList ([25, 24, 19, 23] : List (Fin 33))
def priorityNeighbors26 : List Atom := atomList ([28, 18, 29, 27] : List (Fin 33))
def priorityNeighbors29 : List Atom := atomList ([32, 31, 26, 30] : List (Fin 33))

/-- Priority lists enumerate the actual graph neighbor sets. The exact source atomic-number
readbacks below establish the descending priority order. -/
theorem priorityNeighbors4_neighbors :
    priorityNeighbors4.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 4) := by
  rw [graphNeighbors4]
  decide +kernel

theorem priorityNeighbors7_neighbors :
    priorityNeighbors7.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 7) := by
  rw [graphNeighbors7]
  decide +kernel

theorem priorityNeighbors11_neighbors :
    priorityNeighbors11.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 11) := by
  rw [graphNeighbors11]
  decide +kernel

theorem priorityNeighbors14_neighbors :
    priorityNeighbors14.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 14) := by
  rw [graphNeighbors14]
  decide +kernel

theorem priorityNeighbors19_neighbors :
    priorityNeighbors19.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 19) := by
  rw [graphNeighbors19]
  decide +kernel

theorem priorityNeighbors22_neighbors :
    priorityNeighbors22.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 22) := by
  rw [graphNeighbors22]
  decide +kernel

theorem priorityNeighbors26_neighbors :
    priorityNeighbors26.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 26) := by
  rw [graphNeighbors26]
  decide +kernel

theorem priorityNeighbors29_neighbors :
    priorityNeighbors29.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 29) := by
  rw [graphNeighbors29]
  decide +kernel

def atomicNumbers (xs : List Atom) : List Nat :=
  xs.map fun a => (source.molecule.atoms.get a).element.atomicNumber

theorem ligandAtomicNumbers4 :
    atomicNumbers priorityNeighbors4 = [9, 7, 6, 1] := by decide +kernel
theorem ligandAtomicNumbers7 :
    atomicNumbers priorityNeighbors7 = [35, 17, 6, 1] := by decide +kernel
theorem ligandAtomicNumbers11 :
    atomicNumbers priorityNeighbors11 = [9, 7, 6, 1] := by decide +kernel
theorem ligandAtomicNumbers14 :
    atomicNumbers priorityNeighbors14 = [35, 17, 6, 1] := by decide +kernel
theorem ligandAtomicNumbers19 :
    atomicNumbers priorityNeighbors19 = [9, 7, 6, 1] := by decide +kernel
theorem ligandAtomicNumbers22 :
    atomicNumbers priorityNeighbors22 = [35, 17, 6, 1] := by decide +kernel
theorem ligandAtomicNumbers26 :
    atomicNumbers priorityNeighbors26 = [9, 7, 6, 1] := by decide +kernel
theorem ligandAtomicNumbers29 :
    atomicNumbers priorityNeighbors29 = [35, 17, 6, 1] := by decide +kernel

theorem ligandAtomicNumbers4_nodup : (atomicNumbers priorityNeighbors4).Nodup := by
  rw [ligandAtomicNumbers4]
  decide +kernel
theorem ligandAtomicNumbers7_nodup : (atomicNumbers priorityNeighbors7).Nodup := by
  rw [ligandAtomicNumbers7]
  decide +kernel
theorem ligandAtomicNumbers11_nodup : (atomicNumbers priorityNeighbors11).Nodup := by
  rw [ligandAtomicNumbers11]
  decide +kernel
theorem ligandAtomicNumbers14_nodup : (atomicNumbers priorityNeighbors14).Nodup := by
  rw [ligandAtomicNumbers14]
  decide +kernel
theorem ligandAtomicNumbers19_nodup : (atomicNumbers priorityNeighbors19).Nodup := by
  rw [ligandAtomicNumbers19]
  decide +kernel
theorem ligandAtomicNumbers22_nodup : (atomicNumbers priorityNeighbors22).Nodup := by
  rw [ligandAtomicNumbers22]
  decide +kernel
theorem ligandAtomicNumbers26_nodup : (atomicNumbers priorityNeighbors26).Nodup := by
  rw [ligandAtomicNumbers26]
  decide +kernel
theorem ligandAtomicNumbers29_nodup : (atomicNumbers priorityNeighbors29).Nodup := by
  rw [ligandAtomicNumbers29]
  decide +kernel

end FixtureInventory

assert_kernel_only FixtureInventory.detectedCenterSet
assert_kernel_only FixtureInventory.atomCount
assert_kernel_only FixtureInventory.graphNeighbors4
assert_kernel_only FixtureInventory.graphNeighbors7
assert_kernel_only FixtureInventory.graphNeighbors11
assert_kernel_only FixtureInventory.graphNeighbors14
assert_kernel_only FixtureInventory.graphNeighbors19
assert_kernel_only FixtureInventory.graphNeighbors22
assert_kernel_only FixtureInventory.graphNeighbors26
assert_kernel_only FixtureInventory.graphNeighbors29
assert_kernel_only FixtureInventory.ligandAtomicNumbers4
assert_kernel_only FixtureInventory.ligandAtomicNumbers7
assert_kernel_only FixtureInventory.ligandAtomicNumbers11
assert_kernel_only FixtureInventory.ligandAtomicNumbers14
assert_kernel_only FixtureInventory.ligandAtomicNumbers19
assert_kernel_only FixtureInventory.ligandAtomicNumbers22
assert_kernel_only FixtureInventory.ligandAtomicNumbers26
assert_kernel_only FixtureInventory.ligandAtomicNumbers29
assert_kernel_only FixtureInventory.priorityNeighbors4_neighbors
assert_kernel_only FixtureInventory.priorityNeighbors7_neighbors
assert_kernel_only FixtureInventory.priorityNeighbors11_neighbors
assert_kernel_only FixtureInventory.priorityNeighbors14_neighbors
assert_kernel_only FixtureInventory.priorityNeighbors19_neighbors
assert_kernel_only FixtureInventory.priorityNeighbors22_neighbors
assert_kernel_only FixtureInventory.priorityNeighbors26_neighbors
assert_kernel_only FixtureInventory.priorityNeighbors29_neighbors
assert_kernel_only FixtureInventory.ligandAtomicNumbers4_nodup
assert_kernel_only FixtureInventory.ligandAtomicNumbers7_nodup
assert_kernel_only FixtureInventory.ligandAtomicNumbers11_nodup
assert_kernel_only FixtureInventory.ligandAtomicNumbers14_nodup
assert_kernel_only FixtureInventory.ligandAtomicNumbers19_nodup
assert_kernel_only FixtureInventory.ligandAtomicNumbers22_nodup
assert_kernel_only FixtureInventory.ligandAtomicNumbers26_nodup
assert_kernel_only FixtureInventory.ligandAtomicNumbers29_nodup
