import TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
import TetraStereo.OneCenter.LocalizedPhysicalDomainReindexing
import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

/-!
# A finite threefold-symmetric reference fixture

The only detected degree-four atom is carbon `0`, with incoming fluorine `1` and three
boron neighbors `2,3,4`. The outer cycle is `2–5–8–3–6–9–4–7–10–2`, colored B–O–S.
Its color-preserving automorphisms are precisely the three rotations. In particular the
incoming ligand is fixed and every induced permutation of the central frame is even.

These are actual raw/certified input and coordinate facts, not fabricated comparison keys.
Structural admission and the encoded valence-table check are separate from a claim of
chemical realizability or normative profile coverage. No evaluator result is asserted here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture

open CertifiedLocalizedCIPInput CartesianPoint3
open LocalizedActualPhysicalBranchDecision
open LocalizedRecursiveAuxiliaryPhysicalDomain

private def atom (z : Nat) (positive : 0 < z) (bounded : z ≤ 118) : SemanticAtom :=
  { element := ⟨z, positive, bounded⟩ }

private def bond (a b : Nat) : RawBond := { source := a, target := b, kind := .single }
private def edge (a b : Nat) : SemanticInteraction :=
  { participants := [a, b], kind := .covalent 1 }

def mol : RawMolecule where
  atoms := [.aliphatic .C, .aliphatic .F, .aliphatic .B, .aliphatic .B, .aliphatic .B,
    .aliphatic .O, .aliphatic .O, .aliphatic .O, .aliphatic .S, .aliphatic .S, .aliphatic .S]
  bonds := [bond 0 1, bond 0 2, bond 0 3, bond 0 4,
    bond 2 5, bond 5 8, bond 8 3, bond 3 6, bond 6 9,
    bond 9 4, bond 4 7, bond 7 10, bond 10 2]
  neighborOrder := [[1, 2, 3, 4], [0], [0, 5, 10], [0, 6, 8], [0, 7, 9],
    [2, 8], [3, 9], [4, 10], [5, 3], [6, 4], [7, 2]]

def point (x y z : ℚ) : CartesianPoint3 := ⟨x, y, z⟩
def positions : List CartesianPoint3 :=
  [point (-1) (-1) (-1), point 0 0 0, point 1 0 0, point 0 1 0, point 0 0 1,
    point 2 0 0, point 0 2 0, point 0 0 2, point 2 1 0, point 0 2 1, point 1 0 2]

def source : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [atom 6 (by decide) (by decide), atom 9 (by decide) (by decide),
        atom 5 (by decide) (by decide), atom 5 (by decide) (by decide),
        atom 5 (by decide) (by decide), atom 8 (by decide) (by decide),
        atom 8 (by decide) (by decide), atom 8 (by decide) (by decide),
        atom 16 (by decide) (by decide), atom 16 (by decide) (by decide),
        atom 16 (by decide) (by decide)]
      interactions := [edge 0 1, edge 0 2, edge 0 3, edge 0 4,
        edge 2 5, edge 5 8, edge 8 3, edge 3 6, edge 6 9,
        edge 9 4, edge 4 7, edge 7 10, edge 10 2] }
  spatial? := some ⟨positions⟩
  diagram? := some mol.toDiagramConfiguration

theorem source_wellFormed : source.structurallyWellFormed? = true := by decide +kernel
theorem source_ready : source.molecule.localizedCIPGraphReady? = true := by decide +kernel

def certified : CertifiedLocalizedCIPInput where
  certified := ⟨source, source.structurallyWellFormed?_eq_true_iff.mp source_wellFormed⟩
  graphReady := source.molecule.localizedCIPGraphReady?_eq_true_iff.mp source_ready

theorem structure_agreement : mol.AuthoritativeStructureAgreement source := ⟨rfl, rfl⟩
theorem admissible : mol.StereochemicalAdmissible :=
  mol.stereochemicalAdmissible?_eq_true_iff.mp (by decide +kernel)
theorem valence_table : mol.ValenceOK := mol.valenceOK?_eq_true_iff.mp (by decide +kernel)

theorem supported : ∀ b ∈ mol.bonds, b.kind.IsLocalizedCovalent := by
  intro b member
  simp only [mol, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨1, rfl⟩

abbrev graph : MoleculeGraph (Fin 11) := certified.moleculeGraph
noncomputable abbrev physical := certified.detectedMultiCenterMolecule

theorem single_bonded : graph.SimpleBonded := by
  intro a b adjacent
  fin_cases a <;> fin_cases b <;> first
    | exact absurd adjacent (by decide)
    | decide

theorem constant_charge (a : Fin 11) : graph.formalCharge a = 0 := by fin_cases a <;> rfl
theorem degree_four_iff (a : Fin 11) : a ∈ graph.tetrahedralCenterSet ↔ a = 0 := by
  fin_cases a <;> decide +kernel
theorem detected_inventory : certified.tetrahedralCenterSet = ({0} : Finset (Fin 11)) := by
  ext a
  simpa only [Finset.mem_singleton] using degree_four_iff a

def center : physical.Center := ⟨(0 : Fin 11), (degree_four_iff 0).mpr rfl⟩
theorem center_unique (c : physical.Center) : c = center :=
  Subtype.ext ((degree_four_iff c.1).mp c.2)

def root : RawMolecule.CanonicalBranchNode := canonicalCenterRoot 0
def incoming : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 1, history := [0, 1], provenance := .realAtom }

theorem raw_frames :
    LocalizedGenericMarkedRecalculation.frameAtoms? mol root = some [1, 2, 3, 4] ∧
    LocalizedGenericMarkedRecalculation.frameAtoms? mol incoming = some [1, 2, 3, 4] := by
  decide +kernel

theorem incoming_child : incoming ∈ mol.canonicalChildren (canonicalCenterRoot 1) := by
  decide +kernel

theorem other_ligand_count (a : Fin 11) (ne : a ≠ 0) :
    (mol.ligandsWithLonePair a.val).length ≠ 4 := by
  fin_cases a <;> first | contradiction | decide +kernel

def rotationFun (a : Fin 11) : Fin 11 :=
  if a = 2 then 3 else if a = 3 then 4 else if a = 4 then 2 else
  if a = 5 then 6 else if a = 6 then 7 else if a = 7 then 5 else
  if a = 8 then 9 else if a = 9 then 10 else if a = 10 then 8 else a

def rotation : Equiv.Perm (Fin 11) where
  toFun := rotationFun
  invFun := rotationFun ∘ rotationFun
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem rotation_graph : graph.IsAutomorphism rotation := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases a <;> decide +kernel

def graphRotation : graph.Aut := ⟨rotation, rotation_graph⟩
def physicalRotation : physical.Aut := graph.detectedMultiCenterAutOfGraphAut graphRotation

theorem rotation_fixed : rotation 0 = 0 ∧ rotation 1 = 1 := ⟨rfl, rfl⟩
theorem rotation_cube : physicalRotation * (physicalRotation * physicalRotation) = 1 := by
  apply Subtype.ext
  ext a
  fin_cases a <;> rfl
theorem rotation_center : physical.centerPerm physicalRotation center = center :=
  center_unique _

theorem rotation_even : permHandedness (physical.ligandPermAt physicalRotation center) = 1 := by
  have cube := congrArg (fun e : physical.Aut => physical.ligandPermAt e center) rotation_cube
  dsimp only at cube
  rw [physical.ligandPermAt_mul, physical.ligandPermAt_mul,
    center_unique (physical.centerPerm (physicalRotation * physicalRotation) center),
    rotation_center, physical.ligandPermAt_one] at cube
  have signs := congrArg permHandedness cube
  simp only [permHandedness_mul, permHandedness_one] at signs
  rcases permHandedness_eq_one_or_eq_neg_one
      (physical.ligandPermAt physicalRotation center) with h | h
  · exact h
  · rw [h] at signs
    norm_num at signs

/-! The directed color cycle determines every graph automorphism from the image of atom 2. -/
private def next (a : Fin 11) : Fin 11 :=
  if a = 2 then 5 else if a = 5 then 8 else if a = 8 then 3 else
  if a = 3 then 6 else if a = 6 then 9 else if a = 9 then 4 else
  if a = 4 then 7 else if a = 7 then 10 else if a = 10 then 2 else a

private def nextZ (a : Fin 11) : Nat :=
  if graph.atomZ a = 5 then 8 else if graph.atomZ a = 8 then 16 else 5

private theorem next_iff (a b : Fin 11) (cycle : 2 ≤ a.val) :
    graph.Adj a b ∧ graph.atomZ b = nextZ a ↔ b = next a := by
  fin_cases a <;> norm_num at cycle
  all_goals fin_cases b <;> decide +kernel

private theorem cycle_iff (a : Fin 11) :
    2 ≤ a.val ↔ graph.atomZ a = 5 ∨ graph.atomZ a = 8 ∨ graph.atomZ a = 16 := by
  fin_cases a <;> decide +kernel

private theorem z_carbon (a : Fin 11) : graph.atomZ a = 6 ↔ a = 0 := by
  fin_cases a <;> decide +kernel

private theorem z_fluorine (a : Fin 11) : graph.atomZ a = 9 ↔ a = 1 := by
  fin_cases a <;> decide +kernel

private theorem z_boron (a : Fin 11) : graph.atomZ a = 5 ↔ a = 2 ∨ a = 3 ∨ a = 4 := by
  fin_cases a <;> decide +kernel

private theorem aut_next (e : graph.Aut) (a : Fin 11) (cycle : 2 ≤ a.val) :
    (e : Equiv.Perm (Fin 11)) (next a) = next ((e : Equiv.Perm (Fin 11)) a) := by
  have color := MoleculeGraph.Aut.atomZ_eq (m := graph) e
  have cycle' : 2 ≤ ((e : Equiv.Perm (Fin 11)) a).val := by
    rw [cycle_iff, color a]
    exact (cycle_iff a).mp cycle
  apply (next_iff _ _ cycle').mp
  obtain ⟨adjacent, z⟩ := (next_iff a (next a) cycle).mpr rfl
  refine ⟨(MoleculeGraph.Aut.adj_iff (m := graph) e a (next a)).mpr adjacent, ?_⟩
  rw [color (next a), z]
  simp only [nextZ, color a]

theorem graph_aut_classification (e : graph.Aut) :
    (e : Equiv.Perm (Fin 11)) = 1 ∨ (e : Equiv.Perm (Fin 11)) = rotation ∨
      (e : Equiv.Perm (Fin 11)) = rotation * rotation := by
  have color := MoleculeGraph.Aut.atomZ_eq (m := graph) e
  have zero : (e : Equiv.Perm (Fin 11)) 0 = 0 := by
    apply (z_carbon _).mp
    exact (color 0).trans rfl
  have one : (e : Equiv.Perm (Fin 11)) 1 = 1 := by
    apply (z_fluorine _).mp
    exact (color 1).trans rfl
  have two : (e : Equiv.Perm (Fin 11)) 2 = 2 ∨
      (e : Equiv.Perm (Fin 11)) 2 = 3 ∨ (e : Equiv.Perm (Fin 11)) 2 = 4 := by
    apply (z_boron _).mp
    exact (color 2).trans rfl
  have h2 := aut_next e 2 (by decide)
  have h5 := aut_next e 5 (by decide)
  have h8 := aut_next e 8 (by decide)
  have h3 := aut_next e 3 (by decide)
  have h6 := aut_next e 6 (by decide)
  have h9 := aut_next e 9 (by decide)
  have h4 := aut_next e 4 (by decide)
  have h7 := aut_next e 7 (by decide)
  rcases two with two | two | two
  · left
    ext a
    fin_cases a <;> simp_all [next]
  · right; left
    ext a
    fin_cases a <;> simp_all [next, rotation, rotationFun]
  · right; right
    ext a
    fin_cases a <;> simp_all [next, rotation, rotationFun]

theorem every_local_permutation_even (e : physical.Aut) :
    permHandedness (physical.ligandPermAt e center) = 1 := by
  let g : graph.Aut :=
    ⟨(e : Equiv.Perm certified.Atom), MultiCenterMolecule.Aut.mem_molAut (m := physical) e⟩
  rcases graph_aut_classification g with h | h | h
  · have same : e = 1 := Subtype.ext h
    rw [same, physical.ligandPermAt_one, permHandedness_one]
  · have same : e = physicalRotation := Subtype.ext h
    rw [same, rotation_even]
  · have same : e = physicalRotation * physicalRotation := Subtype.ext h
    rw [same, physical.ligandPermAt_mul, rotation_center, permHandedness_mul, rotation_even]
    norm_num

/-! The calibrated configuration is transported to the actual detected frame enumeration. -/
abbrev canonical := actualCanonicalMolecule certified
def canonicalCenter : canonical.Center := ⟨(0 : Fin 11), (degree_four_iff 0).mpr rfl⟩

private theorem sorted_neighbors : (graph.neighborFinset 0).sort (· ≤ ·) = [1, 2, 3, 4] := by
  have h : graph.neighborFinset 0 = ([1, 2, 3, 4] : List (Fin 11)).toFinset := by
    ext a
    fin_cases a <;> decide +kernel
  rw [h]
  exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by decide)

private theorem ligand_of_sorted (c : canonical.Center) (sorted : List certified.Atom)
    (ordered : (certified.moleculeGraph.neighborFinset c.1).sort (· ≤ ·) = sorted)
    (length : sorted.length = 4) (i : Fin 4) :
    canonical.ligandAtomAt c i = sorted.get (Fin.cast length.symm i) := by
  unfold canonical actualCanonicalMolecule MultiCenterMolecule.ligandAtomAt
    CertifiedLocalizedCIPInput.canonicalLigandAtom CertifiedLocalizedCIPInput.canonicalNeighborList
  simp [ordered]

theorem canonical_ligands (i : Fin 4) :
    canonical.ligandAtomAt canonicalCenter i = (![1, 2, 3, 4] : Fin 4 → Fin 11) i := by
  have h := ligand_of_sorted canonicalCenter ([1, 2, 3, 4] : List (Fin 11)) sorted_neighbors rfl i
  fin_cases i <;> simpa using h

private theorem canonical_calibrated (c : canonical.Center) :
    ActualPhysicalCalibratedCoordinates certified canonical (coordinateCfg certified) c := by
  have same : c = canonicalCenter := Subtype.ext ((degree_four_iff c.1).mp c.2)
  subst c
  apply coordinateCfg_calibrated certified canonicalCenter
    ![point 0 0 0, point 1 0 0, point 0 1 0, point 0 0 1]
  · intro i
    rw [canonical_ligands]
    fin_cases i <;> rfl
  · decide +kernel

noncomputable def frameChange : canonical.Center → Equiv.Perm (Fin 4) :=
  Classical.choose (exists_canonical_reindex certified)
theorem frameChange_spec : canonical.reindexFrames frameChange = physical :=
  Classical.choose_spec (exists_canonical_reindex certified)

noncomputable def cfg : physical.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration frameChange_spec)
    (canonical.reindexConfiguration frameChange (coordinateCfg certified))

private theorem calibration_reindexed (c : canonical.Center) :
    ActualPhysicalCalibratedCoordinates certified (canonical.reindexFrames frameChange)
      (canonical.reindexConfiguration frameChange (coordinateCfg certified)) c := by
  obtain ⟨points, observed, nonzero, sign⟩ := canonical_calibrated c
  refine ⟨fun i => points (frameChange c i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed _
  · exact cartesianOrientedVolume_perm_ne_zero points (frameChange c) nonzero
  · have vec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector (points 0) (points 1) (points 2) (points 3) k =
          points k := by intro k; fin_cases k <;> rfl
    have volume : RationalTetrahedralPermutation.permutedOrientedVolume
        (points 0) (points 1) (points 2) (points 3) (frameChange c) =
        orientedVolume (points (frameChange c 0)) (points (frameChange c 1))
          (points (frameChange c 2)) (points (frameChange c 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, vec]
    rw [← volume, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

theorem calibrated (c : physical.Center) :
    ActualPhysicalCalibratedCoordinates certified physical cfg c := by
  let c' : (canonical.reindexFrames frameChange).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center frameChange_spec.symm) c
  have transported := calibration_reindexed c'
  have transfer {m n : MultiCenterMolecule certified.Atom} (h : m = n)
      (configuration : m.Configuration) (d : m.Center)
      (proof : ActualPhysicalCalibratedCoordinates certified m configuration d) :
      ActualPhysicalCalibratedCoordinates certified n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) d) := by
    cases h
    exact proof
  simpa [cfg, c'] using transfer frameChange_spec
    (canonical.reindexConfiguration frameChange (coordinateCfg certified)) c' transported

end TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.source_wellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.source_ready
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.structure_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.admissible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.valence_table
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.supported
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.single_bonded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.constant_charge
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.detected_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.raw_frames
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.incoming_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.other_ligand_count
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.rotation_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.rotation_even
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.graph_aut_classification
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.every_local_permutation_even
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceFixture.calibrated
