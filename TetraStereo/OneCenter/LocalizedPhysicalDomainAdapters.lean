import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.OneCenter.LocalizedPhysicalRootDescriptorExecution
import TetraStereo.OneCenter.LocalizedRootZAutomorphismLabelCovariance
import TetraStereo.OneCenter.Geometry
import Mathlib.Tactic.FinCases
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false






























































namespace TetraStereo
namespace OneCenter

open TetraStereo.OneCenter

/-! ## Constitutional rigidity from injective ligand atomic numbers -/

/-- **Neighbour-level injectivity implies constitutional rigidity.**  If the atomic number is
injective on the four neighbours of a distinguished center, then every center-fixing automorphism
fixes all four ligand slots.  The induced ligand permutation sends slot `i` to the unique slot whose
atom is the image of the `i`-th ligand; automorphism invariance of atomic number plus injectivity
forces that slot to be `i` itself. -/
theorem constitutionallyRigid_of_atomZ_injective_on_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : MultiCenterMolecule V} {d : m.Center}
    (hZ : ∀ a b : V, m.mol.Adj d.1 a → m.mol.Adj d.1 b →
      m.mol.atomZ a = m.mol.atomZ b → a = b) :
    ConstitutionallyRigid m d := by
  intro e hcenter
  apply Equiv.ext
  intro i
  have hlig : m.ligandAtomAt d (m.ligandPermAt e d i) =
      (e : Equiv.Perm V) (m.ligandAtomAt d i) := by
    have h := m.ligandAtomAt_ligandPermAt e d i
    rwa [hcenter] at h
  have hZeq : m.mol.atomZ (m.ligandAtomAt d (m.ligandPermAt e d i)) =
      m.mol.atomZ (m.ligandAtomAt d i) := by
    rw [hlig]
    exact MoleculeGraph.Aut.atomZ_eq m.mol
      ⟨(e : Equiv.Perm V), MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩
      (m.ligandAtomAt d i)
  have hidx : (m.ligandPermAt e d) i = i :=
    m.ligandAtomAt_injective d
      (hZ _ _ (m.ligandAtomAt_adj d _) (m.ligandAtomAt_adj d i) hZeq)
  simpa [Equiv.Perm.one_apply] using hidx

/-- Injectivity of atomic numbers along a ligand enumeration is exactly neighbour-level
injectivity: the enumeration is surjective onto the neighbours of the center. -/
theorem atomZ_injective_on_neighbors_of_ligandAtomZ_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : MultiCenterMolecule V} {d : m.Center}
    (hZ : Function.Injective fun i : Fin 4 => m.mol.atomZ (m.ligandAtomAt d i)) :
    ∀ a b : V, m.mol.Adj d.1 a → m.mol.Adj d.1 b →
      m.mol.atomZ a = m.mol.atomZ b → a = b := by
  intro a b ha hb hz
  obtain ⟨i, rfl⟩ := m.ligandAtomAt_surjective d a ha
  obtain ⟨j, rfl⟩ := m.ligandAtomAt_surjective d b hb
  have hij : i = j := hZ hz
  rw [hij]

/-- **Injective ligand atomic numbers imply constitutional rigidity.**  This is the enumeration
form used by the calibrated root-`Z` branch. -/
theorem constitutionallyRigid_of_ligandAtomZ_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : MultiCenterMolecule V} {d : m.Center}
    (hZ : Function.Injective fun i : Fin 4 => m.mol.atomZ (m.ligandAtomAt d i)) :
    ConstitutionallyRigid m d :=
  constitutionallyRigid_of_atomZ_injective_on_neighbors
    (atomZ_injective_on_neighbors_of_ligandAtomZ_injective hZ)

/-! ## Oriented-volume nondegeneracy under reindexing -/

/-- The real geometry attached to four exact rational points, expressed with a plain function
rather than the pattern-matching constructor, is the same tetrahedron. -/
theorem toRealTetrahedralGeometry_fun_eq (pointAt : Fin 4 → CartesianPoint3) :
    ({ vertex := fun i => (pointAt i).toRealPoint } : TetrahedralGeometry) =
      CartesianPoint3.toRealTetrahedralGeometry
        (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) := by
  apply TetrahedralGeometry.ext
  intro i
  fin_cases i <;> rfl

/-- The real oriented volume of the plain-function tetrahedron is the cast of the exact rational
oriented volume of the four points. -/
theorem orientedVolume_fun_eq_realOrientedVolume (pointAt : Fin 4 → CartesianPoint3) :
    TetrahedralGeometry.orientedVolume
        ({ vertex := fun i => (pointAt i).toRealPoint } : TetrahedralGeometry) =
      ((CartesianPoint3.orientedVolume
        (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) : ℚ) : ℝ) := by
  rw [toRealTetrahedralGeometry_fun_eq pointAt,
    CartesianPoint3.orientedVolume_toRealTetrahedralGeometry]

/-- **Nonzero oriented volume survives a permutation of the four points.**  Reindexing the four
points by `alpha` multiplies the oriented volume by `permHandedness alpha`, which is `±1`, so a
nonzero exact rational volume stays nonzero. -/
theorem cartesianOrientedVolume_perm_ne_zero
    (pointAt : Fin 4 → CartesianPoint3) (alpha : Equiv.Perm (Fin 4))
    (nonzero : CartesianPoint3.orientedVolume
      (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0) :
    CartesianPoint3.orientedVolume
      (pointAt (alpha 0)) (pointAt (alpha 1))
        (pointAt (alpha 2)) (pointAt (alpha 3)) ≠ 0 := by
  intro hzero
  have hPerm := TetrahedralGeometry.orientedVolume_reindex
    ({ vertex := fun i => (pointAt i).toRealPoint } : TetrahedralGeometry) alpha
  have hLeft : TetrahedralGeometry.orientedVolume
        (TetrahedralGeometry.reindex
          ({ vertex := fun i => (pointAt i).toRealPoint } : TetrahedralGeometry) alpha) =
      ((CartesianPoint3.orientedVolume
        (pointAt (alpha 0)) (pointAt (alpha 1))
          (pointAt (alpha 2)) (pointAt (alpha 3)) : ℚ) : ℝ) := by
    change TetrahedralGeometry.orientedVolume
        ({ vertex := fun i => (pointAt (alpha i)).toRealPoint } : TetrahedralGeometry) =
      ((CartesianPoint3.orientedVolume
        (pointAt (alpha 0)) (pointAt (alpha 1))
          (pointAt (alpha 2)) (pointAt (alpha 3)) : ℚ) : ℝ)
    exact orientedVolume_fun_eq_realOrientedVolume (fun i => pointAt (alpha i))
  have hRight : TetrahedralGeometry.orientedVolume
        ({ vertex := fun i => (pointAt i).toRealPoint } : TetrahedralGeometry) =
      ((CartesianPoint3.orientedVolume
        (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) : ℚ) : ℝ) :=
    orientedVolume_fun_eq_realOrientedVolume pointAt
  have hZero : permHandedness alpha * TetrahedralGeometry.orientedVolume
        ({ vertex := fun i => (pointAt i).toRealPoint } : TetrahedralGeometry) = 0 := by
    rw [← hPerm, hLeft, hzero]
    norm_num
  have hAlpha : permHandedness alpha ≠ 0 := by
    rcases permHandedness_eq_one_or_eq_neg_one alpha with h | h <;> rw [h] <;> norm_num
  have hBase : TetrahedralGeometry.orientedVolume
      ({ vertex := fun i => (pointAt i).toRealPoint } : TetrahedralGeometry) = 0 := by
    rcases mul_eq_zero.mp hZero with h | h
    · exact absurd h hAlpha
    · exact h
  have hRat : CartesianPoint3.orientedVolume
      (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) = 0 := by
    rw [hRight] at hBase
    exact (Rat.cast_eq_zero (α := ℝ)).mp hBase
  exact nonzero hRat

namespace CertifiedLocalizedCIPInput

/-! ## Transport of physical terminal twins across equal graphs -/

/-- Physical terminal twins are graph-level data: they mention the multi-center molecule only
through its underlying graph and the center atom.  Hence a twin transports between any two
multi-center molecules with the same graph and the same center atom.  This bridges the canonical
detected molecule (whose ligand enumeration is the executable canonical one) and the automatically
detected molecule (whose enumeration is an arbitrary cardinality equivalence) without changing the
twin content. -/
theorem actualPhysicalTerminalTwinCenter_congr_mol
    {input : CertifiedLocalizedCIPInput}
    {m₁ m₂ : MultiCenterMolecule input.Atom}
    {c₁ : m₁.Center} {c₂ : m₂.Center}
    (hmol : m₁.mol = m₂.mol) (hcenter : c₁.1 = c₂.1)
    (twin : ActualPhysicalTerminalTwinCenter input m₁ c₁) :
    ActualPhysicalTerminalTwinCenter input m₂ c₂ := by
  obtain ⟨a, b, pair⟩ := twin
  refine ⟨a, b, ?_⟩
  refine
    { ne := pair.ne
      neighbor_a := ?_
      neighbor_b := ?_
      z_eq := ?_
      mass_eq := ?_
      charge_eq := ?_
      bond_eq := ?_ }
  · rw [← hmol, ← hcenter]
    exact pair.neighbor_a
  · rw [← hmol, ← hcenter]
    exact pair.neighbor_b
  · rw [← hmol]
    exact pair.z_eq
  · rw [← hmol]
    exact pair.mass_eq
  · rw [← hmol]
    exact pair.charge_eq
  · rw [← hmol, ← hcenter]
    exact pair.bond_eq

/-! ## The canonical detected multi-center molecule -/

/-- The automatically detected multi-center molecule with the **canonical** ligand enumeration:
the molecule is the certified input graph, the distinguished centers are exactly the detected
degree-four candidates, and each center's four ligands are enumerated by the executable ascending
neighbour list `canonicalLigandAtom`.  Both structural fields are definitional; the ligand
alignment is definitional too. -/
noncomputable def canonicalDetectedMultiCenterMolecule
    (input : CertifiedLocalizedCIPInput) :
    MultiCenterMolecule input.Atom where
  mol := input.moleculeGraph
  centers := input.tetrahedralCenterSet
  ligandAtom := fun c hc i => input.canonicalLigandAtom ⟨c, hc⟩ i
  ligandAtom_adj := by
    intro c hc i
    exact input.canonicalLigandAtom_adj ⟨c, hc⟩ i
  ligandAtom_injective := by
    intro c hc i j hij
    exact input.canonicalLigandAtom_injective ⟨c, hc⟩ hij
  ligandAtom_surjective := by
    intro c hc v hv
    obtain ⟨index, hindex⟩ :=
      (input.canonicalLigandNeighbor_bijective ⟨c, hc⟩).2 ⟨v, hv⟩
    exact ⟨index, congrArg Subtype.val hindex⟩

/-- The canonical detected molecule's graph is the certified input graph (definitionally). -/
theorem canonicalDetectedMultiCenterMolecule_mol (input : CertifiedLocalizedCIPInput) :
    input.canonicalDetectedMultiCenterMolecule.mol = input.moleculeGraph := rfl

/-- The canonical detected molecule's center inventory is the detected candidate set
(definitionally). -/
theorem canonicalDetectedMultiCenterMolecule_centers (input : CertifiedLocalizedCIPInput) :
    input.canonicalDetectedMultiCenterMolecule.centers = input.tetrahedralCenterSet := rfl

/-- **Definitional canonical ligand alignment.**  The canonical detected molecule's ligand
enumeration at a center is exactly `input.canonicalLigandAtom`. -/
@[simp] theorem canonicalDetectedMultiCenterMolecule_ligandAtomAt
    (input : CertifiedLocalizedCIPInput)
    (center : input.canonicalDetectedMultiCenterMolecule.Center) (i : Fin 4) :
    input.canonicalDetectedMultiCenterMolecule.ligandAtomAt center i =
      input.canonicalLigandAtom center i := rfl




theorem constitutionallyRigid_of_canonicalLigandAtomZ_injective
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter)
    (hZ : Function.Injective fun i : Fin 4 =>
      input.moleculeGraph.atomZ (input.canonicalLigandAtom center i)) :
    ConstitutionallyRigid input.detectedMultiCenterMolecule center := by
  have hneighbor : ∀ a b : input.Atom,
      input.detectedMultiCenterMolecule.mol.Adj center.1 a →
      input.detectedMultiCenterMolecule.mol.Adj center.1 b →
      input.detectedMultiCenterMolecule.mol.atomZ a =
        input.detectedMultiCenterMolecule.mol.atomZ b → a = b := by
    intro a b ha hb hz
    obtain ⟨i, hi⟩ :=
      (input.canonicalLigandNeighbor_bijective center).2 ⟨a, ha⟩
    obtain ⟨j, hj⟩ :=
      (input.canonicalLigandNeighbor_bijective center).2 ⟨b, hb⟩
    have hia : input.canonicalLigandAtom center i = a := congrArg Subtype.val hi
    have hjb : input.canonicalLigandAtom center j = b := congrArg Subtype.val hj
    have hzi : input.moleculeGraph.atomZ (input.canonicalLigandAtom center i) =
        input.moleculeGraph.atomZ (input.canonicalLigandAtom center j) := by
      rw [hia, hjb]
      exact hz
    have hij : i = j := hZ hzi
    rw [← hia, ← hjb, hij]
  exact constitutionallyRigid_of_atomZ_injective_on_neighbors hneighbor



/-- **A calibrated center of the canonical detected domain is a general rigid calibrated
center.**  Injectivity of ligand atomic numbers gives `ConstitutionallyRigid` at the same detected
atom; the coordinates, nonzero volume and configuration-sign identity are the calibrated ones,
already stated in the canonical ligand enumeration definitionally.  No frame, slot permutation,
label, key or automorphism sign law is introduced, and no new semantic premise is used. -/
theorem actualGeneralRigidCalibratedCenter_of_canonicalPhysicalCalibratedCenter
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.canonicalDetectedMultiCenterMolecule.Configuration)
    (center : input.canonicalDetectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalCalibratedCenter input
      input.canonicalDetectedMultiCenterMolecule cfg center) :
    ActualGeneralRigidCalibratedCenter input cfg center := by
  obtain ⟨pointAt, zInjective, observed, nonzero, signEq⟩ := calibrated
  have hZcanonical : Function.Injective (fun i : Fin 4 =>
      input.moleculeGraph.atomZ (input.canonicalLigandAtom center i)) := zInjective
  refine ⟨?_, pointAt, ?_, nonzero, ?_⟩
  · exact constitutionallyRigid_of_canonicalLigandAtomZ_injective input center hZcanonical
  · intro i
    simpa using observed i
  · simpa [MultiCenterMolecule.configurationSign] using signEq





theorem actualGeneralRigidGlobalPhysicalDomain_of_canonicalPhysicalCalibratedDomain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.canonicalDetectedMultiCenterMolecule.Configuration)
    (root : input.canonicalDetectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input
      input.canonicalDetectedMultiCenterMolecule cfg root) :
    ActualGeneralRigidGlobalPhysicalDomain input cfg root := by
  refine actualGeneralRigidGlobalPhysicalDomain_of_centerCase input cfg root ?_
  intro center center_ne_root
  rcases domain.centerCase center center_ne_root with twin | calibrated
  · exact Or.inl (actualPhysicalTerminalTwinCenter_congr_mol
      (m₁ := input.canonicalDetectedMultiCenterMolecule)
      (m₂ := input.detectedMultiCenterMolecule)
      (c₁ := center) (c₂ := ⟨center.1, center.2⟩)
      (by rw [canonicalDetectedMultiCenterMolecule_mol, detectedMultiCenter_mol])
      rfl twin)
  · exact Or.inr
      (actualGeneralRigidCalibratedCenter_of_canonicalPhysicalCalibratedCenter
        input cfg center calibrated)
















/-- The per-center permutation taking the detected molecule's own ligand indices to the executable
canonical (ascending-neighbour) ligand indices.  Writing `Em` for the physical ligand equivalence
and `Ecan` for the canonical one, it is `Em.trans Ecan.symm`. -/
noncomputable def canonicalLigandReindex
    (input : CertifiedLocalizedCIPInput)
    (center : input.detectedMultiCenterMolecule.Center) : Equiv.Perm (Fin 4) :=
  (input.physicalLigandEquiv input.detectedMultiCenterMolecule
      (detectedMultiCenter_mol input) center).trans
    (Equiv.ofBijective (input.canonicalLigandNeighbor center)
      (input.canonicalLigandNeighbor_bijective center)).symm

/-- **The reindexing equation.**  The detected molecule's ligand atom in its own enumeration is the
canonical ligand atom at the reindexed slot. -/
theorem canonicalLigandReindex_spec
    (input : CertifiedLocalizedCIPInput)
    (center : input.detectedMultiCenterMolecule.Center) (i : Fin 4) :
    input.detectedMultiCenterMolecule.ligandAtomAt center i =
      input.canonicalLigandAtom center (input.canonicalLigandReindex center i) := by
  let Em : Fin 4 ≃ input.moleculeGraph.Neighbor center.1 :=
    input.physicalLigandEquiv input.detectedMultiCenterMolecule
      (detectedMultiCenter_mol input) center
  let Ecan : Fin 4 ≃ input.moleculeGraph.Neighbor center.1 :=
    Equiv.ofBijective (input.canonicalLigandNeighbor center)
      (input.canonicalLigandNeighbor_bijective center)
  have h : Ecan (input.canonicalLigandReindex center i) = Em i := by
    simp [canonicalLigandReindex, Em, Ecan, Equiv.trans_apply]
  have hval := congrArg Subtype.val h
  simpa [Em, Ecan, input.physicalLigandEquiv_apply_coe] using hval.symm





noncomputable def canonicalReindexConfiguration
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration) :
    input.detectedMultiCenterMolecule.Configuration :=
  fun center => cfg center * input.canonicalLigandReindex center

/-- A physical center that is both constitutionally rigid and calibrated in the molecule's own
ligand enumeration: available source coordinates on `m.ligandAtomAt`, nonzero exact oriented
volume, and physical volume sign equal to the physical configuration sign at the center. -/
def ActualPhysicalGeneralRigidCalibratedCenter
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (center : m.Center) : Prop :=
  ConstitutionallyRigid m center ∧
    ∃ pointAt : Fin 4 → CartesianPoint3,
      (∀ i, input.spatialPointAt? (m.ligandAtomAt center i) = some (pointAt i)) ∧
        CartesianPoint3.orientedVolume
            (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0 ∧
          rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
            m.configurationSign cfg center

/-- **The general rigid physical domain in the original detected enumeration.**  One actual
multi-center molecule on the certified atoms, one physical configuration, one physical root.  Every
non-root center is a physical terminal twin or a constitutionally rigid center calibrated in the
molecule's own ligand enumeration.  No canonical enumeration is mentioned. -/
structure ActualGeneralRigidPhysicalDomain
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (root : m.Center) : Prop where
  /-- The physical molecule has exactly the certified input graph. -/
  graphEq : m.mol = input.moleculeGraph
  /-- Every non-root center is a physical terminal twin or a physical general rigid calibrated
  center. -/
  centerCase : ∀ center : m.Center, center ≠ root →
    ActualPhysicalTerminalTwinCenter input m center ∨
      ActualPhysicalGeneralRigidCalibratedCenter input m cfg center





theorem actualGeneralRigidPhysicalDomain_of_physicalCalibratedDomain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input
      input.detectedMultiCenterMolecule cfg root) :
    ActualGeneralRigidPhysicalDomain input input.detectedMultiCenterMolecule cfg root := by
  refine ⟨domain.graphEq, ?_⟩
  intro center center_ne_root
  rcases domain.centerCase center center_ne_root with twin | calibrated
  · exact Or.inl twin
  · obtain ⟨pointAt, zInjective, observed, nonzero, signEq⟩ := calibrated
    exact Or.inr
      ⟨constitutionallyRigid_of_ligandAtomZ_injective zInjective,
        pointAt, observed, nonzero, signEq⟩

/-- **Canonical conversion of one physical general rigid center.**  The physical coordinates are
reindexed by `beta.symm`; nonzero volume is retained (the alternating volume acquires the factor
`permHandedness beta`), and the physical sign equation at `cfgPhys` becomes the canonical sign
equation at `cfgCan = cfgPhys * beta`.  The rigidity and twin status are those of the original
detected molecule. -/
theorem actualGeneralRigidCalibratedCenter_of_physicalGeneralRigidCalibratedCenter
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (center : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input
      input.detectedMultiCenterMolecule cfg center) :
    ActualGeneralRigidCalibratedCenter input
      (input.canonicalReindexConfiguration cfg) center := by
  obtain ⟨rigid, pointAtP, observedP, nonzeroP, signP⟩ := calibrated
  let beta : Equiv.Perm (Fin 4) := input.canonicalLigandReindex center
  let pointAtC : Fin 4 → CartesianPoint3 := fun i => pointAtP (beta.symm i)
  have hpoint : ∀ i : Fin 4, pointAtC i = pointAtP (beta.symm i) := fun _ => rfl
  have hvec : ∀ k : Fin 4,
      RationalTetrahedralPermutation.pointVector
        (pointAtP 0) (pointAtP 1) (pointAtP 2) (pointAtP 3) k = pointAtP k := by
    intro k
    fin_cases k <;> rfl
  have hpermuted : RationalTetrahedralPermutation.permutedOrientedVolume
        (pointAtP 0) (pointAtP 1) (pointAtP 2) (pointAtP 3) beta.symm =
      CartesianPoint3.orientedVolume
        (pointAtP (beta.symm 0)) (pointAtP (beta.symm 1))
          (pointAtP (beta.symm 2)) (pointAtP (beta.symm 3)) := by
    simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
  refine ⟨rigid, pointAtC, ?_, ?_, ?_⟩
  · intro i
    have hcanon : input.canonicalLigandAtom center i =
        input.detectedMultiCenterMolecule.ligandAtomAt center (beta.symm i) := by
      have h := input.canonicalLigandReindex_spec center (beta.symm i)
      simpa [beta] using h.symm
    rw [hcanon, observedP (beta.symm i)]
  · have hnonzero : CartesianPoint3.orientedVolume
        (pointAtP (beta.symm 0)) (pointAtP (beta.symm 1))
          (pointAtP (beta.symm 2)) (pointAtP (beta.symm 3)) ≠ 0 :=
      cartesianOrientedVolume_perm_ne_zero pointAtP beta.symm nonzeroP
    simpa [hpoint] using hnonzero
  · have hvol : CartesianPoint3.orientedVolume
        (pointAtC 0) (pointAtC 1) (pointAtC 2) (pointAtC 3) =
        RationalTetrahedralPermutation.permutedOrientedVolume
          (pointAtP 0) (pointAtP 1) (pointAtP 2) (pointAtP 3) beta.symm := by
      simpa [pointAtC] using hpermuted.symm
    rw [hvol, rationalVolumeSign_permutedOrientedVolume, signP]
    have hsymm : (Equiv.symm beta : Equiv.Perm (Fin 4)) = beta⁻¹ := rfl
    rw [hsymm, permHandedness_inv]
    simp only [MultiCenterMolecule.configurationSign, canonicalReindexConfiguration, beta,
      permHandedness_mul]




theorem actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input
      input.detectedMultiCenterMolecule cfg root) :
    ActualGeneralRigidGlobalPhysicalDomain input
      (input.canonicalReindexConfiguration cfg) root := by
  refine actualGeneralRigidGlobalPhysicalDomain_of_centerCase input
    (input.canonicalReindexConfiguration cfg) root ?_
  intro center center_ne_root
  rcases domain.centerCase center center_ne_root with twin | calibrated
  · exact Or.inl twin
  · exact Or.inr
      (actualGeneralRigidCalibratedCenter_of_physicalGeneralRigidCalibratedCenter
        input cfg center calibrated)







theorem exists_physicalFrameSlotLink
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (center : input.detectedMultiCenterMolecule.Center)
    (targetCurrent : target.1.node.current? = some center.1) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (alpha : Equiv.Perm (Fin 4)),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (input.detectedMultiCenterMolecule.ligandAtomAt center (alpha i)) :=
  input.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
    singleBonded acyclic enough target targetCurrent
    input.detectedMultiCenterMolecule (detectedMultiCenter_mol input) center rfl

/-- **Reusable `PhysicalFrameCalibration` in the original detected enumeration.**  A physical
general rigid calibrated center already carries source coordinates on `m.ligandAtomAt`, nonzero
exact volume and the physical configuration sign.  Conjugating those coordinates by any slot
permutation `alpha` gives a `PhysicalFrameCalibration m cfg center alpha (fun i => pointAt (alpha
i))` for the same molecule, configuration and center.  No canonical alignment, frame or desired
geometry is assumed; the permutation is the caller's actual frame slot permutation. -/
theorem physicalFrameCalibration_of_generalRigidCalibratedCenter
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (center : m.Center)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input m cfg center)
    (alpha : Equiv.Perm (Fin 4)) :
    ∃ pointAt : Fin 4 → CartesianPoint3,
      Nonempty (PhysicalFrameCalibration m cfg center alpha (fun i => pointAt (alpha i))) := by
  obtain ⟨_rigid, pointAt, _observed, nonzero, signEq⟩ := calibrated
  exact ⟨pointAt, ⟨{ physicalPointAt := pointAt,
                      calibrated := fun _i => rfl,
                      nondegenerate := nonzero,
                      sign_eq := signEq }⟩⟩







theorem exists_canonicalFrameSlotLink
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (center : input.TetrahedralCenter)
    (targetCurrent : target.1.node.current? = some center.1) :
    ∃ (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
      (alpha : Equiv.Perm (Fin 4)),
      input.localizedOccurrenceFourLigandFrame? target = some frame ∧
        ∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (input.canonicalLigandAtom center (alpha i)) := by
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
      singleBonded acyclic enough target targetCurrent
      input.canonicalDetectedMultiCenterMolecule rfl center rfl
  exact ⟨frame, alpha, frameComputed, fun i => by
    simpa using ligandLink i⟩

/-- **Canonical actual root coordinate availability.**  The four canonical ligand atoms of a
detected center have concrete source coordinates and their written order has nonzero oriented
volume.  This is the genuine physical geometry hypothesis; it mentions no frame, sort, key or
label. -/
def ActualCanonicalRootCoordinates
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) : Prop :=
  ∃ pointAt : Fin 4 → CartesianPoint3,
    (∀ i, input.spatialPointAt? (input.canonicalLigandAtom center i) = some (pointAt i)) ∧
      CartesianPoint3.orientedVolume
        (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0









theorem actualFrameRealNodeCoordinates_of_canonicalRootCoordinates
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (center : input.TetrahedralCenter)
    (targetCurrent : target.1.node.current? = some center.1)
    (pointAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.spatialPointAt? (input.canonicalLigandAtom center i) =
      some (pointAt i))
    (nonzero : CartesianPoint3.orientedVolume
      (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0) :
    input.ActualFrameRealNodeCoordinates target := by
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.exists_canonicalFrameSlotLink target singleBonded acyclic enough center targetCurrent
  let atomAt : Fin 4 → input.Atom := fun i => input.canonicalLigandAtom center (alpha i)
  let pointsAt : Fin 4 → CartesianPoint3 := fun i => pointAt (alpha i)
  have current : ∀ i : Fin 4,
      (frame.cursorAt i).occurrence.1.node.current? = some (atomAt i) := by
    intro i
    simpa [atomAt] using ligandLink i
  have physical : ∀ i : Fin 4,
      input.spatialPointAt? (atomAt i) = some (pointsAt i) := by
    intro i
    simpa [atomAt, pointsAt] using observed (alpha i)
  have nonzeroPerm : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 := by
    simpa [pointsAt] using cartesianOrientedVolume_perm_ne_zero pointAt alpha nonzero
  exact input.actualFrameRealNodeCoordinates_of_frame target frame frameComputed
    atomAt pointsAt current physical nonzeroPerm

/-- **Adapter 2 (packaged form).**  Same conclusion from the named canonical root coordinate
predicate. -/
theorem actualFrameRealNodeCoordinates_of_actualCanonicalRootCoordinates
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (center : input.TetrahedralCenter)
    (targetCurrent : target.1.node.current? = some center.1)
    (coordinates : input.ActualCanonicalRootCoordinates center) :
    input.ActualFrameRealNodeCoordinates target := by
  obtain ⟨pointAt, observed, nonzero⟩ := coordinates
  exact input.actualFrameRealNodeCoordinates_of_canonicalRootCoordinates
    target singleBonded acyclic enough center targetCurrent pointAt observed nonzero



theorem actualFrameSpatialCoordinates_of_canonicalRootCoordinates
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (center : input.TetrahedralCenter)
    (targetCurrent : target.1.node.current? = some center.1)
    (pointAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, input.spatialPointAt? (input.canonicalLigandAtom center i) =
      some (pointAt i))
    (nonzero : CartesianPoint3.orientedVolume
      (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0) :
    input.ActualFrameSpatialCoordinates target :=
  input.actualFrameSpatialCoordinates_of_realNode target
    (input.actualFrameRealNodeCoordinates_of_canonicalRootCoordinates
      target singleBonded acyclic enough center targetCurrent pointAt observed nonzero)

/-! ## Public kernel guards -/

assert_kernel_only TetraStereo.OneCenter.constitutionallyRigid_of_atomZ_injective_on_neighbors
assert_kernel_only
  TetraStereo.OneCenter.atomZ_injective_on_neighbors_of_ligandAtomZ_injective
assert_kernel_only TetraStereo.OneCenter.constitutionallyRigid_of_ligandAtomZ_injective
assert_kernel_only TetraStereo.OneCenter.toRealTetrahedralGeometry_fun_eq
assert_kernel_only TetraStereo.OneCenter.orientedVolume_fun_eq_realOrientedVolume
assert_kernel_only TetraStereo.OneCenter.cartesianOrientedVolume_perm_ne_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_congr_mol
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalDetectedMultiCenterMolecule
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalDetectedMultiCenterMolecule_mol
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalDetectedMultiCenterMolecule_centers
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalDetectedMultiCenterMolecule_ligandAtomAt
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutionallyRigid_of_canonicalLigandAtomZ_injective
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidCalibratedCenter_of_canonicalPhysicalCalibratedCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidGlobalPhysicalDomain_of_canonicalPhysicalCalibratedDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalLigandReindex
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalLigandReindex_spec
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalReindexConfiguration
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalGeneralRigidCalibratedCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualGeneralRigidPhysicalDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidPhysicalDomain_of_physicalCalibratedDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidCalibratedCenter_of_physicalGeneralRigidCalibratedCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_physicalFrameSlotLink
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalFrameCalibration_of_generalRigidCalibratedCenter
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_canonicalFrameSlotLink
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualCanonicalRootCoordinates
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrameRealNodeCoordinates_of_canonicalRootCoordinates
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrameRealNodeCoordinates_of_actualCanonicalRootCoordinates
assert_kernel_only
  TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrameSpatialCoordinates_of_canonicalRootCoordinates

end CertifiedLocalizedCIPInput

end OneCenter
end TetraStereo
