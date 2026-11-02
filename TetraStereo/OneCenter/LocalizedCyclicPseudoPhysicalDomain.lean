import TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness
import TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Actual physical domain for the nine-atom cyclic fixture

The molecule below is the certified input graph with its detected degree-four center inventory.
Its atom type is explicitly identified with `Fin 9`; the local frames are transported from the
accepted canonical source-coordinate calibration through that atom-index equivalence.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain

noncomputable section

open TetraStereo.OneCenter
open CertifiedLocalizedCIPInput
open CartesianPoint3
open RootedTetrahedralBranchSymmetry
open LocalizedCyclicPseudoInputWitness
open LocalizedCyclicPseudoSpatialWitness
open LocalizedCyclicPseudoGeneratedLabels

private theorem spatial_atomCount :
    pseudoSpatialCertified.certified.input.molecule.atomCount = 9 := by
  have moleculeEq : pseudoSpatialCertified.certified.input.molecule = pseudoSource.molecule := by
    rw [show pseudoSpatialCertified.certified.input = pseudoSpatialSource from rfl,
      spatial_molecule]
  rw [moleculeEq]
  exact atomCount_eq

private def atomToActual (i : Fin 9) : pseudoSpatialCertified.Atom :=
  ⟨i.val, by have h := i.isLt; rw [spatial_atomCount]; exact h⟩

private def atomToFin (a : pseudoSpatialCertified.Atom) : Fin 9 :=
  ⟨a.val, by simpa only [spatial_atomCount] using a.isLt⟩

def atomEquiv : Fin 9 ≃ pseudoSpatialCertified.Atom where
  toFun := atomToActual
  invFun := atomToFin
  left_inv := by intro i; apply Fin.ext; rfl
  right_inv := by intro a; apply Fin.ext; rfl

private theorem atomEquiv_val (i : Fin 9) : (atomEquiv i).val = i.val := rfl

theorem actualZ (i : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.atomZ (atomEquiv i) = graph.atomZ i := by
  simp [CertifiedLocalizedCIPInput.moleculeGraph,
    pseudoSpatialCertified, pseudoSpatialCertifiedAuthority, spatial_molecule,
    graph, pseudoCertified, pseudoCertifiedAuthority, atomEquiv, atomToActual]

theorem actualMass (i : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.atomMass (atomEquiv i) = graph.atomMass i := by
  simp [CertifiedLocalizedCIPInput.moleculeGraph,
    pseudoSpatialCertified, pseudoSpatialCertifiedAuthority, spatial_molecule,
    graph, pseudoCertified, pseudoCertifiedAuthority, atomEquiv, atomToActual]

theorem actualCharge (i : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.formalCharge (atomEquiv i) = graph.formalCharge i := by
  simp [CertifiedLocalizedCIPInput.moleculeGraph,
    pseudoSpatialCertified, pseudoSpatialCertifiedAuthority, spatial_molecule,
    graph, pseudoCertified, pseudoCertifiedAuthority, atomEquiv, atomToActual]

theorem actualBond (i j : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.bond (atomEquiv i) (atomEquiv j) = graph.bond i j := by
  simp [CertifiedLocalizedCIPInput.moleculeGraph,
    pseudoSpatialCertified, pseudoSpatialCertifiedAuthority, spatial_molecule,
    graph, pseudoCertified, pseudoCertifiedAuthority, atomEquiv, atomToActual]

theorem actualAdj (i j : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.Adj (atomEquiv i) (atomEquiv j) ↔ graph.Adj i j := by
  simp [MoleculeGraph.Adj, actualBond]

theorem actualNeighborFinset (i : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.neighborFinset (atomEquiv i) =
      Finset.map atomEquiv.toEmbedding (graph.neighborFinset i) := by
  ext a
  constructor
  · intro ha
    let j := atomEquiv.symm a
    have hja : atomEquiv j = a := atomEquiv.apply_symm_apply a
    refine Finset.mem_map.mpr ⟨j, ?_, hja⟩
    exact (MoleculeGraph.mem_neighborFinset _ _ _).mpr
      ((actualAdj i j).mp ((MoleculeGraph.mem_neighborFinset _ _ _).mp ha))
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨j, hj, hja⟩
    subst a
    exact (MoleculeGraph.mem_neighborFinset _ _ _).mpr
      ((actualAdj i j).mpr ((MoleculeGraph.mem_neighborFinset _ _ _).mp hj))

private theorem actualCenter_iff (i : Fin 9) :
    atomEquiv i ∈ pseudoSpatialCertified.tetrahedralCenterSet ↔
      i ∈ graph.tetrahedralCenterSet := by
  rw [CertifiedLocalizedCIPInput.tetrahedralCenterSet,
    MoleculeGraph.mem_tetrahedralCenterSet, MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card,
    MoleculeGraph.mem_tetrahedralCenterSet, MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card,
    actualNeighborFinset, Finset.card_map]

private theorem actualPoint (i : Fin 9) (p : CartesianPoint3)
    (lookup : positions[i.val]? = some p) :
    pseudoSpatialCertified.spatialPointAt? (atomEquiv i) = some p := by
  rw [spatialPointAt?_eq_some_iff]
  exact ⟨⟨positions⟩, rfl, by simpa [atomEquiv] using lookup⟩

private def physicalCenters : Finset pseudoSpatialCertified.Atom :=
  Finset.map atomEquiv.toEmbedding graph.tetrahedralCenterSet

abbrev PhysicalCenter := {c : pseudoSpatialCertified.Atom // c ∈ physicalCenters}

noncomputable def centerToCanon (c : PhysicalCenter) : canon.Center := by
  refine ⟨atomEquiv.symm c.1, ?_⟩
  have hmap := Finset.mem_map.mp c.2
  obtain ⟨source, sourceMember, sourceEq⟩ := hmap
  have invEq : atomEquiv.symm c.1 = source := by
    rw [← sourceEq]
    simp
  rw [invEq]
  exact sourceMember

theorem centerToCanon_val (c : PhysicalCenter) :
    atomEquiv (centerToCanon c).1 = c.1 := by
  simp [centerToCanon]

noncomputable def physicalMolecule : MultiCenterMolecule pseudoSpatialCertified.Atom where
  mol := pseudoSpatialCertified.moleculeGraph
  centers := physicalCenters
  ligandAtom c hc i := atomEquiv (canon.ligandAtomAt (centerToCanon ⟨c, hc⟩) i)
  ligandAtom_adj := by
    intro c hc i
    let cc : PhysicalCenter := ⟨c, hc⟩
    exact (actualAdj (centerToCanon cc).1
      (canon.ligandAtomAt (centerToCanon cc) i)).mpr
        (canon.ligandAtom_adj (centerToCanon cc).1 (centerToCanon cc).2 i)
  ligandAtom_injective := by
    intro c hc i j equal
    apply canon.ligandAtom_injective (centerToCanon ⟨c, hc⟩)
    exact atomEquiv.injective equal
  ligandAtom_surjective := by
    intro c hc a adjacent
    let cc : PhysicalCenter := ⟨c, hc⟩
    have hcenter : atomEquiv (centerToCanon cc).1 = c := atomEquiv.apply_symm_apply c
    have adj9 : graph.Adj (centerToCanon cc).1 (atomEquiv.symm a) := by
      apply (actualAdj (centerToCanon cc).1 (atomEquiv.symm a)).mp
      simpa [hcenter] using adjacent
    obtain ⟨i, hi⟩ := canon.ligandAtom_surjective (centerToCanon cc).1
      (centerToCanon cc).2 (atomEquiv.symm a) adj9
    exact ⟨i, by
      change atomEquiv (canon.ligandAtomAt (centerToCanon cc) i) = a
      calc
        atomEquiv (canon.ligandAtomAt (centerToCanon cc) i) =
            atomEquiv (atomEquiv.symm a) := congrArg atomEquiv hi
        _ = a := atomEquiv.apply_symm_apply a⟩

noncomputable def centerFromCanon (c : canon.Center) : physicalMolecule.Center :=
  ⟨atomEquiv c.1, Finset.mem_map.mpr ⟨c.1, c.2, rfl⟩⟩

theorem centerToCanon_fromCanon (c : canon.Center) :
    centerToCanon (centerFromCanon c) = c := by
  apply Subtype.ext
  apply Fin.ext
  rfl

theorem centerFromCanon_toCanon (c : physicalMolecule.Center) :
    centerFromCanon (centerToCanon c) = c := by
  apply Subtype.ext
  apply Fin.ext
  rfl

theorem physical_ligandAt (c : canon.Center) (i : Fin 4) :
    physicalMolecule.ligandAtomAt (centerFromCanon c) i =
      atomEquiv (canon.ligandAtomAt c i) := by
  change atomEquiv (canon.ligandAtomAt (centerToCanon (centerFromCanon c)) i) = _
  rw [centerToCanon_fromCanon]

noncomputable def physicalCfg : physicalMolecule.Configuration :=
  fun c => pseudoCfg (centerToCanon c)

noncomputable def rootCenter : physicalMolecule.Center := centerFromCanon LocalizedCyclicPseudoSpatialWitness.rootCenter
private noncomputable def armCenter : physicalMolecule.Center := centerFromCanon LocalizedCyclicPseudoSpatialWitness.armCenter
private noncomputable def closingCenter : physicalMolecule.Center := centerFromCanon LocalizedCyclicPseudoSpatialWitness.closingCenter

theorem physical_arm_ligandAt (i : Fin 4) :
    physicalMolecule.ligandAtomAt armCenter i =
      atomEquiv (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.armCenter i) := by
  simpa [armCenter] using physical_ligandAt LocalizedCyclicPseudoSpatialWitness.armCenter i

theorem physical_closing_ligandAt (i : Fin 4) :
    physicalMolecule.ligandAtomAt closingCenter i =
      atomEquiv (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.closingCenter i) := by
  simpa [closingCenter] using physical_ligandAt LocalizedCyclicPseudoSpatialWitness.closingCenter i

private theorem graph_eq : physicalMolecule.mol = pseudoSpatialCertified.moleculeGraph := rfl

noncomputable def pullbackAut (e : physicalMolecule.Aut) : canon.Aut := by
  let p : Equiv.Perm (Fin 9) := atomEquiv.trans ((e : Equiv.Perm pseudoSpatialCertified.Atom).trans atomEquiv.symm)
  let eM : pseudoSpatialCertified.moleculeGraph.Aut :=
    ⟨(e : Equiv.Perm pseudoSpatialCertified.Atom), e.property.1⟩
  have pa : graph.IsAutomorphism p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have applyEq : atomEquiv (p i) = (e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i) := by
        simp [p, Equiv.trans_apply]
      calc
        graph.atomZ (p i) = pseudoSpatialCertified.moleculeGraph.atomZ (atomEquiv (p i)) :=
          (actualZ (p i)).symm
        _ = pseudoSpatialCertified.moleculeGraph.atomZ ((e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i)) := by rw [applyEq]
        _ = pseudoSpatialCertified.moleculeGraph.atomZ (atomEquiv i) :=
          MoleculeGraph.Aut.atomZ_eq pseudoSpatialCertified.moleculeGraph eM _
        _ = graph.atomZ i := actualZ i
    · intro i
      have applyEq : atomEquiv (p i) = (e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i) := by
        simp [p, Equiv.trans_apply]
      calc
        graph.atomMass (p i) = pseudoSpatialCertified.moleculeGraph.atomMass (atomEquiv (p i)) :=
          (actualMass (p i)).symm
        _ = pseudoSpatialCertified.moleculeGraph.atomMass ((e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i)) := by rw [applyEq]
        _ = pseudoSpatialCertified.moleculeGraph.atomMass (atomEquiv i) :=
          MoleculeGraph.Aut.atomMass_eq pseudoSpatialCertified.moleculeGraph eM _
        _ = graph.atomMass i := actualMass i
    · intro i
      have applyEq : atomEquiv (p i) = (e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i) := by
        simp [p, Equiv.trans_apply]
      calc
        graph.formalCharge (p i) = pseudoSpatialCertified.moleculeGraph.formalCharge (atomEquiv (p i)) :=
          (actualCharge (p i)).symm
        _ = pseudoSpatialCertified.moleculeGraph.formalCharge ((e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i)) := by rw [applyEq]
        _ = pseudoSpatialCertified.moleculeGraph.formalCharge (atomEquiv i) :=
          MoleculeGraph.Aut.formalCharge_eq pseudoSpatialCertified.moleculeGraph eM _
        _ = graph.formalCharge i := actualCharge i
    · intro i j
      have applyEqI : atomEquiv (p i) = (e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i) := by
        simp [p, Equiv.trans_apply]
      have applyEqJ : atomEquiv (p j) = (e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv j) := by
        simp [p, Equiv.trans_apply]
      calc
        graph.bond (p i) (p j) = pseudoSpatialCertified.moleculeGraph.bond (atomEquiv (p i)) (atomEquiv (p j)) :=
          (actualBond (p i) (p j)).symm
        _ = pseudoSpatialCertified.moleculeGraph.bond
            ((e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i))
            ((e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv j)) := by rw [applyEqI, applyEqJ]
        _ = pseudoSpatialCertified.moleculeGraph.bond (atomEquiv i) (atomEquiv j) :=
          MoleculeGraph.Aut.bond_eq pseudoSpatialCertified.moleculeGraph eM _ _
        _ = graph.bond i j := actualBond i j
  have aut : graph.Aut := ⟨p, pa⟩
  refine ⟨p, pa, ?_⟩
  intro i
  change i ∈ graph.tetrahedralCenterSet ↔ p i ∈ graph.tetrahedralCenterSet
  have conv (j : Fin 9) : atomEquiv j ∈ physicalCenters ↔ j ∈ graph.tetrahedralCenterSet := by
    simp [physicalCenters]
  have h := e.property.2 (atomEquiv i)
  have applyEq : atomEquiv (p i) = (e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv i) := by
    simp [p, Equiv.trans_apply]
  rw [← applyEq] at h
  exact (conv i).symm.trans (h.trans (conv (p i)))

/-- Transport a canonical fixture automorphism to the actual certified atom type. -/
noncomputable def pushforwardAut (e : canon.Aut) : physicalMolecule.Aut := by
  let p : Equiv.Perm pseudoSpatialCertified.Atom :=
    atomEquiv.symm.trans ((e : Equiv.Perm (Fin 9)).trans atomEquiv)
  have app (a : pseudoSpatialCertified.Atom) :
      p a = atomEquiv ((e : Equiv.Perm (Fin 9)) (atomEquiv.symm a)) := by
    simp [p, Equiv.trans_apply]
  let ep : graph.Aut := ⟨(e : Equiv.Perm (Fin 9)), e.property.1⟩
  have epeq : (ep : Equiv.Perm (Fin 9)) = (e : Equiv.Perm (Fin 9)) := by
    ext i
    simp [ep]
  have pa : pseudoSpatialCertified.moleculeGraph.IsAutomorphism p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      let i := atomEquiv.symm a
      calc
        pseudoSpatialCertified.moleculeGraph.atomZ (p a) =
            pseudoSpatialCertified.moleculeGraph.atomZ
              (atomEquiv ((e : Equiv.Perm (Fin 9)) i)) := by rw [app]
        _ = graph.atomZ ((e : Equiv.Perm (Fin 9)) i) := actualZ ((e : Equiv.Perm (Fin 9)) i)
        _ = graph.atomZ i := by
          rw [← epeq]
          exact MoleculeGraph.Aut.atomZ_eq graph ep i
        _ = pseudoSpatialCertified.moleculeGraph.atomZ (atomEquiv i) := (actualZ i).symm
        _ = pseudoSpatialCertified.moleculeGraph.atomZ a := by simp [i]
    · intro a
      let i := atomEquiv.symm a
      calc
        pseudoSpatialCertified.moleculeGraph.atomMass (p a) =
            pseudoSpatialCertified.moleculeGraph.atomMass
              (atomEquiv ((e : Equiv.Perm (Fin 9)) i)) := by rw [app]
        _ = graph.atomMass ((e : Equiv.Perm (Fin 9)) i) := actualMass ((e : Equiv.Perm (Fin 9)) i)
        _ = graph.atomMass i := by
          rw [← epeq]
          exact MoleculeGraph.Aut.atomMass_eq graph ep i
        _ = pseudoSpatialCertified.moleculeGraph.atomMass (atomEquiv i) := (actualMass i).symm
        _ = pseudoSpatialCertified.moleculeGraph.atomMass a := by simp [i]
    · intro a
      let i := atomEquiv.symm a
      calc
        pseudoSpatialCertified.moleculeGraph.formalCharge (p a) =
            pseudoSpatialCertified.moleculeGraph.formalCharge
              (atomEquiv ((e : Equiv.Perm (Fin 9)) i)) := by rw [app]
        _ = graph.formalCharge ((e : Equiv.Perm (Fin 9)) i) := actualCharge ((e : Equiv.Perm (Fin 9)) i)
        _ = graph.formalCharge i := by
          rw [← epeq]
          exact MoleculeGraph.Aut.formalCharge_eq graph ep i
        _ = pseudoSpatialCertified.moleculeGraph.formalCharge (atomEquiv i) := (actualCharge i).symm
        _ = pseudoSpatialCertified.moleculeGraph.formalCharge a := by simp [i]
    · intro a b
      let i := atomEquiv.symm a
      let j := atomEquiv.symm b
      calc
        pseudoSpatialCertified.moleculeGraph.bond (p a) (p b) =
            pseudoSpatialCertified.moleculeGraph.bond
              (atomEquiv ((e : Equiv.Perm (Fin 9)) i))
              (atomEquiv ((e : Equiv.Perm (Fin 9)) j)) := by rw [app, app]
        _ = graph.bond ((e : Equiv.Perm (Fin 9)) i) ((e : Equiv.Perm (Fin 9)) j) :=
          actualBond ((e : Equiv.Perm (Fin 9)) i) ((e : Equiv.Perm (Fin 9)) j)
        _ = graph.bond i j := by
          rw [← epeq]
          exact MoleculeGraph.Aut.bond_eq graph ep i j
        _ = pseudoSpatialCertified.moleculeGraph.bond (atomEquiv i) (atomEquiv j) := (actualBond i j).symm
        _ = pseudoSpatialCertified.moleculeGraph.bond a b := by simp [i, j]
  refine ⟨p, pa, ?_⟩
  intro a
  let i := atomEquiv.symm a
  have conv (j : Fin 9) : atomEquiv j ∈ physicalMolecule.centers ↔ j ∈ graph.tetrahedralCenterSet := by
    simp [physicalMolecule, physicalCenters]
  have h := e.property.2 i
  have hpi : p a = atomEquiv ((e : Equiv.Perm (Fin 9)) i) := app a
  rw [hpi]
  exact (conv i).symm.trans (h.trans (conv ((e : Equiv.Perm (Fin 9)) i)))

theorem pullback_pushforwardAut (e : canon.Aut) :
    pullbackAut (pushforwardAut e) = e := by
  apply Subtype.ext
  ext i
  simp [pullbackAut, pushforwardAut, Equiv.trans_apply]

theorem pushforward_pullbackAut (e : physicalMolecule.Aut) :
    pushforwardAut (pullbackAut e) = e := by
  apply Subtype.ext
  ext a
  simp [pullbackAut, pushforwardAut, Equiv.trans_apply]

/-- The center permutation commutes with the canonical/actual center identification. -/
theorem centerToCanon_centerPerm_pushforward (e : canon.Aut) (c : canon.Center) :
    centerToCanon (physicalMolecule.centerPerm (pushforwardAut e) (centerFromCanon c)) =
      canon.centerPerm e c := by
  apply Subtype.ext
  change atomEquiv.symm
      ((pushforwardAut e : Equiv.Perm pseudoSpatialCertified.Atom) (atomEquiv c.1)) =
    (e : Equiv.Perm (Fin 9)) c.1
  simp [pushforwardAut, Equiv.trans_apply]

theorem centerPerm_pushforward (e : canon.Aut) (c : canon.Center) :
    physicalMolecule.centerPerm (pushforwardAut e) (centerFromCanon c) =
      centerFromCanon (canon.centerPerm e c) := by
  apply centerToCanon_injective
  rw [centerToCanon_centerPerm_pushforward, centerToCanon_fromCanon]
  where
    centerToCanon_injective : Function.Injective centerToCanon := by
      intro x y h
      have h' := congrArg centerFromCanon h
      simpa only [centerFromCanon_toCanon] using h'

/-- The induced ligand-index permutation is unchanged under the actual/canonical transport. -/
theorem ligandPermAt_pushforward (e : canon.Aut) (c : canon.Center) (i : Fin 4) :
    physicalMolecule.ligandPermAt (pushforwardAut e) (centerFromCanon c) i =
      canon.ligandPermAt e c i := by
  apply canon.ligandAtomAt_injective (canon.centerPerm e c)
  apply atomEquiv.injective
  calc
    atomEquiv (canon.ligandAtomAt (canon.centerPerm e c) (physicalMolecule.ligandPermAt
        (pushforwardAut e) (centerFromCanon c) i)) =
        physicalMolecule.ligandAtomAt (centerFromCanon (canon.centerPerm e c))
          (physicalMolecule.ligandPermAt (pushforwardAut e) (centerFromCanon c) i) := by
      rw [← centerPerm_pushforward]
      exact (physical_ligandAt (canon.centerPerm e c) _).symm
    _ = (pushforwardAut e : Equiv.Perm pseudoSpatialCertified.Atom)
          (physicalMolecule.ligandAtomAt (centerFromCanon c) i) := by
      simpa only [centerPerm_pushforward] using
        physicalMolecule.ligandAtomAt_ligandPermAt (pushforwardAut e) (centerFromCanon c) i
    _ = atomEquiv (canon.ligandAtomAt (canon.centerPerm e c) (canon.ligandPermAt e c i)) := by
      rw [physical_ligandAt]
      simp [pushforwardAut, Equiv.trans_apply, canon.ligandAtomAt_ligandPermAt]

theorem ligandPermAt_pushforward_eq (e : canon.Aut) (c : canon.Center) :
    physicalMolecule.ligandPermAt (pushforwardAut e) (centerFromCanon c) =
      canon.ligandPermAt e c := by
  ext i
  exact congrArg Fin.val (ligandPermAt_pushforward e c i)

/-- The transported actual configuration has exactly the canonical sign at corresponding centers. -/
theorem configurationSign_physicalCfg (c : canon.Center) :
    physicalMolecule.configurationSign physicalCfg (centerFromCanon c) =
      canon.configurationSign pseudoCfg c := by
  change permHandedness (physicalCfg (centerFromCanon c)) = permHandedness (pseudoCfg c)
  rw [physicalCfg, centerToCanon_fromCanon]

private theorem armRigid : ConstitutionallyRigid physicalMolecule armCenter := by
  intro e fixed
  let e0 := pullbackAut e
  have centerFix : canon.centerPerm e0 LocalizedCyclicPseudoSpatialWitness.armCenter =
      LocalizedCyclicPseudoSpatialWitness.armCenter := by
    apply (centerPerm_eq_iff canon e0 _).2
    have h := (centerPerm_eq_iff physicalMolecule e armCenter).1 fixed
    change (e : Equiv.Perm pseudoSpatialCertified.Atom) armCenter.1 = armCenter.1 at h
    have h' : atomEquiv ((e0 : Equiv.Perm (Fin 9)) LocalizedCyclicPseudoSpatialWitness.armCenter.1) =
        (e : Equiv.Perm pseudoSpatialCertified.Atom)
          (atomEquiv LocalizedCyclicPseudoSpatialWitness.armCenter.1) := by
      simp [e0, pullbackAut, Equiv.trans_apply]
    apply atomEquiv.injective
    rw [h']
    exact h
  have localRigid := (nonroot_constitutionally_rigid e0).1 centerFix
  apply Equiv.ext
  intro i
  have ligandTransport := physicalMolecule.ligandAtomAt_ligandPermAt e armCenter i
  rw [fixed] at ligandTransport
  have pulledLigand := canon.ligandAtomAt_ligandPermAt e0
    LocalizedCyclicPseudoSpatialWitness.armCenter i
  rw [centerFix] at pulledLigand
  have imageEq : atomEquiv ((e0 : Equiv.Perm (Fin 9))
      (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.armCenter i)) =
      (e : Equiv.Perm pseudoSpatialCertified.Atom)
        (physicalMolecule.ligandAtomAt armCenter i) := by
    rw [physical_arm_ligandAt]
    simp [e0, pullbackAut, Equiv.trans_apply]
  have idxEq : (physicalMolecule.ligandPermAt e armCenter) i =
      (canon.ligandPermAt e0 LocalizedCyclicPseudoSpatialWitness.armCenter) i := by
    apply canon.ligandAtom_injective LocalizedCyclicPseudoSpatialWitness.armCenter
    apply atomEquiv.injective
    calc
      atomEquiv (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.armCenter
          ((physicalMolecule.ligandPermAt e armCenter) i)) =
        (e : Equiv.Perm pseudoSpatialCertified.Atom)
          (physicalMolecule.ligandAtomAt armCenter i) := by
            rw [← ligandTransport]
            rw [physical_arm_ligandAt ((physicalMolecule.ligandPermAt e armCenter) i)]
      _ = atomEquiv (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.armCenter
          ((canon.ligandPermAt e0 LocalizedCyclicPseudoSpatialWitness.armCenter) i)) := by
            rw [← imageEq]
            exact (congrArg atomEquiv pulledLigand).symm
  rw [idxEq, localRigid]

private theorem closingRigid : ConstitutionallyRigid physicalMolecule closingCenter := by
  intro e fixed
  let e0 := pullbackAut e
  have centerFix : canon.centerPerm e0 LocalizedCyclicPseudoSpatialWitness.closingCenter =
      LocalizedCyclicPseudoSpatialWitness.closingCenter := by
    apply (centerPerm_eq_iff canon e0 _).2
    have h := (centerPerm_eq_iff physicalMolecule e closingCenter).1 fixed
    change (e : Equiv.Perm pseudoSpatialCertified.Atom) closingCenter.1 = closingCenter.1 at h
    have h' : atomEquiv ((e0 : Equiv.Perm (Fin 9)) LocalizedCyclicPseudoSpatialWitness.closingCenter.1) =
        (e : Equiv.Perm pseudoSpatialCertified.Atom)
          (atomEquiv LocalizedCyclicPseudoSpatialWitness.closingCenter.1) := by
      simp [e0, pullbackAut, Equiv.trans_apply]
    apply atomEquiv.injective
    rw [h']
    exact h
  have localRigid := (nonroot_constitutionally_rigid e0).2 centerFix
  apply Equiv.ext
  intro i
  have ligandTransport := physicalMolecule.ligandAtomAt_ligandPermAt e closingCenter i
  rw [fixed] at ligandTransport
  have pulledLigand := canon.ligandAtomAt_ligandPermAt e0
    LocalizedCyclicPseudoSpatialWitness.closingCenter i
  rw [centerFix] at pulledLigand
  have imageEq : atomEquiv ((e0 : Equiv.Perm (Fin 9))
      (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.closingCenter i)) =
      (e : Equiv.Perm pseudoSpatialCertified.Atom)
        (physicalMolecule.ligandAtomAt closingCenter i) := by
    rw [physical_closing_ligandAt]
    simp [e0, pullbackAut, Equiv.trans_apply]
  have idxEq : (physicalMolecule.ligandPermAt e closingCenter) i =
      (canon.ligandPermAt e0 LocalizedCyclicPseudoSpatialWitness.closingCenter) i := by
    apply canon.ligandAtom_injective LocalizedCyclicPseudoSpatialWitness.closingCenter
    apply atomEquiv.injective
    calc
      atomEquiv (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.closingCenter
          ((physicalMolecule.ligandPermAt e closingCenter) i)) =
        (e : Equiv.Perm pseudoSpatialCertified.Atom)
          (physicalMolecule.ligandAtomAt closingCenter i) := by
            rw [← ligandTransport]
            rw [physical_closing_ligandAt ((physicalMolecule.ligandPermAt e closingCenter) i)]
      _ = atomEquiv (canon.ligandAtomAt LocalizedCyclicPseudoSpatialWitness.closingCenter
          ((canon.ligandPermAt e0 LocalizedCyclicPseudoSpatialWitness.closingCenter) i)) := by
            rw [← imageEq]
            exact (congrArg atomEquiv pulledLigand).symm
  rw [idxEq, localRigid]

private theorem calibratedArm :
    ActualPhysicalGeneralRigidCalibratedCenter pseudoSpatialCertified physicalMolecule
      physicalCfg armCenter := by
  refine ⟨armRigid, ?_⟩
  refine ⟨fun i => if i = 0 then P0 else if i = 1 then P3 else if i = 2 then P4 else P6,
    ?_, ?_, ?_⟩
  · intro i
    have h0 := actualPoint 0 P0 rfl
    have h3 := actualPoint 3 P3 rfl
    have h4 := actualPoint 4 P4 rfl
    have h6 := actualPoint 6 P6 rfl
    rcases arm_ligands with ⟨l0, l1, l2, l3⟩
    fin_cases i
    · simpa [physical_arm_ligandAt, l0] using h0
    · simpa [physical_arm_ligandAt, l1] using h3
    · simpa [physical_arm_ligandAt, l2] using h4
    · simpa [physical_arm_ligandAt, l3] using h6
  · change orientedVolume P0 P3 P4 P6 ≠ 0
    rw [arm_volume]
    norm_num
  · change rationalVolumeSign (orientedVolume P0 P3 P4 P6) =
      physicalMolecule.configurationSign physicalCfg armCenter
    have cfgEq : physicalMolecule.configurationSign physicalCfg armCenter =
        canon.configurationSign pseudoCfg LocalizedCyclicPseudoSpatialWitness.armCenter := by
      simp [MultiCenterMolecule.configurationSign, physicalCfg, armCenter,
        centerToCanon_fromCanon]
    rw [arm_volume, cfgEq, arm_configurationSign]
    norm_num [rationalVolumeSign]

private theorem calibratedClosing :
    ActualPhysicalGeneralRigidCalibratedCenter pseudoSpatialCertified physicalMolecule
      physicalCfg closingCenter := by
  refine ⟨closingRigid, ?_⟩
  refine ⟨fun i => if i = 0 then P0 else if i = 1 then P2 else if i = 2 then P7 else P8,
    ?_, ?_, ?_⟩
  · intro i
    have h0 := actualPoint 0 P0 rfl
    have h2 := actualPoint 2 P2 rfl
    have h7 := actualPoint 7 P7 rfl
    have h8 := actualPoint 8 P8 rfl
    rcases closing_ligands with ⟨l0, l1, l2, l3⟩
    fin_cases i
    · simpa [physical_closing_ligandAt, l0] using h0
    · simpa [physical_closing_ligandAt, l1] using h2
    · simpa [physical_closing_ligandAt, l2] using h7
    · simpa [physical_closing_ligandAt, l3] using h8
  · change orientedVolume P0 P2 P7 P8 ≠ 0
    rw [closing_volume]
    norm_num
  · change rationalVolumeSign (orientedVolume P0 P2 P7 P8) =
      physicalMolecule.configurationSign physicalCfg closingCenter
    have cfgEq : physicalMolecule.configurationSign physicalCfg closingCenter =
        canon.configurationSign pseudoCfg LocalizedCyclicPseudoSpatialWitness.closingCenter := by
      simp [MultiCenterMolecule.configurationSign, physicalCfg, closingCenter,
        centerToCanon_fromCanon]
    rw [closing_volume, cfgEq, closing_configurationSign]
    norm_num [rationalVolumeSign]

/-- Actual general-rigid physical domain at the actual certified graph and root atom 0. -/
theorem actual_physical_domain :
    ActualGeneralRigidPhysicalDomain pseudoSpatialCertified physicalMolecule physicalCfg rootCenter := by
  refine ⟨graph_eq, ?_⟩
  intro center notRoot
  have cases : (centerToCanon center).1 = 0 ∨ (centerToCanon center).1 = 2 ∨
      (centerToCanon center).1 = 4 := by
    exact (degree_four_iff (centerToCanon center).1).mp (centerToCanon center).2
  rcases cases with hroot | harm | hclosing
  · have hval : center.1 = rootCenter.1 := by
      calc
        center.1 = atomEquiv (centerToCanon center).1 := (centerToCanon_val center).symm
        _ = atomEquiv 0 := congrArg atomEquiv hroot
        _ = rootCenter.1 := by rfl
    have heq : center = rootCenter := Subtype.ext hval
    exact False.elim (notRoot heq)
  · have hval : center.1 = armCenter.1 := by
      calc
        center.1 = atomEquiv (centerToCanon center).1 := (centerToCanon_val center).symm
        _ = atomEquiv 2 := congrArg atomEquiv harm
        _ = armCenter.1 := by rfl
    have heq : center = armCenter := Subtype.ext hval
    subst center
    exact Or.inr calibratedArm
  · have hval : center.1 = closingCenter.1 := by
      calc
        center.1 = atomEquiv (centerToCanon center).1 := (centerToCanon_val center).symm
        _ = atomEquiv 4 := congrArg atomEquiv hclosing
        _ = closingCenter.1 := by rfl
    have heq : center = closingCenter := Subtype.ext hval
    subst center
    exact Or.inr calibratedClosing

/-- The physical molecule's center inventory is exactly the certified input's detected
degree-four inventory, transported along `atomEquiv`. -/
theorem actual_detected_center_inventory (i : Fin 9) :
    atomEquiv i ∈ physicalMolecule.centers ↔
      atomEquiv i ∈ pseudoSpatialCertified.tetrahedralCenterSet := by
  have mapped : atomEquiv i ∈ physicalCenters ↔ i ∈ graph.tetrahedralCenterSet := by
    change atomEquiv i ∈ Finset.map atomEquiv.toEmbedding graph.tetrahedralCenterSet ↔ _
    constructor
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨j, hj, hji⟩
      have : j = i := atomEquiv.injective hji
      simpa [this] using hj
    · intro hi
      exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
  change atomEquiv i ∈ physicalCenters ↔
    atomEquiv i ∈ pseudoSpatialCertified.tetrahedralCenterSet
  rw [mapped, CertifiedLocalizedCIPInput.tetrahedralCenterSet]
  exact (actualCenter_iff i).symm

end

end TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.actual_physical_domain
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.actual_detected_center_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.pullbackAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.pushforwardAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.pullback_pushforwardAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.pushforward_pullbackAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.centerToCanon_centerPerm_pushforward
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.centerPerm_pushforward
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.ligandPermAt_pushforward
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.ligandPermAt_pushforward_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoPhysicalDomain.configurationSign_physicalCfg
