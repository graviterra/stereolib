import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
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

noncomputable section

/-! ## 1. Generic per-center enumeration equality -/

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Generic enumeration adapter.**  Two multi-center molecules on the same vertex type with the
same graph and the same distinguished centers differ by a per-center permutation of their ligand
enumerations: there is `τ` with `m₁.reindexFrames τ = m₂`.

The permutation is the composite `(E₁ c)⁻¹ ∘ E₂ c` of the two bundled ligand equivalences, so no
correspondence between the enumerations is assumed.  The remaining fields of the structure are
propositions and are equal by proof irrelevance. -/
theorem exists_reindexFrames_eq_of_mol_centers_eq {m₁ m₂ : MultiCenterMolecule V}
    (hmol : m₁.mol = m₂.mol) (hcenters : m₁.centers = m₂.centers) :
    ∃ τ : m₁.Center → Equiv.Perm (Fin 4), m₁.reindexFrames τ = m₂ := by
  classical
  rcases m₁ with ⟨mol₁, centers₁, ligand₁, adj₁, inj₁, surj₁⟩
  rcases m₂ with ⟨mol₂, centers₂, ligand₂, adj₂, inj₂, surj₂⟩
  simp only at hmol hcenters
  subst hmol
  subst hcenters
  -- At each center the two enumerations are two bijections `Fin 4 → Neighbor c`; the reindexing is
  -- their comparison.
  have key : ∀ (c : V) (hc : c ∈ centers₁), ∃ σ : Equiv.Perm (Fin 4),
      ∀ i : Fin 4, ligand₁ c hc (σ i) = ligand₂ c hc i := by
    intro c hc
    let e₁ : Fin 4 ≃ mol₁.Neighbor c :=
      MultiCenterMolecule.ligandEquiv
        (⟨mol₁, centers₁, ligand₁, adj₁, inj₁, surj₁⟩ : MultiCenterMolecule V) ⟨c, hc⟩
    let e₂ : Fin 4 ≃ mol₁.Neighbor c :=
      MultiCenterMolecule.ligandEquiv
        (⟨mol₁, centers₁, ligand₂, adj₂, inj₂, surj₂⟩ : MultiCenterMolecule V) ⟨c, hc⟩
    refine ⟨e₂.trans e₁.symm, fun i => ?_⟩
    have h3 : e₁ (e₁.symm (e₂ i)) = e₂ i := Equiv.apply_symm_apply e₁ (e₂ i)
    calc
      ligand₁ c hc ((e₂.trans e₁.symm) i)
          = (e₁ ((e₂.trans e₁.symm) i)).1 := rfl
      _ = (e₁ (e₁.symm (e₂ i))).1 := rfl
      _ = (e₂ i).1 := congrArg Subtype.val h3
      _ = ligand₂ c hc i := rfl
  choose σ hσ using key
  refine ⟨fun c => σ c.1 c.2, ?_⟩
  have hlig :
      (fun (c : V) (hc : c ∈ centers₁) (i : Fin 4) => ligand₁ c hc (σ c hc i)) = ligand₂ := by
    funext c hc i
    exact hσ c hc i
  subst hlig
  let A : MultiCenterMolecule V :=
    MultiCenterMolecule.reindexFrames
      (⟨mol₁, centers₁, ligand₁, adj₁, inj₁, surj₁⟩ : MultiCenterMolecule V)
      (fun c => σ c.1 c.2)
  -- The two structures have definitionally identical data fields; only the three proof fields
  -- differ, and those are propositions.
  change (⟨A.mol, A.centers, A.ligandAtom, A.ligandAtom_adj, A.ligandAtom_injective,
      A.ligandAtom_surjective⟩ : MultiCenterMolecule V) =
    ⟨mol₁, centers₁,
      (fun (c : V) (hc : c ∈ centers₁) (i : Fin 4) => ligand₁ c hc (σ c hc i)),
      adj₂, inj₂, surj₂⟩
  have h1 : A.ligandAtom_adj = adj₂ := Subsingleton.elim _ _
  have h2 : A.ligandAtom_injective = inj₂ := Subsingleton.elim _ _
  have h3 : A.ligandAtom_surjective = surj₂ := Subsingleton.elim _ _
  rw [h1, h2, h3]
  -- The data fields of `A` are definitionally the fields of `m₁` at `σ`, since `reindexFrames`
  -- keeps `mol` and `centers` and post-composes the ligand enumeration.
  rfl

end MultiCenterMolecule

/-! ## The detected-molecule specialization -/

namespace CertifiedLocalizedCIPInput

open TetraStereo.OneCenter

/-- **Enumeration adapter at the automatically detected molecule.**  Any multi-center molecule on
the certified atoms with the certified graph and the detected candidate set differs from
`input.detectedMultiCenterMolecule` by a per-center ligand reindexing.  Both structural hypotheses
hold definitionally for the detected molecule itself. -/
theorem exists_reindexFrames_detectedMultiCenterMolecule
    (input : CertifiedLocalizedCIPInput)
    {m : MultiCenterMolecule input.Atom}
    (hmol : m.mol = input.moleculeGraph)
    (hcenters : m.centers = input.tetrahedralCenterSet) :
    ∃ τ : m.Center → Equiv.Perm (Fin 4),
      m.reindexFrames τ = input.detectedMultiCenterMolecule :=
  MultiCenterMolecule.exists_reindexFrames_eq_of_mol_centers_eq
    (m₁ := m) (m₂ := input.detectedMultiCenterMolecule)
    (hmol.trans (input.detectedMultiCenter_mol).symm)
    (hcenters.trans (input.detectedMultiCenter_centers).symm)











theorem actualPhysicalGeneralRigidCalibratedCenter_reindexFrames
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (τ : m.Center → Equiv.Perm (Fin 4))
    (center : m.Center)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input m cfg center) :
    ActualPhysicalGeneralRigidCalibratedCenter input (m.reindexFrames τ)
      (m.reindexConfiguration τ cfg) center := by
  classical
  obtain ⟨rigid, pointAt, observed, nonzero, signEq⟩ := calibrated
  refine ⟨?_, (fun i => pointAt (τ center i)), ?_, ?_, ?_⟩
  · -- Constitutional rigidity conjugates across the reindexing.
    intro e' hcenter'
    let e : m.Aut := m.autUnreindex τ e'
    have heq : m.autReindex τ e = e' := m.autReindex_autUnreindex τ e'
    have hcenter : m.centerPerm e center = center := by
      have h := hcenter'
      rw [← heq] at h
      rwa [← MultiCenterMolecule.reindexFrames_centerPerm m τ e center]
    have hlig : m.ligandPermAt e center = 1 := rigid e hcenter
    have hconj := MultiCenterMolecule.reindexFrames_ligandPermAt m τ e center
    rw [hlig, heq, hcenter'] at hconj
    simpa using hconj
  · -- The actual spatial reads are the reindexed points.
    intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed (τ center i)
  · -- Nonzero oriented volume is alternating.
    exact cartesianOrientedVolume_perm_ne_zero pointAt (τ center) nonzero
  · -- The physical sign equation at the reindexed configuration.
    have hvec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) k = pointAt k := by
      intro k
      fin_cases k <;> rfl
    have hperm : RationalTetrahedralPermutation.permutedOrientedVolume
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) (τ center) =
        CartesianPoint3.orientedVolume
          (pointAt (τ center 0)) (pointAt (τ center 1))
            (pointAt (τ center 2)) (pointAt (τ center 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
    rw [← hperm, rationalVolumeSign_permutedOrientedVolume, signEq,
      MultiCenterMolecule.configurationSign_reindexConfiguration m τ cfg center]







theorem actualGeneralRigidPhysicalDomain_reindexFrames
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (τ : m.Center → Equiv.Perm (Fin 4))
    (domain : ActualGeneralRigidPhysicalDomain input m cfg root) :
    ActualGeneralRigidPhysicalDomain input (m.reindexFrames τ)
      (m.reindexConfiguration τ cfg) root := by
  refine ⟨?_, ?_⟩
  · simpa using domain.graphEq
  · intro center center_ne_root
    rcases domain.centerCase center center_ne_root with twin | calibrated
    · exact Or.inl
        (actualPhysicalTerminalTwinCenter_congr_mol
          (m₁ := m) (m₂ := m.reindexFrames τ) (c₁ := center) (c₂ := center)
          (MultiCenterMolecule.reindexFrames_mol m τ).symm rfl twin)
    · exact Or.inr
        (actualPhysicalGeneralRigidCalibratedCenter_reindexFrames input m cfg τ center
          calibrated)








theorem exists_reindexed_detectedPhysicalDomain
    (input : CertifiedLocalizedCIPInput)
    {m : MultiCenterMolecule input.Atom}
    (cfg : m.Configuration)
    (root : m.Center)
    (hmol : m.mol = input.moleculeGraph)
    (hcenters : m.centers = input.tetrahedralCenterSet)
    (domain : ActualGeneralRigidPhysicalDomain input m cfg root) :
    ∃ (τ : m.Center → Equiv.Perm (Fin 4))
      (cfg' : (m.reindexFrames τ).Configuration),
      m.reindexFrames τ = input.detectedMultiCenterMolecule ∧
        ActualGeneralRigidPhysicalDomain input (m.reindexFrames τ) cfg' root := by
  obtain ⟨τ, hτ⟩ := input.exists_reindexFrames_detectedMultiCenterMolecule hmol hcenters
  exact ⟨τ, m.reindexConfiguration τ cfg, hτ,
    actualGeneralRigidPhysicalDomain_reindexFrames input m cfg root τ domain⟩










theorem actualGeneralRigidPhysicalDomain_of_globalPhysicalCalibratedDomain
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input m cfg root) :
    ActualGeneralRigidPhysicalDomain input m cfg root := by
  refine ⟨domain.graphEq, ?_⟩
  intro center center_ne_root
  rcases domain.centerCase center center_ne_root with twin | calibrated
  · exact Or.inl twin
  · obtain ⟨pointAt, zInjective, observed, nonzero, signEq⟩ := calibrated
    exact Or.inr
      ⟨constitutionallyRigid_of_ligandAtomZ_injective zInjective,
        pointAt, observed, nonzero, signEq⟩

end CertifiedLocalizedCIPInput

end

end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.exists_reindexFrames_eq_of_mol_centers_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_reindexFrames_detectedMultiCenterMolecule
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalGeneralRigidCalibratedCenter_reindexFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidPhysicalDomain_reindexFrames
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_reindexed_detectedPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualGeneralRigidPhysicalDomain_of_globalPhysicalCalibratedDomain
