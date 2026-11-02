import TetraStereo.OneCenter.ChronologicalPhysicalTree
import TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
import TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.ChronologicalRawAdmissionRecoveryProofs.ChronologicalRawAdmissionRecovery
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords























/-! ## The fresh append preserves the accepted domain -/

/-- The projected target inventory of one append: the old target list with the fresh target
`mol.atomCount` appended.  This is the actual image of the written bond list, not a supplied field. -/
theorem appendFreshChild_bonds_map_target (mol : RawMolecule) (parent : Fin mol.atomCount)
    (child : AtomSpec) :
    (appendFreshChild mol parent child).bonds.map RawBond.target =
      mol.bonds.map RawBond.target ++ [mol.atomCount] := by
  rw [appendFreshChild_bonds, List.map_append]
  simp [freshBond]

/-- The genuine chronological append preserves exactly the kernel-accepted shared predicate
`RawMolecule.ChronologicalPhysicalTree`.  The only inputs are the old domain, a real parent index
`parent < mol.atomCount` and a fresh `AtomSpec`; the fresh single bond and its forward orientation
come from the actual constructor `freshBond`. -/
theorem appendFreshChild_chronologicalPhysicalTree (mol : RawMolecule)
    (parent : Fin mol.atomCount) (child : AtomSpec)
    (h : mol.ChronologicalPhysicalTree) :
    (appendFreshChild mol parent child).ChronologicalPhysicalTree := by
  obtain ⟨hpos, hbonds, hnodup, hcover⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [appendFreshChild_atomCount]; omega
  · intro bond hmem
    rw [appendFreshChild_bonds] at hmem
    rcases List.mem_append.mp hmem with hold | hfresh
    · obtain ⟨hk, hst, hlt⟩ := hbonds bond hold
      exact ⟨hk, hst, by rw [appendFreshChild_atomCount]; omega⟩
    · rw [List.mem_singleton] at hfresh
      subst hfresh
      refine ⟨?_, ?_, ?_⟩
      · show (freshBond mol parent).kind = ParsedBondKind.single; rfl
      · show parent.val < mol.atomCount; exact parent.isLt
      · rw [appendFreshChild_atomCount]
        show mol.atomCount < mol.atomCount + 1
        exact Nat.lt_succ_self _
  · rw [appendFreshChild_bonds_map_target]
    refine List.nodup_append.mpr ⟨hnodup, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    obtain ⟨bond, hmem, rfl⟩ := List.mem_map.mp ha
    have hlt := (hbonds bond hmem).2.2
    omega
  · intro atom hgt hlt
    rw [appendFreshChild_atomCount] at hlt
    rw [appendFreshChild_bonds_map_target]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hsmall | heq
    · exact List.mem_append_left _ (hcover atom hgt hsmall)
    · subst heq
      exact List.mem_append_right _ (by simp)

/-! ## The initial `[H]` cap inhabits the domain -/


theorem family543Base_chronologicalPhysicalTree :
    family543Base.ChronologicalPhysicalTree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [family543Base, RawMolecule.atomCount]
  · intro bond hmem; simp [family543Base] at hmem
  · simp [family543Base]
  · intro atom hgt hlt
    change atom < 1 at hlt
    omega

/-! ## The frozen physical constructors preserve the domain -/

/-- The twelve-append parity block preserves the shared predicate from an arbitrary parent domain. -/
theorem blockAppend_chronologicalPhysicalTree (mol : RawMolecule) (base : ℕ)
    (hbase : mol.atomCount = base) (externalParent : Fin mol.atomCount)
    (parity : TetrahedralInputParity) (h : mol.ChronologicalPhysicalTree) :
    (blockAppend mol base hbase externalParent parity).ChronologicalPhysicalTree := by
  unfold blockAppend
  dsimp only
  repeat (first | apply appendFreshChild_chronologicalPhysicalTree)
  exact h

/-- The whole `n`-block fold preserves the shared predicate from an arbitrary parent domain. -/
theorem blocksResult543_chronologicalPhysicalTree (ps : List TetrahedralInputParity)
    (mol : RawMolecule) (parent : Fin mol.atomCount) (h : mol.ChronologicalPhysicalTree) :
    (blocksResult543 ps mol parent).ChronologicalPhysicalTree := by
  induction ps generalizing mol parent with
  | nil => exact h
  | cons parity rest ih =>
      simp only [blocksResult543]
      exact ih (blockAppend mol mol.atomCount rfl parent parity)
        ⟨mol.atomCount, by rw [blockAppend_atomCount]; omega⟩
        (blockAppend_chronologicalPhysicalTree mol mol.atomCount rfl parent parity h)

/-! ## The arbitrary second-sphere family inhabits the domain -/

/-- The arbitrary second-sphere family — initial `[H]` cap, `n` twelve-append parity blocks, final
`[H]` cap — satisfies exactly the kernel-accepted predicate, for every parity list.  No size is
fixed, no parity is privileged, and the domain is derived from the physical construction. -/
theorem familyRaw_chronologicalPhysicalTree (ps : List TetrahedralInputParity) :
    (familyRaw ps).ChronologicalPhysicalTree := by
  unfold familyRaw
  dsimp only
  apply appendFreshChild_chronologicalPhysicalTree
  exact blocksResult543_chronologicalPhysicalTree ps family543Base baseFin
    family543Base_chronologicalPhysicalTree

/-- The empty parity list instantiates the `H-H` capped molecule, provided by the initial and final
`[H]` cap constructors alone. -/
theorem familyRaw_empty_chronologicalPhysicalTree :
    (familyRaw []).ChronologicalPhysicalTree :=
  familyRaw_chronologicalPhysicalTree []

/-- Every family whose first block carries an anticlockwise tag inhabits the domain, for an
arbitrary trailing parity list. -/
theorem familyRaw_anticlockwise_chronologicalPhysicalTree
    (ps : List TetrahedralInputParity) :
    (familyRaw (TetrahedralInputParity.anticlockwise :: ps)).ChronologicalPhysicalTree :=
  familyRaw_chronologicalPhysicalTree _

/-- Every family whose first block carries a clockwise tag inhabits the domain, for an arbitrary
trailing parity list. -/
theorem familyRaw_clockwise_chronologicalPhysicalTree
    (ps : List TetrahedralInputParity) :
    (familyRaw (TetrahedralInputParity.clockwise :: ps)).ChronologicalPhysicalTree :=
  familyRaw_chronologicalPhysicalTree _

end TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
