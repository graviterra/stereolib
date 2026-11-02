import TetraStereo.OneCenter.CIPAuthoritativeBranchDiscoveryTotality
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open AuthoritativeCIPCursorSupport
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPMancudeTotality

namespace RawMolecule

/-!
# Authoritative P-92 branch totality at an arbitrary physical edge

The width-unbounded authoritative branch compiler is total at every distinct positive physical
edge of a raw molecule on its existing chemical domain.  Unlike the occurrence-level totality
theorem, this result does not require a tetrahedral `FinalUnit`, a four-slot ligand frame, or exact
written-neighbour ordering: the center, ligand, and positive edge are supplied directly.

This is deliberately a raw-molecule theorem.  It does not construct a `RawMolecule` from an
`AuthoritativeChemicalInput` or `SemanticMolecule`, and it does not enumerate saturated-ring paths
or ring-closure duplicates.  Those representation and occurrence-enumeration boundaries remain
separate.
-/

/-- Every distinct positive physical edge has a complete width-unbounded authoritative branch
under the structural, valence, and mancude premises required by the lower generated-tree totality
theorem. -/
theorem branchCanonicalKeyAuthoritative?_exists_complete_of_physical_edge
    (mol : RawMolecule)
    (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique)
    (valence : mol.ValenceOK)
    (kekule : LocalizedMancudeKekuleAdmissible mol)
    (center ligand : Fin mol.atomCount)
    (distinct : ligand ≠ center)
    (positive : 0 < mol.bondOrder center.val ligand.val) :
    ∃ key,
      branchCanonicalKeyAuthoritative? mol center.val ligand.val = some key ∧
        key.complete = true := by
  have rootMember : canonicalRoot center.val ligand.val ∈
      mol.canonicalChildren (canonicalCenterRoot center.val) :=
    AuthoritativeCIPRule6Scheduler.canonicalRoot_mem_canonicalChildren_of_bondOrder_pos
      mol center.val ligand.val (fun equality => distinct (Fin.ext equality)) positive
  have bonding : CanonicalCenterBondingNumberSix mol center.val :=
    AuthoritativeCIPValenceBondingNumber.canonicalCenterBondingNumberSix_of_valence
      mol center.val center.isLt wellFormed unique valence
  have supported : MancudeRule1aSupported mol :=
    mancudeRule1aSupported_of_localizedKekuleAdmissible mol wellFormed unique kekule
  unfold branchCanonicalKeyAuthoritative?
  exact buildCanonicalBranchKeyAuthoritative_exists_complete_of_centerDescendant
    mol center.val center.isLt wellFormed bonding supported
    (2 * mol.atomCount + 2) (canonicalRoot center.val ligand.val)
    ⟨canonicalCenterRoot center.val, .root, rootMember⟩ (by
      simp [canonicalRoot]
      omega)

end RawMolecule

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.branchCanonicalKeyAuthoritative?_exists_complete_of_physical_edge
