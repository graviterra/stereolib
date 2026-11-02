import TetraStereo.OneCenter.CIPAuthoritativeBranchDiscoveryTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open ProductionCIPOccurrenceDiscovery
open AuthoritativeCIPMancudeTotality

namespace AuthoritativeCIPDiscovery

/-!
# Molecule-wide totality of authoritative CIP discovery

`CIPAuthoritativeBranchDiscoveryTotality` proves that every molecule-derived physical or lone-pair
slot compiles to a complete width-unbounded key on the independently stated finite chemical
domain.  This module lifts that pointwise theorem through the actual executable constructors:
`CompleteBranchDiscovery.discover?`, `discoverCenter?`, and finally `discoverAll?`.
-/

namespace CompleteBranchDiscovery

/-- The executable proof-carrying branch discovery returns on every molecule-derived slot in the
chemical applicability domain. -/
theorem discover?_exists_of_chemical_applicability
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol)
    (root : Root mol) (slot : Fin 4) :
    ∃ discovery,
      discover? mol (centerAtom root) (ligandAtom root slot) = some discovery := by
  obtain ⟨key, accepted, complete⟩ :=
    RawMolecule.branchCanonicalKeyAuthoritative?_exists_complete_of_chemical_applicability
      mol wellFormed unique writtenExact valence kekule root slot
  let discovery : CompleteBranchDiscovery mol (centerAtom root) (ligandAtom root slot) :=
    { key := key, accepted := accepted, complete := complete }
  exact ⟨discovery, discover?_eq_some discovery⟩

end CompleteBranchDiscovery

/-- All four authoritative branches of a molecule-derived final center succeed on the chemical
applicability domain. -/
theorem centerBranchesSucceeded_of_chemical_applicability
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol)
    (root : Root mol) :
    centerBranchesSucceeded? mol root = true := by
  unfold centerBranchesSucceeded?
  rw [List.all_eq_true]
  intro slot _slotMember
  obtain ⟨discovery, discovered⟩ :=
    CompleteBranchDiscovery.discover?_exists_of_chemical_applicability
      mol wellFormed unique writtenExact valence kekule root slot
  rw [discovered]
  rfl

/-- The actual four-slot center discovery returns a proof-carrying center witness. -/
theorem discoverCenter?_exists_of_chemical_applicability
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol)
    (root : Root mol) :
    ∃ discovery, discoverCenter? mol root = some discovery := by
  have succeeded := centerBranchesSucceeded_of_chemical_applicability
    mol wellFormed unique writtenExact valence kekule root
  have isSome : (discoverCenter? mol root).isSome = true := by
    rw [discoverCenter?_isSome, succeeded]
  cases discovered : discoverCenter? mol root with
  | none => simp [discovered] at isSome
  | some discovery => exact ⟨discovery, rfl⟩

/-- Every molecule-derived eligible center succeeds, including the vacuous molecule with no such
centers. -/
theorem allCentersSucceeded_of_chemical_applicability
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol) :
    allCentersSucceeded? mol = true := by
  unfold allCentersSucceeded?
  rw [List.all_eq_true]
  intro root _rootMember
  obtain ⟨discovery, discovered⟩ := discoverCenter?_exists_of_chemical_applicability
    mol wellFormed unique writtenExact valence kekule root
  rw [discovered]
  rfl

/-- Molecule-wide authoritative discovery returns on the full finite chemical applicability
domain. -/
theorem discoverAll?_exists_of_chemical_applicability
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol) :
    ∃ discovery, discoverAll? mol = some discovery := by
  have succeeded := allCentersSucceeded_of_chemical_applicability
    mol wellFormed unique writtenExact valence kekule
  have isSome : (discoverAll? mol).isSome = true := by
    rw [discoverAll?_isSome, succeeded]
  cases discovered : discoverAll? mol with
  | none => simp [discovered] at isSome
  | some discovery => exact ⟨discovery, rfl⟩

/-- The successful executable molecule discovery comes with the independent faithful molecular
digraph and exact Rules-1a--2 constitutional hierarchy conformance for every eligible center and
every ordered pair of physical ligands. -/
theorem discoverAll?_exists_exactConstitutionalMoleculeConformance_of_chemical_applicability
    (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (kekule : LocalizedMancudeKekuleAdmissible mol)
    (known : mol.Rule2MassesKnown) :
    ∃ discovery,
      discoverAll? mol = some discovery ∧
        BlueBookP92.Digraph.AuthoritativeExactConstitutionalMoleculeConformance mol discovery := by
  obtain ⟨discovery, discovered⟩ := discoverAll?_exists_of_chemical_applicability
    mol wellFormed unique writtenExact valence kekule
  refine ⟨discovery, discovered, ?_⟩
  exact discovery.exactConstitutionalMoleculeConformance_of_stereochemicalAdmissible
    ⟨⟨wellFormed, unique⟩, writtenExact⟩ known

end AuthoritativeCIPDiscovery

end

end TetraStereo.OneCenter
