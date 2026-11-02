import TetraStereo.OneCenter.LocalizedAxialChainPerception

set_option autoImplicit false

namespace TetraStereo.Examples.LocalizedAxialRootPerceptionRegression

open OneCenter

private def carbon : PeriodicElement :=
  { atomicNumber := 6, positive := by decide, atMost118 := by decide }

/-- A constitution with an axial candidate but no four-neighbour tetrahedral carrier root. -/
private def alleneInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [{ element := carbon }, { element := carbon }, { element := carbon }]
        interactions :=
          [{ participants := [0, 1], kind := .covalent 2 },
           { participants := [1, 2], kind := .covalent 2 }] } }

private def certifiedAllene : CertifiedAuthoritativeChemicalInput :=
  { input := alleneInput
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff alleneInput).mp
        (by decide) }

private def localizedAllene : CertifiedLocalizedCIPInput :=
  { certified := certifiedAllene
    graphReady :=
      (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff
        certifiedAllene.input.molecule).mp (by decide) }

private def atom0 : localizedAllene.Atom := ⟨0, by decide⟩
private def atom1 : localizedAllene.Atom := ⟨1, by decide⟩
private def atom2 : localizedAllene.Atom := ⟨2, by decide⟩

private def leftRoot : localizedAllene.LocalizedAxialRootCandidate :=
  { terminal := atom0, firstAxis := atom1 }

private def rightRoot : localizedAllene.LocalizedAxialRootCandidate :=
  { terminal := atom2, firstAxis := atom1 }

private theorem leftRoot_declarative :
    localizedAllene.DeclarativeLocalizedAxialRootCandidate leftRoot := by
  constructor
  · rfl
  · intro neighbor doubleBond
    fin_cases neighbor <;> simp_all [CertifiedLocalizedCIPInput.moleculeGraph,
      SemanticMolecule.toLocalizedMoleculeGraph, SemanticMolecule.localizedBondOrder,
      SemanticMolecule.localizedBondOrderAtKey, SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, semanticEdgeKey,
      SemanticMolecule.atomCount, localizedAllene, certifiedAllene, alleneInput,
      atom0, atom1, leftRoot]

private theorem rightRoot_declarative :
    localizedAllene.DeclarativeLocalizedAxialRootCandidate rightRoot := by
  constructor
  · rfl
  · intro neighbor doubleBond
    fin_cases neighbor <;> simp_all [CertifiedLocalizedCIPInput.moleculeGraph,
      SemanticMolecule.toLocalizedMoleculeGraph, SemanticMolecule.localizedBondOrder,
      SemanticMolecule.localizedBondOrderAtKey, SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, semanticEdgeKey,
      SemanticMolecule.atomCount, localizedAllene, certifiedAllene, alleneInput,
      atom1, atom2, rightRoot]

/-- The fixture has no four-neighbour atom from which the older localized carrier could start. -/
theorem allene_has_no_tetrahedral_carrier_root
    (atom : localizedAllene.Atom) :
    atom ∉ localizedAllene.tetrahedralCenterSet := by
  fin_cases atom <;> decide

/-- Both terminal starts are discovered even though no tetrahedral root was supplied. -/
theorem allene_terminal_axial_roots_are_discovered :
    leftRoot ∈ localizedAllene.localizedAxialRootCandidates ∧
      rightRoot ∈ localizedAllene.localizedAxialRootCandidates := by
  exact ⟨
    (localizedAllene.mem_localizedAxialRootCandidates_iff leftRoot).mpr
      leftRoot_declarative,
    (localizedAllene.mem_localizedAxialRootCandidates_iff rightRoot).mpr
      rightRoot_declarative⟩

#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialRootCandidateAt?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialRootCandidateAt?_complete
#check OneCenter.CertifiedLocalizedCIPInput.mem_localizedAxialRootCandidates_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialRootCandidates_nodup
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialChainWalk?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedAxialChainWalk?_complete_of_length
#check OneCenter.CertifiedLocalizedCIPInput.DeclarativeLocalizedAxialChainFromRoot.path_nodup
#check OneCenter.CertifiedLocalizedCIPInput.localizedEvenAxialChainFromRoot?_sound
#check OneCenter.CertifiedLocalizedCIPInput.localizedEvenAxialChainFromRoot?_complete
#check OneCenter.CertifiedLocalizedCIPInput.mem_localizedEvenAxialChains_iff
#check OneCenter.CertifiedLocalizedCIPInput.localizedEvenAxialChains_nodup

end TetraStereo.Examples.LocalizedAxialRootPerceptionRegression
