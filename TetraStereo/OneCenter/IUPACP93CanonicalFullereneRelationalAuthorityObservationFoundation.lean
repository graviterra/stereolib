import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthoritySourceAudit

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0









namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

def iupacP93CanonicalFullereneC76Type1AuthorityObservation :
    P93RelationalFullereneHandedAuthorityObservation
      iupacP93CanonicalFullereneRelationalAuthorityPolicy where
  base :=
    { molecule := iupacP93CanonicalFullereneC76Type1Molecule
      spatial? := none
      inputs := [iupacP93CanonicalFullereneC76Type1RelationalSourceInput]
      selectedInput := iupacP93CanonicalFullereneC76Type1RelationalSourceInput
      addends := iupacP93CanonicalFullereneC76Type1RelationalInput.evidence.addends
      chiralAddends :=
        iupacP93CanonicalFullereneC76Type1RelationalInput.evidence.chiralAddends
      assignment := iupacP93CanonicalFullereneC76Type1LocalAssignment
      substituentAssignments := [] }
  numberingKind := .systematic
  handedness := .C

def iupacP93CanonicalFullereneC60Type2AuthorityObservation :
    P93RelationalFullereneHandedAuthorityObservation
      iupacP93CanonicalFullereneRelationalAuthorityPolicy where
  base :=
    { molecule := iupacP93CanonicalFullereneC60Type2Molecule
      spatial? := none
      inputs := [iupacP93CanonicalFullereneC60Type2RelationalSourceInput]
      selectedInput := iupacP93CanonicalFullereneC60Type2RelationalSourceInput
      addends := iupacP93CanonicalFullereneC60Type2RelationalInput.evidence.addends
      chiralAddends :=
        iupacP93CanonicalFullereneC60Type2RelationalInput.evidence.chiralAddends
      assignment := iupacP93CanonicalFullereneC60Type2LocalAssignment
      substituentAssignments := [] }
  numberingKind := .systematic
  handedness := .C

def iupacP93CanonicalFullereneC60Type3AuthorityObservation :
    P93RelationalFullereneHandedAuthorityObservation
      iupacP93CanonicalFullereneRelationalAuthorityPolicy where
  base :=
    { molecule := iupacP93CanonicalFullereneC60Type3Molecule
      spatial? := none
      inputs := [iupacP93CanonicalFullereneC60Type3RelationalSourceInput]
      selectedInput := iupacP93CanonicalFullereneC60Type3RelationalSourceInput
      addends := iupacP93CanonicalFullereneC60Type3RelationalInput.evidence.addends
      chiralAddends :=
        iupacP93CanonicalFullereneC60Type3RelationalInput.evidence.chiralAddends
      assignment := iupacP93CanonicalFullereneC60Type3LocalAssignment
      substituentAssignments := [] }
  numberingKind := .systematic
  handedness := .C

def iupacP93CanonicalFullereneC70Type4AuthorityObservation :
    P93RelationalFullereneType4AuthorityObservation
      iupacP93CanonicalFullereneRelationalAuthorityPolicy where
  molecule := iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
  spatial? := none
  input := iupacP93CanonicalFullereneC70Type4RelationalInput
  assignment := iupacP93CanonicalFullereneC70Type4LocalAssignment
  substituentAssignments := iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments

def iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation :
    P93RelationalFullereneSuperimposedAuthorityObservation
      iupacP93CanonicalFullereneRelationalAuthorityPolicy where
  handed :=
    { base :=
        { molecule := iupacP93CanonicalFullereneC70SuperimposedMolecule
          spatial? := none
          inputs := [iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]
          selectedInput := iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput
          addends := iupacP93CanonicalFullereneC70SuperimposedRelationalInput.evidence.addends
          chiralAddends :=
            iupacP93CanonicalFullereneC70SuperimposedRelationalInput.evidence.chiralAddends
          assignment := iupacP93CanonicalFullereneC70SuperimposedLocalAssignment
          substituentAssignments :=
            iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments }
      numberingKind := .systematic
      handedness := .C }

theorem p93AuthorityBinaryBond_of_nonCageRawBond
    (molecule : RawMolecule) (carrier : Finset Nat)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.MolecularFullereneTopologyRepresentationAgreement
      carrier none source)
    (bond : RawBond) (bondPresent : bond ∈ molecule.bonds)
    (notInternal : ¬(bond.source ∈ carrier ∧ bond.target ∈ carrier))
    (distinct : bond.source ≠ bond.target) :
    P93AuthorityBinaryBond source bond.source bond.target := by
  refine ⟨distinct, bond.toSemanticInteraction, ?_, ?_, Or.inl ?_⟩
  · exact molecule.toMolecularFullereneTopologySemanticMolecule?_nonCageBondExact
      carrier source.molecule agreement.1 bond bondPresent notInternal
  · rcases bond with ⟨bondSource, bondTarget, bondKind⟩
    cases bondKind <;> trivial
  · simp [RawBond.toSemanticInteraction]

theorem rawBond_exact_of_bondOrder_positive
    (molecule : RawMolecule) (carrier : Finset Nat) (center neighbor : Nat)
    (distinct : center ≠ neighbor) (centerOutside : center ∉ carrier)
    (positive : 0 < molecule.bondOrder center neighbor) :
    ∃ bond : RawBond, bond ∈ molecule.bonds ∧
      ((bond.source = center ∧ bond.target = neighbor) ∨
        (bond.source = neighbor ∧ bond.target = center)) ∧
      ¬(bond.source ∈ carrier ∧ bond.target ∈ carrier) ∧
      bond.source ≠ bond.target := by
  obtain ⟨bond, bondPresent, connects⟩ :=
    (molecule.bondOrder_pos_iff_exists_bond distinct).mp positive
  have endpoints :
      (bond.source = center ∧ bond.target = neighbor) ∨
        (bond.source = neighbor ∧ bond.target = center) := by
    simpa [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] using connects
  refine ⟨bond, bondPresent, endpoints, ?_, ?_⟩
  · rintro ⟨sourceInternal, targetInternal⟩
    rcases endpoints with ⟨sourceEq, _⟩ | ⟨_, targetEq⟩
    · exact centerOutside (sourceEq ▸ sourceInternal)
    · exact centerOutside (targetEq ▸ targetInternal)
  · rcases endpoints with ⟨sourceEq, targetEq⟩ | ⟨sourceEq, targetEq⟩
    · simpa [sourceEq, targetEq] using distinct
    · simpa [sourceEq, targetEq] using distinct.symm

theorem p93AuthorityAtomCenterValid_of_rawNeighbors
    (molecule : RawMolecule) (carrier : Finset Nat)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.MolecularFullereneTopologyRepresentationAgreement
      carrier none source)
    (center : Nat) (neighbors : List Nat)
    (centerBound : center < molecule.atomCount)
    (three : 3 ≤ neighbors.length) (nodup : neighbors.Nodup)
    (neighborsBound : ∀ neighbor ∈ neighbors, neighbor < molecule.atomCount)
    (rawBonds : ∀ neighbor ∈ neighbors,
      ∃ bond : RawBond, bond ∈ molecule.bonds ∧
        ((bond.source = center ∧ bond.target = neighbor) ∨
          (bond.source = neighbor ∧ bond.target = center)) ∧
        ¬(bond.source ∈ carrier ∧ bond.target ∈ carrier) ∧
        bond.source ≠ bond.target) :
    (P93AuthorityPhysicalUnit.atomCenter center).ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy source := by
  have countExact :=
    molecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
      carrier source.molecule agreement.1
  refine ⟨by simpa [countExact] using centerBound, neighbors, three, nodup, ?_, ?_⟩
  · intro neighbor neighborPresent
    simpa [P93AuthorityAtomsBounded, countExact] using
      neighborsBound neighbor neighborPresent
  · intro neighbor neighborPresent
    left
    obtain ⟨bond, bondPresent, endpoints, notInternal, distinct⟩ :=
      rawBonds neighbor neighborPresent
    have binary := p93AuthorityBinaryBond_of_nonCageRawBond molecule carrier source agreement bond
      bondPresent notInternal distinct
    rcases endpoints with ⟨sourceEq, targetEq⟩ | ⟨sourceEq, targetEq⟩
    · simpa [sourceEq, targetEq] using binary
    · refine ⟨by simpa [sourceEq, targetEq] using distinct.symm, ?_⟩
      obtain ⟨interaction, interactionPresent, kind, participants⟩ := binary.2
      refine ⟨interaction, interactionPresent, kind, ?_⟩
      rcases participants with participants | participants
      · exact Or.inr (by simpa [sourceEq, targetEq] using participants)
      · exact Or.inl (by simpa [sourceEq, targetEq] using participants)


private theorem iupacP93CanonicalFullereneC70Type4SecondPlacement_attachmentSites :
    iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced.attachmentSites = {15, 34} := by
  simpa [iupacP93CanonicalFullereneC70Type4SecondPlacement] using
    (compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
      (core := iupacP93CanonicalFullereneC70Transcription.cageMolecule)
      (carrier := iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier)
      rfl { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {15, 34} }
      (iupacP93CanonicalFullereneC70Type4Placements_audited.2.2.1 _ (by
        simp [iupacP93CanonicalFullereneC70Type4Placements])) (by decide))

private theorem iupacP93CanonicalFullereneC70SuperimposedPlacement_attachmentSites :
    iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced.attachmentSites = {7, 24} ∧
      iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced.attachmentSites =
        {32, 33} := by
  exact ⟨
    by simpa [iupacP93CanonicalFullereneC70SuperimposedFirstPlacement] using
      (compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
        (core := iupacP93CanonicalFullereneC70Transcription.cageMolecule)
        (carrier := iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier)
        rfl { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {7, 24} }
        (iupacP93CanonicalFullereneC70SuperimposedPlacements_audited.2.2.1 _ (by
          simp [iupacP93CanonicalFullereneC70SuperimposedPlacements])) (by decide)),
    by simpa [iupacP93CanonicalFullereneC70SuperimposedSecondPlacement] using
      (compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
        (core := iupacP93CanonicalFullereneC70Transcription.cageMolecule)
        (carrier := iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier)
        rfl { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {32, 33} }
        (iupacP93CanonicalFullereneC70SuperimposedPlacements_audited.2.2.1 _ (by
          simp [iupacP93CanonicalFullereneC70SuperimposedPlacements])) (by decide))⟩

private theorem iupacP93CanonicalFullereneC70Type4AttachmentBond_positive :
    0 < iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 15 97 := by
  have port : (15, 97) ∈
      (iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
        iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced).attachmentPorts := by
    have sitePresent : 15 ∈
        iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced.attachmentSites := by
      rw [iupacP93CanonicalFullereneC70Type4SecondPlacement_attachmentSites]
      simp
    obtain ⟨portIndex, _, siteEq⟩ := Finset.mem_image.mp sitePresent
    simp only [MolecularFullereneAddendTemplateAssembly.compiledPlacedAddend]
    refine Finset.mem_image.mpr ⟨portIndex, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact siteEq
    · have portRoot :=
        iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate_constitution
          |>.2.2.2.2.2 portIndex |>.1
      have portRoot' :
          ((iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced.template.port
            portIndex).externalAtom : Nat) = 0 := by
        simpa [iupacP93CanonicalFullereneC70Type4SecondPlacement] using portRoot
      simp only [molecularFullereneRemapLocalAtom]
      rw [portRoot']
      change 70 + 27 = 97
      decide
  exact (MolecularFullereneAddend.validFor_port_exact
      (iupacP93CanonicalFullereneC70Type4RelationalEvidence.addendsValid
        (iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
          iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced) (by
            change _ ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends
            rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]
            simp))
      15 97).1 port |>.2.2

private theorem iupacP93CanonicalFullereneC70SuperimposedAttachmentBond_zero :
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 15 97 = 0 := by
  by_contra nonzero
  have positive : 0 < iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 15 97 :=
    Nat.pos_of_ne_zero nonzero
  obtain ⟨addend, addendPresent, port⟩ :=
    (iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence.attachmentPortsPartition
      15 97 (by decide) (by decide) (by decide)).1 positive
  change addend ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends at addendPresent
  rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2] at addendPresent
  simp only [List.mem_cons, List.not_mem_nil, or_false] at addendPresent
  rcases addendPresent with rfl | rfl
  · simp only [MolecularFullereneAddendTemplateAssembly.compiledPlacedAddend] at port
    obtain ⟨portIndex, _, portEq⟩ := Finset.mem_image.mp port
    have siteEq := congrArg Prod.fst portEq
    have sitePresent' : 15 ∈
        iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced.attachmentSites := by
      refine Finset.mem_image.mpr ⟨portIndex, Finset.mem_univ _, ?_⟩
      simpa using siteEq
    rw [iupacP93CanonicalFullereneC70SuperimposedPlacement_attachmentSites.1] at sitePresent'
    simp at sitePresent'
  · simp only [MolecularFullereneAddendTemplateAssembly.compiledPlacedAddend] at port
    obtain ⟨portIndex, _, portEq⟩ := Finset.mem_image.mp port
    have siteEq := congrArg Prod.fst portEq
    have sitePresent' : 15 ∈
        iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced.attachmentSites := by
      refine Finset.mem_image.mpr ⟨portIndex, Finset.mem_univ _, ?_⟩
      simpa using siteEq
    rw [iupacP93CanonicalFullereneC70SuperimposedPlacement_attachmentSites.2] at sitePresent'
    simp at sitePresent'

theorem iupacP93CanonicalFullereneC70Type4Molecule_ne_superimposed :
    iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble ≠
      iupacP93CanonicalFullereneC70SuperimposedMolecule := by
  intro equal
  have orderEq := congrArg (fun molecule : RawMolecule => molecule.bondOrder 15 97) equal
  change _ = iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 15 97 at orderEq
  rw [iupacP93CanonicalFullereneC70SuperimposedAttachmentBond_zero] at orderEq
  exact Nat.ne_of_gt iupacP93CanonicalFullereneC70Type4AttachmentBond_positive orderEq


end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
