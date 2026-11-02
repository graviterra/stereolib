import TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal

set_option autoImplicit false

/-!
# Actual frames from detected degree and existing source admission

Exact written-neighbor integrity is already part of StereochemicalAdmissible. Combined with
the actual raw molecular neighborhood and reached occurrence invariants, it constructs a frame
at every real occurrence of a detected degree-four atom, including in rings. Successful frame
construction is a conclusion. Malformed hand-written neighbor metadata is not admitted here.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedDetectedFrames

open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedCertifiedTerminalRefusal
open LocalizedGenericMarkedRecalculation (frameAtoms? frameAtomsOf)
open CertifiedLocalizedCIPInput

abbrev Node := RawMolecule.CanonicalBranchNode

theorem written_perm_incident (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (written : mol.WrittenNeighborExact)
    (atom : Fin mol.atomCount) :
    (mol.writtenNeighbors atom.val).Perm (mol.canonicalIncidentNeighbors atom.val) := by
  have facts := RawMolecule.WrittenNeighborExact.at mol written atom
  apply (List.perm_ext_iff_of_nodup facts.1
    (mol.canonicalIncidentNeighbors_nodup atom.val unique)).mpr
  intro other
  rw [mol.mem_canonicalIncidentNeighbors_iff atom.val wellFormed other]
  constructor
  · intro member
    exact (facts.2.2 ⟨other, facts.2.1 other member⟩).mp member
  · intro positive
    have valid := (mol.bondOrder_pos_endpoint_lt wellFormed positive).2
    exact (facts.2.2 ⟨other, valid⟩).mpr positive

theorem frame_of_degree_four (mol : RawMolecule) (wellFormed : mol.WellFormed)
    (single : SingleBonded mol) (unique : mol.BondRecordsUnique)
    (written : mol.WrittenNeighborExact) (node : Node) (reached : Reached mol node)
    (real : node.provenance = .realAtom)
    (four : (mol.canonicalIncidentNeighbors node.atom).length = 4) :
    occurrenceLigandFrame? mol node = some (occurrenceLigandCursors mol node) := by
  have notLeaf : node.forcedLeaf = false := by
    simp [RawMolecule.CanonicalBranchNode.forcedLeaf, real]
  have valid := reached_atom_valid mol wellFormed node reached
  have writtenFour : (mol.writtenNeighbors node.atom).length = 4 :=
    (written_perm_incident mol wellFormed unique written ⟨node.atom, valid⟩).length_eq.trans four
  have ligandsFour : (mol.ligandsWithLonePair node.atom).length = 4 := by
    cases atom : mol.atomAt? node.atom <;>
      simp [RawMolecule.ligandsWithLonePair, atom, writtenFour]
  have physicalFour : (occurrenceLigandCursors mol node).length = 4 := by
    have perm := occurrence_atoms_perm_neighbors mol wellFormed single node reached notLeaf
    simpa [frameAtomsOf] using perm.length_eq.trans four
  simp [occurrenceLigandFrame?, ligandsFour, physicalFour]

theorem detected_raw_degree (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (center : input.detectedMultiCenterMolecule.Center) :
    (mol.canonicalIncidentNeighbors center.1.val).length = 4 := by
  let index : Fin mol.atomCount := ⟨center.1.val, raw_atom_bound mol input agreement center.1⟩
  have indexEq : localizedIndexOf mol input agreement index = center.1 := Fin.ext rfl
  have perm := canonicalIncidentNeighbors_perm_sortedNeighborAtoms mol input agreement
    wellFormed unique supported index
  rw [indexEq] at perm
  have degree : (input.moleculeGraph.neighborFinset center.1).card = 4 :=
    (input.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card center.1).mp
      ((input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2)
  have length := perm.length_eq
  simpa [index, sortedNeighborAtoms, degree] using length

/-- Every reached real occurrence at an actually detected center has its literal runtime frame,
under the existing stereochemical source-intake contract. -/
theorem detected_frame (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (center : input.detectedMultiCenterMolecule.Center) (node : Node) (reached : Reached mol node)
    (real : node.provenance = .realAtom) (current : node.atom = center.1.val) :
    frameAtoms? mol node = some (frameAtomsOf (occurrenceLigandCursors mol node)) := by
  have wf := admissible.1.1
  have unique := admissible.1.2
  have degree := detected_raw_degree mol input agreement wf unique supported center
  have frame := frame_of_degree_four mol wf
    (raw_single mol input agreement wf unique supported single) unique admissible.2 node reached real
    (by simpa [current] using degree)
  simp [frameAtoms?, frame]

theorem detected_root_frame (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (root : input.detectedMultiCenterMolecule.Center) :
    frameAtoms? mol (canonicalCenterRoot root.1.val) =
      some (frameAtomsOf (occurrenceLigandCursors mol (canonicalCenterRoot root.1.val))) :=
  detected_frame mol input agreement admissible supported single root _
    (reached_root mol root.1.val (raw_atom_bound mol input agreement root.1)) rfl rfl

end TetraStereo.OneCenter.LocalizedMarkedDetectedFrames

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedFrames.written_perm_incident
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedFrames.frame_of_degree_four
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedFrames.detected_raw_degree
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedFrames.detected_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedFrames.detected_root_frame
