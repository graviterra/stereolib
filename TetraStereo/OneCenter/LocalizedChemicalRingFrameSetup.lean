import TetraStereo.OneCenter.LocalizedChemicalRingFrameReadback
import TetraStereo.KernelOnly
set_option autoImplicit false

/-! Actual paired frames at reached degree-four nodes, with no supplied execution data. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingFrameSetup
open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingLookupTransport LocalizedChemicalRingFrameReadback
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedOperations LocalizedMarkedRetainedStateReader
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedCertifiedTerminalRefusal
open LocalizedMarkedRetainedReachDegree LocalizedMarkedDetectedSnapshotSupport
open LocalizedGenericMarkedRecalculation (frameAtoms?)

variable (input : CertifiedLocalizedCIPInput)

structure Setup (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (node : RawMolecule.CanonicalBranchNode) (atoms atoms' : List Nat) where
  target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)
  found : lookup? input node = some target
  imageFound : lookup? input (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
    some (input.transportOccurrence single e target)
  real : target.1.node.provenance = .realAtom
  detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom
  imageReal : (input.transportOccurrence single e target).1.node.provenance = .realAtom
  imageDetected : IsDetectedCenter input.moleculeGraph
    (input.molecularFrameUnit (input.transportOccurrence single e target).1).atom
  center : input.TetrahedralCenter
  frames : input.ActualFrameSlotTransport single e target center
  sourceRead : Readback input atoms frames.sourceFrame
  imageRead : Readback input atoms' frames.imageFrame

theorem setup_exists (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms atoms' : List Nat) (raw : frameAtoms? mol node = some atoms)
    (raw' : frameAtoms? mol (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some atoms')
    (four : (mol.canonicalIncidentNeighbors node.atom).length = 4) :
    Nonempty (Setup input single e node atoms atoms') := by
  have wf := admissible.1.1
  have uq := admissible.1.2
  have rs := raw_single mol input agreement wf uq supported single
  have imageReach := reached_map sym wf uq rs node reached
  obtain ⟨root, bound, path⟩ := reached
  obtain ⟨target, found, _, corr⟩ := lookup?_exists_of_reachedFrom mol input agreement wf uq
    supported rs root bound node path
  have reached : Reached mol node := ⟨root, bound, path⟩
  have rawReal := LocalizedMarkedGeneratedSnapshotSupport.real_of_frame mol node atoms raw
  have real := lookup?_real input node target found rawReal
  have detected := carrier_detected_of_raw_degree mol input agreement wf uq supported rs target
    node (reached_atom_valid mol wf node reached) corr four
  let execution := rawStateFrames input single [] target real
    ⟨input.molecularFrameUnit target.1, detected⟩ rfl
  have meaning := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target execution.center).mp
    execution.centerComputed
  let frames := input.actualFrameSlotTransport single e (Nat.le_succ _) target execution.center meaning
  have imageFound := lookup_transport input mol agreement admissible supported single e sym node reached target found
  have imageRawReal := LocalizedMarkedGeneratedSnapshotSupport.real_of_frame mol _ atoms' raw'
  have imageReal := lookup?_real input _ _ imageFound imageRawReal
  have imageFour : (mol.canonicalIncidentNeighbors (relabelOf input (e : Equiv.Perm input.Atom) node.atom)).length = 4 := by
    simpa [four] using (neighbors_map sym wf uq node.atom).length_eq
  have imageDetected := carrier_detected_of_raw_degree mol input agreement wf uq supported rs _ _
    (reached_atom_valid mol wf _ imageReach) (lookup?_sound input _ _ imageFound) imageFour
  obtain ⟨sourceRead⟩ := readback_exists input mol agreement admissible supported single node reached
    target found real detected atoms raw frames.sourceFrame frames.sourceComputed
  obtain ⟨imageRead⟩ := readback_exists input mol agreement admissible supported single _ imageReach
    _ imageFound imageReal imageDetected atoms' raw' frames.imageFrame frames.imageComputed
  exact ⟨⟨target, found, imageFound, real, detected, imageReal, imageDetected, execution.center,
    frames, sourceRead, imageRead⟩⟩

/-- Three-coordinate raw frames have no certified tetrahedral frame. -/
theorem noFrame_of_three (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (three : (mol.canonicalIncidentNeighbors node.atom).length = 3)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target) :
    input.localizedNoDoubleFourLigandFrameExec? target = none := by
  obtain ⟨current, observed, degree⟩ := lookup_degree input mol agreement admissible supported
    node (reached_atom_valid mol admissible.1.1 node reached) target found
  exact frame_none_of_degree_ne_four input single target current
    ⟨lookup?_real input node target found
      (LocalizedMarkedGeneratedSnapshotSupport.real_of_frame mol node atoms raw), observed⟩ (by omega)

end TetraStereo.OneCenter.LocalizedChemicalRingFrameSetup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrameSetup.setup_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrameSetup.noFrame_of_three
