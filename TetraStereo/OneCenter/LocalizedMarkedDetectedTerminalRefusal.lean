import TetraStereo.OneCenter.LocalizedMarkedDetectedFrames

set_option autoImplicit false

/-!
# Detected physical terminal-twin refusal without frame-success premises

The actual root and target frames are constructed from the detected molecular inventory and
the existing stereochemical source-admission contract. An inherited reference is valid at the
target exactly when it is a physical neighbor there. Duplicate occurrences already refuse.
The source frame records where that reference was actually selected; no root/target frame,
outward cursor, real provenance, generated label, comparison, or execution result is assumed.
Local-reference fallback remains separate.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedDetectedTerminalRefusal

open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedCertifiedTerminalRefusal
open LocalizedMarkedDetectedFrames
open LocalizedMarkedUncappedEvaluator (operations)
open LocalizedMarkedOperationEvaluator (descriptor? facts)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? frameAtomsOf)
open CertifiedLocalizedCIPInput

abbrev Node := RawMolecule.CanonicalBranchNode

theorem physical_terminal_carried_none (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (root center : input.detectedMultiCenterMolecule.Center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center)
    (source target : Node) (sourcePath : ReachedFrom mol root.1.val source)
    (path : StrictDescendant mol source target) (current : target.atom = center.1.val)
    (sourceAtoms : List Nat) (sourceFrame : frameAtoms? mol source = some sourceAtoms)
    (mark : Nat) (selected : mark ∈ sourceAtoms)
    (targetNeighbor : 0 < mol.bondOrder target.atom mark)
    (depth : Nat) (geom : Geometry) :
    descriptor? mol (operations mol) depth geom [] (some mark) target = none := by
  cases forced : target.forcedLeaf with
  | true =>
      exact LocalizedMarkedOperationSimulation.descriptor_none_of_frame mol (operations mol)
        geom [] (some mark) target (facts mol (operations mol) depth)
        (LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol target forced)
  | false =>
      have real : target.provenance = .realAtom := by
        cases provenance : target.provenance <;>
          simp [RawMolecule.CanonicalBranchNode.forcedLeaf, provenance] at forced
        rfl
      have sourceReached : Reached mol source :=
        ⟨root.1.val, raw_atom_bound mol input agreement root.1, sourcePath⟩
      have targetReached : Reached mol target := by
        obtain ⟨child, edge, rest⟩ := path
        exact descendant_reached (reached_child mol source child sourceReached edge) rest
      have rootFrame := detected_root_frame mol input agreement admissible supported single root
      have targetFrame := detected_frame mol input agreement admissible supported single center
        target targetReached real current
      have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
      have perm := occurrence_atoms_perm_neighbors mol admissible.1.1 rawSingle target
        targetReached forced
      have member : mark ∈ frameAtomsOf (occurrenceLigandCursors mol target) :=
        perm.mem_iff.mpr
          ((mol.mem_canonicalIncidentNeighbors_iff target.atom admissible.1.1 mark).mpr targetNeighbor)
      exact physical_terminal_carried_descriptor_none mol input agreement admissible.1.1
        admissible.1.2 supported single root center twin _ rootFrame source target sourcePath path
        current sourceAtoms sourceFrame _ targetFrame mark selected member depth geom

end TetraStereo.OneCenter.LocalizedMarkedDetectedTerminalRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedTerminalRefusal.physical_terminal_carried_none
