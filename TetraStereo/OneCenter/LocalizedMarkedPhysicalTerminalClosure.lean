import TetraStereo.OneCenter.LocalizedMarkedCertifiedTerminalRefusal
import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeRefusal

set_option autoImplicit false















namespace TetraStereo.OneCenter.LocalizedMarkedPhysicalTerminalClosure

open CertifiedLocalizedCIPInput
open LocalizedMarkedCertifiedTerminalRefusal
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedTerminalReferenceScope LocalizedMarkedUncappedOperations
open LocalizedMarkedTerminalOutward LocalizedMarkedTerminalGaugeFrame
open LocalizedMarkedOperationEvaluator LocalizedMarkedOperationSimulation
open LocalizedMarkedUncappedEvaluator (operations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms?)
open AuthoritativeCIPMoleculeCursorRanking

abbrev Node := RawMolecule.CanonicalBranchNode

section Physical

variable (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)

include agreement wellFormed unique supported single in
/-- Construct the actual twin witnesses from molecular leaves and an actual generated path.
In particular, the original detected root is automatically different from either leaf. -/
theorem exists_physicalTwinCenter
    (root center : input.detectedMultiCenterMolecule.Center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center)
    (target : Node) (path : ReachedFrom mol root.1.val target)
    (real : target.provenance = .realAtom) (current : target.atom = center.1.val) :
    ∃ left right : CanonicalRerootCursor, TwinCenter mol target left right := by
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have generated := generated_of_reachedFrom mol root.1.val target path
  obtain ⟨a, b, twins⟩ := twin
  have terminalA : TerminalNeighbor mol target.atom a.val := by
    rw [current]
    exact raw_terminal mol input agreement wellFormed unique supported center.1 a twins.neighbor_a
  have terminalB : TerminalNeighbor mol target.atom b.val := by
    rw [current]
    exact raw_terminal mol input agreement wellFormed unique supported center.1 b twins.neighbor_b
  have rootNeA : root.1.val ≠ a.val := by
    intro equal
    have equalAtoms : root.1 = a := Fin.ext equal
    exact twins.leaf_not_mem_centers_a (equalAtoms ▸ root.2)
  have rootNeB : root.1.val ≠ b.val := by
    intro equal
    have equalAtoms : root.1 = b := Fin.ext equal
    exact twins.leaf_not_mem_centers_b (equalAtoms ▸ root.2)
  obtain ⟨left, leftSlot, leftChild, leftAtom, leftReal, _⟩ := exists_outward_terminal_cursor
    mol wellFormed rawSingle unique root.1.val target generated real a.val terminalA rootNeA
  obtain ⟨right, rightSlot, rightChild, rightAtom, rightReal, _⟩ := exists_outward_terminal_cursor
    mol wellFormed rawSingle unique root.1.val target generated real b.val terminalB rootNeB
  have aData := raw_atom_data mol input agreement a
  have bData := raw_atom_data mol input agreement b
  refine ⟨left, right, ⟨leftSlot, rightSlot, leftChild, rightChild, ?_, ?_,
    leftReal, rightReal, ?_, ?_, ?_⟩⟩
  · simpa [leftAtom] using terminalA
  · simpa [rightAtom] using terminalB
  · rw [leftAtom, rightAtom, ← aData.1, ← bData.1]
    exact twins.z_eq
  · rw [leftAtom, rightAtom, ← aData.2, ← bData.2]
    exact twins.mass_eq
  · rw [leftAtom, rightAtom]
    exact fun equal => twins.ne (Fin.ext equal)

private theorem real_of_frame (target : Node) (atoms : List Nat)
    (frame : frameAtoms? mol target = some atoms) : target.provenance = .realAtom := by
  have notLeaf : target.forcedLeaf = false := by
    cases leaf : target.forcedLeaf with
    | false => rfl
    | true => rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol target leaf]
        at frame; contradiction
  cases provenance : target.provenance <;>
    simp [RawMolecule.CanonicalBranchNode.forcedLeaf, provenance] at notLeaf
  rfl

include agreement wellFormed unique supported single in
/-- Own-context refusal throughout the physical carrier. Frame existence, real provenance and
the actual twin slots are derived when the evaluator reaches its framed branch. -/
theorem physical_terminal_own_descriptor_none
    (root center : input.detectedMultiCenterMolecule.Center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center)
    (target : Node) (path : ReachedFrom mol root.1.val target)
    (current : target.atom = center.1.val) (depth : Nat) (geom : Geometry) :
    descriptor? mol (operations mol) depth geom [] none target = none := by
  cases frame : frameAtoms? mol target with
  | none =>
      exact descriptor_none_of_frame mol (operations mol) geom [] none target _ frame
  | some atoms =>
      obtain ⟨left, right, tc⟩ := exists_physicalTwinCenter mol input agreement wellFormed
        unique supported single root center twin target path (real_of_frame mol target atoms frame)
        current
      exact LocalizedMarkedTerminalGaugeRefusal.descriptor_none tc wellFormed
        (raw_single mol input agreement wellFormed unique supported single) unique
        ⟨root.1.val, raw_atom_bound mol input agreement root.1, path⟩ depth geom none
        (fun _ impossible => by cases impossible)

include agreement wellFormed unique supported single in
/-- The actual top-level assignment of a physically terminal-twin detected center refuses,
without a supplied frame, calibration, comparison or expected descriptor. -/
theorem physical_terminal_assignCenter_none
    (center : input.detectedMultiCenterMolecule.Center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center)
    (geom : Geometry) :
    LocalizedMarkedUncappedEvaluator.assignCenter? mol geom center.1.val = none := by
  exact physical_terminal_own_descriptor_none mol input agreement wellFormed unique supported
    single center center twin (canonicalCenterRoot center.1.val) (.refl) rfl _ geom

include agreement wellFormed unique supported single in
/-- A reference selected at a framed ancestor cannot label a descendant physical twin center.
This includes the evaluator's local fallback when that reference is outside the target frame. -/
theorem physical_terminal_carried_descriptor_none
    (root center : input.detectedMultiCenterMolecule.Center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center)
    (source target : Node) (sourcePath : ReachedFrom mol root.1.val source)
    (path : StrictDescendant mol source target) (current : target.atom = center.1.val)
    (sourceAtoms : List Nat) (sourceFrame : frameAtoms? mol source = some sourceAtoms)
    (mark : Nat) (selected : mark ∈ sourceAtoms) (depth : Nat) (geom : Geometry) :
    descriptor? mol (operations mol) depth geom [] (some mark) target = none := by
  cases frame : frameAtoms? mol target with
  | none =>
      exact descriptor_none_of_frame mol (operations mol) geom [] (some mark) target _ frame
  | some atoms =>
      have rawSingle := raw_single mol input agreement wellFormed unique supported single
      have sourceReached : Reached mol source :=
        ⟨root.1.val, raw_atom_bound mol input agreement root.1, sourcePath⟩
      have targetPath : ReachedFrom mol root.1.val target := by
        obtain ⟨child, edge, rest⟩ := path
        exact (sourcePath.tail edge).trans rest
      have real := real_of_frame mol target atoms frame
      obtain ⟨left, right, tc⟩ := exists_physicalTwinCenter mol input agreement wellFormed
        unique supported single root center twin target targetPath real current
      have notLeaf : target.forcedLeaf = false := by
        simp [RawMolecule.CanonicalBranchNode.forcedLeaf, real]
      have excludes := carried_not_terminal mol wellFormed rawSingle source target sourceReached
        path notLeaf sourceAtoms sourceFrame mark selected
      apply LocalizedMarkedTerminalGaugeRefusal.descriptor_none tc wellFormed rawSingle unique
        ⟨root.1.val, raw_atom_bound mol input agreement root.1, targetPath⟩ depth geom (some mark)
      intro r equal
      cases equal
      exact ⟨fun h => excludes (h ▸ tc.leftTerminal),
        fun h => excludes (h ▸ tc.rightTerminal)⟩

include agreement wellFormed unique supported single in
/-- Actual generated promotion snapshots contain no fact keyed at a real physical twin center.
The root and target are connected by actual expansion, and no target-frame premise is supplied. -/
theorem physical_terminal_snapshot_factAt_none
    (root center : input.detectedMultiCenterMolecule.Center)
    (twin : ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center)
    (target : Node) (targetPath : ReachedFrom mol root.1.val target)
    (real : target.provenance = .realAtom) (current : target.atom = center.1.val)
    (source : Node) (sourceReached : Reached mol source)
    (sourceAtoms : List Nat) (sourceFrame : frameAtoms? mol source = some sourceAtoms)
    (mark : Nat) (selected : mark ∈ sourceAtoms) (depth : Nat) (geom : Geometry) :
    (underWith mol (operations mol) geom [] source (facts mol (operations mol) depth) mark).factAt?
      target = none := by
  obtain ⟨left, right, tc⟩ := exists_physicalTwinCenter mol input agreement wellFormed
    unique supported single root center twin target targetPath real current
  exact LocalizedMarkedTerminalGaugeRefusal.snapshot_factAt_twinCenter_none mol wellFormed
    (raw_single mol input agreement wellFormed unique supported single) unique depth geom source
    sourceReached sourceAtoms sourceFrame mark selected target
    ⟨root.1.val, raw_atom_bound mol input agreement root.1, targetPath⟩ left right tc

end Physical
end TetraStereo.OneCenter.LocalizedMarkedPhysicalTerminalClosure

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedPhysicalTerminalClosure.exists_physicalTwinCenter
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedPhysicalTerminalClosure.physical_terminal_own_descriptor_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedPhysicalTerminalClosure.physical_terminal_assignCenter_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedPhysicalTerminalClosure.physical_terminal_carried_descriptor_none
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedPhysicalTerminalClosure.physical_terminal_snapshot_factAt_none
