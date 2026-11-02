import TetraStereo.OneCenter.LocalizedMarkedRetainedOperations
import TetraStereo.OneCenter.LocalizedMarkedDetectedSnapshotSupport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Actual retained ordinary execution at a physical detected center

A physical detected-center member and the raw current-atom identity establish detection of the
looked-up carrier unit. The raw/certified frame-position permutation then identifies the executable
`findIdx?` conversion exactly: it applies the inverse slot permutation to every ranked certified
slot. Consequently the returned positions permute all four raw slots, rather than merely being
four bounded indices. Rings, arbitrary auxiliary states, and ties remain allowed.

These are normal-domain ordinary-operation statements. They do not justify the marked operation,
interpret generated labels, or claim a global shape invariant for malformed raw inputs.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedOperations LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedCertifiedTerminalRefusal LocalizedMarkedDetectedFrames
open LocalizedMarkedDetectedSnapshotSupport LocalizedMarkedFramePositionBridge
open LocalizedMarkedCarrierLookup
open LocalizedGenericMarkedRecalculation (frameAtoms?)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Physical inventory membership supplies the previously explicit looked-up detection premise.
No successful frame, degree assertion about the runtime frame, or descriptor result is assumed. -/
theorem lookup_detected_of_physical_center
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (center : input.detectedMultiCenterMolecule.Center) (node : Node)
    (current : node.atom = center.1.val)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target) :
    IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have valid : node.atom < mol.atomCount := by
    rw [current]
    exact raw_atom_bound mol input agreement center.1
  have degree : (mol.canonicalIncidentNeighbors node.atom).length = 4 := by
    rw [current]
    exact detected_raw_degree mol input agreement wellFormed unique supported center
  exact carrier_detected_of_raw_degree mol input agreement wellFormed unique supported rawSingle
    target node valid (lookup?_sound input node target found) degree

private theorem findIdx?_get_of_nodup (atoms : List Nat) (nodup : atoms.Nodup)
    (index : Fin atoms.length) :
    atoms.findIdx? (· == atoms.get index) = some index.val := by
  apply List.findIdx?_eq_some_iff_findIdx_eq.mpr
  exact ⟨index.isLt, List.get_idxOf nodup index⟩

/-- The executable `findIdx?` conversion is exactly inverse slot reindexing, including order and
multiplicity for arbitrary input slot lists. Distinct raw atoms are essential to this statement. -/
theorem positions?_eq_inverse_reindex (input : CertifiedLocalizedCIPInput)
    (atoms : List Nat) (length : atoms.length = 4) (nodup : atoms.Nodup)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (reindex : Equiv.Perm (Fin 4))
    (readback : ∀ index : Fin 4,
      (frame.cursorAt (reindex index)).occurrence.1.node.current?.map
        (fun atom : input.Atom => atom.val) =
      some (atoms.get (Fin.cast length.symm index))) :
    ∀ sorted : List (Fin 4),
      positions? input atoms frame sorted =
        some (sorted.map fun slot => (reindex.symm slot).val) := by
  intro sorted
  induction sorted with
  | nil => rfl
  | cons slot rest ih =>
      have read := readback (reindex.symm slot)
      rw [Equiv.apply_symm_apply] at read
      obtain ⟨atom, observed, atomEq⟩ := Option.map_eq_some_iff.mp read
      have found : atoms.findIdx? (· == atom.val) = some (reindex.symm slot).val := by
        rw [atomEq]
        exact findIdx?_get_of_nodup atoms nodup (Fin.cast length.symm (reindex.symm slot))
      simp [positions?, observed, found, ih]

theorem inverse_reindex_perm (reindex : Equiv.Perm (Fin 4)) (sorted : List (Fin 4))
    (permutation : sorted.Perm (List.finRange 4)) :
    (sorted.map fun slot => (reindex.symm slot).val).Perm [0, 1, 2, 3] := by
  have mapped := (permutation.map reindex.symm).trans
    (Equiv.Perm.map_finRange_perm reindex.symm)
  simpa only [List.map_map, Function.comp_def, List.map_coe_finRange_eq_range] using
    mapped.map Fin.val

/-- Any successful conversion of a genuine four-slot permutation returns a permutation of the
four raw indices. This applies directly to the actual `positions?` result, not a replacement list. -/
theorem positions?_perm (input : CertifiedLocalizedCIPInput)
    (atoms : List Nat) (length : atoms.length = 4) (nodup : atoms.Nodup)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (reindex : Equiv.Perm (Fin 4))
    (readback : ∀ index : Fin 4,
      (frame.cursorAt (reindex index)).occurrence.1.node.current?.map
        (fun atom : input.Atom => atom.val) =
      some (atoms.get (Fin.cast length.symm index)))
    (sorted : List (Fin 4)) (permutation : sorted.Perm (List.finRange 4))
    (positions : List Nat) (computed : positions? input atoms frame sorted = some positions) :
    positions.Perm [0, 1, 2, 3] := by
  have exactResult := positions?_eq_inverse_reindex input atoms length nodup frame reindex readback sorted
  have same := Option.some.inj (computed.symm.trans exactResult)
  rw [same]
  exact inverse_reindex_perm reindex sorted permutation

/-- Actual reached execution at a physical detected center: detection, lookup, frame alignment,
and the four-slot output permutation are all derived. Adjacent decisions retain the independent
retained complete-key interpretation of the existing ordinary operation. -/
theorem ordinary_some_of_physical_detected_reached
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (root : Nat) (valid : root < mol.atomCount)
    (center : input.detectedMultiCenterMolecule.Center) (node : Node)
    (reached : ReachedFrom mol root node) (rawReal : node.provenance = .realAtom)
    (current : node.atom = center.1.val) :
    ∃ (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
      (_found : lookup? input node = some target)
      (real : target.1.node.provenance = .realAtom)
      (detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom)
      (positions : List Nat),
      ordinary input mol state node =
        some (positions,
          adjacentBy (fun left right => some
            (compare
              (rawStateKeys input single state target real
                ⟨input.molecularFrameUnit target.1, detected⟩ rfl left)
              (rawStateKeys input single state target real
                ⟨input.molecularFrameUnit target.1, detected⟩ rfl right)))
            (keyOrder (rawStateKeys input single state target real
              ⟨input.molecularFrameUnit target.1, detected⟩ rfl) (List.finRange 4))) ∧
      positions.Perm [0, 1, 2, 3] := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  obtain ⟨target, found, _, corresponds⟩ := lookup?_exists_of_reachedFrom mol input agreement
    wellFormed unique supported rawSingle root valid node reached
  have real := lookup?_real input node target found rawReal
  have detected := lookup_detected_of_physical_center mol input agreement admissible supported
    single center node current target found
  let unit : DetectedOccurrence input.moleculeGraph := ⟨input.molecularFrameUnit target.1, detected⟩
  let execution := rawStateFrames input single state target real unit rfl
  obtain ⟨atoms, length, reindex, rawFrame, nodup, readback⟩ :=
    exists_frame_position_permutation mol input agreement admissible supported single
      (rawStateDescriptorMap input state) target execution node ⟨root, valid, reached⟩ corresponds
  let keys := rawStateKeys input single state target real unit rfl
  let sorted := keyOrder keys (List.finRange 4)
  let positions := sorted.map fun slot => (reindex.symm slot).val
  have converted : positions? input atoms execution.frame sorted = some positions :=
    positions?_eq_inverse_reindex input atoms length nodup execution.frame reindex readback sorted
  dsimp only [sorted, keys] at converted
  refine ⟨target, found, real, detected, positions, ?_, ?_⟩
  · unfold ordinary
    rw [found, rawFrame]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [execution.frameComputed]
    simp only [Option.bind_some]
    rw [ordinaryPartition?_eq input single state target real unit rfl]
    simp only [Option.bind_some, converted]
    rfl
  · exact inverse_reindex_perm reindex sorted (keyOrder_perm keys (List.finRange 4))

/-- The normal-domain shape law for every successful ordinary output, with no desired output list
or detected-target predicate assumed. This does not claim the marked component has been repaired. -/
theorem ordinary_positions_perm_of_physical_detected_reached
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (root : Nat) (valid : root < mol.atomCount)
    (center : input.detectedMultiCenterMolecule.Center) (node : Node)
    (reached : ReachedFrom mol root node) (rawReal : node.provenance = .realAtom)
    (current : node.atom = center.1.val) (positions : List Nat)
    (adjacent : List (Option Ordering))
    (computed : ordinary input mol state node = some (positions, adjacent)) :
    positions.Perm [0, 1, 2, 3] := by
  obtain ⟨_, _, _, _, output, actual, permutation⟩ :=
    ordinary_some_of_physical_detected_reached mol input agreement admissible supported single
      state root valid center node reached rawReal current
  have same := (Prod.mk.inj (Option.some.inj (computed.symm.trans actual))).1
  rw [same]
  exact permutation

end TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution.lookup_detected_of_physical_center
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution.positions?_eq_inverse_reindex
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution.inverse_reindex_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution.positions?_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution.ordinary_some_of_physical_detected_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution.ordinary_positions_perm_of_physical_detected_reached
