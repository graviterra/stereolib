import TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000







namespace TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceArmCoordinates

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames

/-- Each role is transported into this actual parser output's own source. -/
def sourceRoleAtom (c l r : TetrahedralInputParity) (index : Fin 11) :
    (ownSource (raw c l r)).AromaticCanonicalAtom :=
  (raw c l r).convertedAtomIndex (ownSource (raw c l r))
    (raw_semantic_conversion c l r)
    ⟨index.val, by rw [raw_atom_count]; exact index.isLt⟩

@[simp] theorem sourceRoleAtom_index (c l r : TetrahedralInputParity) (index : Fin 11) :
    (sourceRoleAtom c l r index).val = index.val := rfl

/-- Atomic number is read from the same source atom, with no alternate molecule. -/
theorem source_role_Z (c l r : TetrahedralInputParity) (index : Fin 11) :
    (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.atomZ
        (sourceRoleAtom c l r index) = (raw c l r).atomZAt index.val :=
  converted_atomic_number (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) (sourceRoleAtom c l r index)

theorem raw_arm_atomic_numbers (c l r : TetrahedralInputParity) :
    [5, 4, 1, 3].map (raw c l r).atomZAt = [17, 9, 6, 1] ∧
    [10, 9, 1, 8].map (raw c l r).atomZAt = [17, 9, 6, 1] := by
  cases c <;> cases l <;> cases r <;> decide +kernel

theorem source_arm_atomic_numbers (c l r : TetrahedralInputParity) :
    ([5, 4, 1, 3] : List (Fin 11)).map (fun index =>
      (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.atomZ
        (sourceRoleAtom c l r index)) = [17, 9, 6, 1] ∧
    ([10, 9, 1, 8] : List (Fin 11)).map (fun index =>
      (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.atomZ
        (sourceRoleAtom c l r index)) = [17, 9, 6, 1] := by
  simpa only [List.map_cons, List.map_nil, source_role_Z] using
    raw_arm_atomic_numbers c l r

/-- The two distinct arms at the shared central root both start with carbon. -/
theorem central_arm_priorities_tie (c l r : TetrahedralInputParity) :
    occurrenceAtomicPriority (ownSource (raw c l r)) (sourceFrame c l r)
        (leftArmSlot c l r) = 6 ∧
    occurrenceAtomicPriority (ownSource (raw c l r)) (sourceFrame c l r)
        (rightArmSlot c l r) = 6 := by
  rw [leftArm_priority, rightArm_priority]
  cases c <;> cases l <;> cases r <;> decide +kernel

/-- Exact comparator arithmetic within either arm, prior to any label comparison. -/
theorem arm_atomic_order :
    ExactOfficialRuleMajorKey.compareExactAtomicNumber (.ofNat 17) (.ofNat 9) = .gt ∧
    ExactOfficialRuleMajorKey.compareExactAtomicNumber (.ofNat 9) (.ofNat 6) = .gt ∧
    ExactOfficialRuleMajorKey.compareExactAtomicNumber (.ofNat 6) (.ofNat 1) = .gt := by
  decide +kernel

/-- The actual ligand lists used by occurrenceFactAuthoritative?'s lookup. -/
theorem actual_arm_ligands (c l r : TetrahedralInputParity) :
    (raw c l r).ligandsWithLonePair 2 = [1, 3, 4, 5] ∧
    (raw c l r).ligandsWithLonePair 7 = [1, 8, 9, 10] := by
  cases c <;> cases l <;> cases r <;> decide +kernel

/-- Production's zip-index lookup, supplied physical priority IDs explicitly. -/
theorem actual_arm_written_match (c l r : TetrahedralInputParity) :
    [5, 4, 1, 3].mapM (writtenSlot? ((raw c l r).ligandsWithLonePair 2)) =
        some [3, 2, 0, 1] ∧
    [10, 9, 1, 8].mapM (writtenSlot? ((raw c l r).ligandsWithLonePair 7)) =
        some [3, 2, 0, 1] := by
  rw [(actual_arm_ligands c l r).1, (actual_arm_ligands c l r).2]
  decide +kernel

theorem arm_written_positions_odd :
    permutationIsEven [3, 2, 0, 1] = false := by decide +kernel

/-- Descriptor arithmetic after the explicitly supplied physical order is matched. -/
theorem arm_written_descriptor (parity : TetrahedralInputParity) :
    descriptorOfParity parity (permutationIsEven [3, 2, 0, 1]) =
      descriptorOfParity parity false := by
  rw [arm_written_positions_odd]

end TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceArmCoordinates
