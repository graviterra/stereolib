import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Evidence-size cap unreachability

The historical `maxEvidenceSize` argument is forwarded through descriptor discovery but is not
inspected by the assignment computation.  These equalities expose that fact through the local
assignment, update, pass, bounded stabilization, and exact auxiliary layers.  Consequently the
production literal `100` is not a refusal threshold and cannot suppress a descriptor.
-/

theorem tetrahedralFactFromProjectedState?_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel center : Nat) :
    tetrahedralFactFromProjectedState? result mol state left fuel center =
      tetrahedralFactFromProjectedState? result mol state right fuel center :=
  rfl

theorem tetrahedralFactFromState?_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel center : Nat) :
    tetrahedralFactFromState? result mol state left fuel center =
      tetrahedralFactFromState? result mol state right fuel center :=
  rfl

theorem updateRawDescriptorAt_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel center : Nat) :
    updateRawDescriptorAt result mol left fuel state center =
      updateRawDescriptorAt result mol right fuel state center :=
  rfl

theorem runRawDescriptorDiscoveryPass_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel : Nat) :
    runRawDescriptorDiscoveryPass result mol left fuel state =
      runRawDescriptorDiscoveryPass result mol right fuel state :=
  rfl

theorem discoverRawDescriptorsFrom_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel remaining : Nat) :
    discoverRawDescriptorsFrom result mol left fuel remaining state =
      discoverRawDescriptorsFrom result mol right fuel remaining state := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      simp only [discoverRawDescriptorsFrom]
      rw [runRawDescriptorDiscoveryPass_evidenceSize_irrelevant
        result mol state left right fuel]
      split
      · rfl
      · exact inductionHypothesis _

theorem discoverRawDescriptorsFromCertified_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel remaining : Nat) :
    discoverRawDescriptorsFromCertified result mol left fuel remaining state =
      discoverRawDescriptorsFromCertified result mol right fuel remaining state := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining inductionHypothesis =>
      simp only [discoverRawDescriptorsFromCertified]
      rw [runRawDescriptorDiscoveryPass_evidenceSize_irrelevant
        result mol state left right fuel]
      split
      · rfl
      · exact inductionHypothesis _

theorem stabilizedRawDescriptorState?_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel remaining : Nat) :
    stabilizedRawDescriptorState? result mol left fuel remaining state =
      stabilizedRawDescriptorState? result mol right fuel remaining state := by
  unfold stabilizedRawDescriptorState?
  rw [discoverRawDescriptorsFromCertified_evidenceSize_irrelevant
    result mol state left right fuel remaining]

theorem auxiliarySimultaneousDescriptorState_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (auxiliary seed : RawDescriptorState) (unresolved : List Nat)
    (left right fuel : Nat) :
    auxiliarySimultaneousDescriptorState result mol auxiliary left fuel unresolved seed =
      auxiliarySimultaneousDescriptorState result mol auxiliary right fuel unresolved seed :=
  rfl

theorem solveAuxiliaryDescriptorDependencies_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel : Nat) :
    solveAuxiliaryDescriptorDependencies result mol left fuel state =
      solveAuxiliaryDescriptorDependencies result mol right fuel state := by
  unfold solveAuxiliaryDescriptorDependencies
  dsimp only
  split
  · rfl
  · rw [auxiliarySimultaneousDescriptorState_evidenceSize_irrelevant
      (result := result) (mol := mol) (left := left) (right := right) (fuel := fuel)]
    split
    · apply discoverRawDescriptorsFrom_evidenceSize_irrelevant
    · rfl

theorem solveExactAuxiliaryDescriptorDependencies_evidenceSize_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (left right fuel : Nat) :
    solveExactAuxiliaryDescriptorDependencies result mol left fuel state =
      solveExactAuxiliaryDescriptorDependencies result mol right fuel state :=
  rfl

end TetraStereo.OneCenter
