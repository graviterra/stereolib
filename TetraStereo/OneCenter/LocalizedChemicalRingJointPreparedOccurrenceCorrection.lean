import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedEvenReadings
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionLoop
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! A refused prepared occurrence has an odd correction retaining EVERY inherited reference,
assuming source-properness only at strictly smaller residual depth. The even case uses an actual
failed selected fallback, then the smaller-depth claim at the extended list. Unlike the older
single-reference argument there is no moving-reference escape. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedOccurrenceCorrection

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointSelectedTieWitness (JointMatchedSymmetry joint_matched_of_tie)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingReferenceConsensusCorrectionInduction (reextend_proper)
open LocalizedChemicalRingJointPreparedExecution
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingJointOrientationExecution (selected_fixed_context_odd)
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open LocalizedChemicalRingPhysicalSense
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

/-- One automorphism for the whole source component of a tie. -/
def SourceProper (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (references : List input.Atom) (a b : input.Atom) : Prop :=
  ∃ e : input.detectedMultiCenterMolecule.Aut,
    (∀ atom ∈ target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom) ∧
    (e : Equiv.Perm input.Atom) a = b ∧
    (∀ reference ∈ references, (e : Equiv.Perm input.Atom) reference = reference) ∧
    ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1

/-- The actual same-context, same-geometry source-proper claim at residual size n. -/
def Claim (n : Nat) : Prop :=
  ∀ (node : RawMolecule.CanonicalBranchNode), structuralDepth mol node = n → Reached mol node →
  ∀ (c : input.detectedMultiCenterMolecule.Center), node.atom = c.1.val →
  ∀ (data : OccurrenceData input mol c node), TiedRootBranch input data.target →
  ∀ (references : List input.Atom) (reflected : Bool) (left right : Fin 4) (a b : input.Atom), a ≠ b →
  JointMatchedSymmetry input single
    (sideState input mol node (inputGeometry input) references reflected) data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references left right a b →
  SourceProper input cfg data.target references a b

def CenterCorrection (d : input.detectedMultiCenterMolecule.Center) (B : List input.Atom)
    (references : List input.Atom) (g : input.detectedMultiCenterMolecule.Aut) : Prop :=
  ∃ a' b' : input.Atom,
    input.moleculeGraph.Adj d.1 a' ∧ input.moleculeGraph.Adj d.1 b' ∧
    (∀ x ∈ B ++ [d.1], (g : Equiv.Perm input.Atom) x = x) ∧
    (∀ x, ¬ InComponent input.moleculeGraph (B ++ [d.1]) a' x →
      ¬ InComponent input.moleculeGraph (B ++ [d.1]) b' x → (g : Equiv.Perm input.Atom) x = x) ∧
    (∀ reference ∈ references, (g : Equiv.Perm input.Atom) reference = reference) ∧
    relativeSign input.detectedMultiCenterMolecule cfg g d = -1 ∧
    ∀ e : input.detectedMultiCenterMolecule.Center, e.1 ∉ B ++ [d.1] →
      relativeSign input.detectedMultiCenterMolecule cfg g e = 1

include agreement admissible supported single charge calibrated in
theorem occurrence_correction (n : Nat) (IH : ∀ m < n, Claim input mol single cfg m)
    (d : input.detectedMultiCenterMolecule.Center) (query : RawMolecule.CanonicalBranchNode)
    (queryReached : Reached mol query) (queryReal : query.provenance = .realAtom)
    (atomEq : query.atom = d.1.val) (smaller : structuralDepth mol query < n)
    (B : List input.Atom) (outsideB : d.1 ∉ B)
    (boundary : ∀ actual : OccurrenceData input mol d query,
      actual.target.1.node.history.reverse = B ++ [d.1])
    (branch : ∀ actual : OccurrenceData input mol d query, TiedRootBranch input actual.target)
    (references : List input.Atom)
    (refused : preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol query) (inputGeometry input) [] (references.map Fin.val) query = none) :
    ∃ g, CenterCorrection input cfg d B references g := by
  obtain ⟨actual⟩ := occurrenceData_exists input mol agreement admissible supported single d query
    queryReached queryReal atomEq
  have failedSide : ∃ side : Bool, step input mol query (structuralDepth mol query)
      (observedGeometry input side) references = none := by
    rcases (descriptor_none_iff input mol query (structuralDepth mol query)
      (inputGeometry input) references).mp refused with first | second
    · exact ⟨false, first⟩
    · exact ⟨true, second⟩
  obtain ⟨side, stepNone⟩ := failedSide
  have notInj := step_none_noninjective input mol agreement admissible supported single d query actual
    (structuralDepth mol query) references cfg (calibrated d) side stepNone
  obtain ⟨i, j, tie, different⟩ := Function.not_injective_iff.mp notInj
  have actualBoundary := boundary actual
  have branchQ := branch actual
  have sound := (LocalizedMarkedCarrierLookup.lookup?_sound input query actual.target actual.found).history
  have inHistory : ∀ x ∈ B ++ [d.1], x.val ∈ query.history := by
    intro x member
    rw [← sound]
    rw [← actualBoundary] at member
    exact List.mem_map.mpr ⟨x, List.mem_reverse.mp member, rfl⟩
  have carriedB : ∀ atom ∈ B, atom.val ∈ query.history :=
    fun atom member => inHistory atom (List.mem_append_left _ member)
  have centerMember : d.1 ∈ B ++ [d.1] := List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have adjacentOf (slot : Fin 4) :
      input.moleculeGraph.Adj d.1 (referenceAt input mol d query actual slot) :=
    input.detectedMultiCenterMolecule.ligandAtomAt_adj d (actual.ligandOf slot)
  obtain ⟨a', b', distinctQ, ⟨w⟩⟩ := joint_matched_of_tie input mol single charge d query actual branchQ
    _ references i j different tie
  have atLeft : a' = referenceAt input mol d query actual i :=
    Option.some.inj (w.leftCurrent.symm.trans (slot_current input mol single d query actual _ i))
  have atRight : b' = referenceAt input mol d query actual j :=
    Option.some.inj (w.rightCurrent.symm.trans (slot_current input mol single d query actual _ j))
  have adjacentA : input.moleculeGraph.Adj d.1 a' := by
    rw [atLeft]
    exact adjacentOf i
  have adjacentB : input.moleculeGraph.Adj d.1 b' := by
    rw [atRight]
    exact adjacentOf j
  obtain ⟨e, fixedE, entryE, referencesE, properE⟩ :=
    IH _ smaller query rfl queryReached d atomEq actual branchQ references side i j a' b' distinctQ w
  have fixedB : ∀ x ∈ B ++ [d.1], (e : Equiv.Perm input.Atom) x = x := by
    intro x member
    rw [← actualBoundary] at member
    exact fixedE x (List.mem_reverse.mp member)
  have sourceE : ∀ x : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (B ++ [d.1]) a' x.1 →
      relativeSign input.detectedMultiCenterMolecule cfg e x = 1 := by
    intro x member
    rw [← actualBoundary] at member
    exact properE x member
  obtain ⟨g1, fixed1, support1, moved1, keeps1, off1⟩ :=
    reextend_proper input cfg (B ++ [d.1]) a' b' e fixedB entryE distinctQ sourceE
  have references1 : ∀ reference ∈ references, (g1 : Equiv.Perm input.Atom) reference = reference :=
    fun reference member => keeps1 reference (referencesE reference member)
  rcases relativeSign_eq_one_or_neg_one input.detectedMultiCenterMolecule cfg g1 d with
    evenSign | negative
  swap
  · exact ⟨g1, a', b', adjacentA, adjacentB, fixed1, support1, references1, negative, off1⟩
  -- The map fixing the reference is even at the center: the fallback population decides.
  have historyFixed1 : ∀ atom ∈ actual.target.1.node.history,
      (g1 : Equiv.Perm input.Atom) atom = atom := by
    intro atom member
    exact fixed1 atom (by rw [← actualBoundary]; exact List.mem_reverse.mpr member)
  have properResidual : ∀ x : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph B d.1 x.1 → x.1 ≠ d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg g1 x = 1 := by
    intro x member other
    apply off1
    intro present
    rcases List.mem_append.mp present with inB | isCenter
    · exact inComponent_not_mem input.moleculeGraph member inB
    · exact other (List.mem_singleton.mp isCenter)
  obtain ⟨slot, member, failed⟩ :=
    LocalizedChemicalRingJointPreparedEvenReadings.refusal_has_failed_selected
      input mol agreement admissible supported single cfg calibrated d query actual queryReached atomEq
      g1 (fixed1 d.1 centerMember) historyFixed1 references references1 B outsideB carriedB properResidual
      evenSign branchQ ⟨a', adjacentA, by rw [moved1]; exact Ne.symm distinctQ⟩
      (structuralDepth mol query) side stepNone
  have notInjExtended := (fallback_none_iff input mol agreement admissible supported single d query actual
    (structuralDepth mol query) references cfg (calibrated d) side slot).mp failed
  obtain ⟨left, right, extendedTie, differentExtended⟩ := Function.not_injective_iff.mp notInjExtended
  obtain ⟨a'', b'', distinctO, ⟨wOdd⟩⟩ := joint_matched_of_tie input mol single charge d query actual branchQ
    _ (references ++ [referenceAt input mol d query actual slot]) left right differentExtended extendedTie
  have atOddLeft : a'' = referenceAt input mol d query actual left :=
    Option.some.inj (wOdd.leftCurrent.symm.trans
      (slot_current input mol single d query actual _ left))
  have atOddRight : b'' = referenceAt input mol d query actual right :=
    Option.some.inj (wOdd.rightCurrent.symm.trans
      (slot_current input mol single d query actual _ right))
  have adjacentOddA : input.moleculeGraph.Adj d.1 a'' := by
    rw [atOddLeft]
    exact adjacentOf left
  have adjacentOddB : input.moleculeGraph.Adj d.1 b'' := by
    rw [atOddRight]
    exact adjacentOf right
  obtain ⟨o, fixedO, entryO, referencesO, properO⟩ :=
    IH _ smaller query rfl queryReached d atomEq actual branchQ
      (references ++ [referenceAt input mol d query actual slot]) side left right a'' b'' distinctO wOdd
  have fixedOB : ∀ x ∈ B ++ [d.1], (o : Equiv.Perm input.Atom) x = x := by
    intro x present
    rw [← actualBoundary] at present
    exact fixedO x (List.mem_reverse.mp present)
  have sourceO : ∀ x : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (B ++ [d.1]) a'' x.1 →
      relativeSign input.detectedMultiCenterMolecule cfg o x = 1 := by
    intro x present
    rw [← actualBoundary] at present
    exact properO x present
  obtain ⟨g2, fixed2, support2, moved2, keeps2, off2⟩ :=
    reextend_proper input cfg (B ++ [d.1]) a'' b'' o fixedOB entryO distinctO sourceO
  have historyFixed2 : ∀ atom ∈ actual.target.1.node.history,
      (g2 : Equiv.Perm input.Atom) atom = atom := by
    intro atom member
    exact fixed2 atom (by rw [← actualBoundary]; exact List.mem_reverse.mpr member)
  have refs2 : ∀ reference ∈ references ++ [referenceAt input mol d query actual slot],
      (g2 : Equiv.Perm input.Atom) reference = reference :=
    fun reference member => keeps2 reference (referencesO reference member)
  have oddLocal := selected_fixed_context_odd input mol single d query actual references branchQ
    (generated input mol (structuralDepth mol query) (observedGeometry input side) query references)
    slot member g2 (fixed2 d.1 centerMember) historyFixed2 refs2
    ⟨a'', adjacentOddA, by rw [moved2]; exact Ne.symm distinctO⟩
  have negativeO : relativeSign input.detectedMultiCenterMolecule cfg g2 d = -1 := by
    rw [LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed input cfg g2 d
      (Subtype.ext (fixed2 d.1 centerMember))]
    exact oddLocal
  exact ⟨g2, a'', b'', adjacentOddA, adjacentOddB, fixed2, support2,
    fun reference member => refs2 reference (List.mem_append_left _ member), negativeO, off2⟩


end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedOccurrenceCorrection

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedOccurrenceCorrection.occurrence_correction
