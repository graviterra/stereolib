import TetraStereo.OneCenter.LocalizedChemicalRingRawResidualDescendants
import TetraStereo.OneCenter.LocalizedChemicalRingOrientationInduction
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The local physical induction step only needs proper signs at the other centres in
the remaining residual component. Those signs derive the actual descendant-fact agreement
under every context, for the geometry and its mirror. No all-depth label-symmetry premise
is used. Establishing the signs inductively at unlabelled, non-gauge centres remains open. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingRawResidualDescendants
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingOrientationInduction
open LocalizedMarkedOperationEvaluator (Operations underWith mem_tiedChildren_actual)
open LocalizedMarkedTerminalReferenceScope
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedReachedFrameNeighbors (reached_atom_valid)
open LocalizedGenericMarkedRecalculation (frameAtoms? mirror flatMap_congr_mem)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (B : List input.Atom) (source : RawMolecule.CanonicalBranchNode)
  (entry : input.Atom) (entryEq : entry.val = source.atom) (outside : entry ∉ B)
  (carried : ∀ atom ∈ B, atom.val ∈ source.history) (sourceReached : Reached mol source)
  (proper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph B entry d.1 → d.1 ≠ entry →
      relativeSign input.detectedMultiCenterMolecule cfg e d = 1)

include agreement admissible supported single calibrated entryEq outside carried sourceReached proper in
/-- The finite residual-component induction hypothesis supplies all actual descendant
frame readbacks, including degree-three and forced ring-duplicate cases. -/
theorem agreeOn_strictDescendants :
    AgreeOn (StrictDescendant mol source) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))
      (inputGeometry input) := by
  intro node descent atoms frame L sub
  have reached : Reached mol node := by
    obtain ⟨child, edge, rest⟩ := descent
    exact descendant_reached (reached_child mol source child sourceReached edge) rest
  have real : node.forcedLeaf = false := by
    cases leaf : node.forcedLeaf with
    | false => rfl
    | true => rw [LocalizedGenericMarkedRecalculation.frameAtoms?_forcedLeaf mol node leaf] at frame; cases frame
  obtain ⟨child, edge, rest⟩ := descent
  obtain ⟨atom, atomEq, connected⟩ := descendant_component input mol agreement admissible supported
    single B source node entry entryEq outside carried
    ((Relation.ReflTransGen.single edge).trans rest) real
  have different : atom ≠ entry := by
    intro same
    apply strictDescendant_atom_ne sourceReached ⟨child, edge, rest⟩ real
    rw [← atomEq, same, entryEq]
  have signOne : nodeSign input mol agreement admissible supported cfg e node = 1 := by
    unfold nodeSign
    split_ifs with valid
    · apply proper
      · have same : atomOf mol input agreement node.atom valid.1 = atom := by
          apply Fin.ext
          exact atomEq.symm
        simpa only [same] using connected
      · intro same
        apply different
        apply Fin.ext
        simpa only [atomOf_val, atomEq] using congrArg Fin.val same
    · rfl
  rw [flipsBy_input input mol agreement admissible supported single cfg e calibrated
    node reached atoms frame L sub, signOne, flipBy_eq_id _ rfl]
  rfl

include agreement admissible supported single calibrated entryEq outside carried sourceReached proper in
/-- All-context descendant snapshots follow from the finite physical induction hypothesis,
for any actual step with the proved frame-congruence law. Both supported evaluators have
that law (`rawStep_congr_geom` and `distantStep_congr_geom`). -/
theorem underWith_eq_of_residual_signs (ops : Operations) (step : Step)
    (stepCongr : StepCongr step mol ops) (depth : Nat) (state : OccurrenceAuxState) (mark : Nat) :
    underWith mol ops
        (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state source
        (factsWith step mol ops depth) mark =
      underWith mol ops (inputGeometry input) state source (factsWith step mol ops depth) mark ∧
    underWith mol ops
        (mirror (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)))
        state source (factsWith step mol ops depth) mark =
      underWith mol ops (mirror (inputGeometry input)) state source (factsWith step mol ops depth) mark := by
  have agree := agreeOn_strictDescendants input mol agreement admissible supported single cfg e
    calibrated B source entry entryEq outside carried sourceReached proper
  have closed : ∀ parent child, StrictDescendant mol source parent →
      child ∈ mol.canonicalChildren parent → StrictDescendant mol source child := by
    rintro parent child ⟨first, edge, rest⟩ next
    exact ⟨first, edge, rest.tail next⟩
  constructor
  · unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol source) closed stepCongr depth _ _ agree
      state (some mark) child ⟨child, mem_tiedChildren_actual mol ops state source child member, .refl⟩
  · unfold underWith
    apply flatMap_congr_mem
    intro child member
    exact factsWith_congr step (StrictDescendant mol source) closed stepCongr depth _ _ agree.mirror
      state (some mark) child ⟨child, mem_tiedChildren_actual mol ops state source child member, .refl⟩

include agreement admissible supported single calibrated entryEq outside carried sourceReached proper in
/-- The successful-label physical induction step. Descendant-fact equalities are derived
from the residual sign hypothesis, rather than supplied as data or all-context label symmetry.
The two successful executions must still come from the actual witness-label connection. -/
theorem relativeSign_eq_one_of_residual_signs (ops : Operations) (step : Step)
    (stepCongr : StepCongr step mol ops) (stepFlip : StepFlip mol ops step)
    (d : input.detectedMultiCenterMolecule.Center) (atomEq : source.atom = d.1.val)
    (atoms : List Nat) (frame : frameAtoms? mol source = some atoms)
    (depth : Nat) (state : OccurrenceAuxState) (ctx : Option Nat)
    (label : LocalizedTetrahedralRSPseudoDescriptor)
    (original : descriptorWith step mol ops depth (inputGeometry input) state ctx source = some label)
    (pulled : descriptorWith step mol ops depth
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) state ctx source =
        some label) :
    relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
  have below := underWith_eq_of_residual_signs input mol agreement admissible supported single
    cfg e calibrated B source entry entryEq outside carried sourceReached proper
    ops step stepCongr depth state
  exact relativeSign_eq_one_of_descriptor input mol agreement admissible supported single cfg e
    calibrated d source atomEq sourceReached atoms frame ops step stepFlip depth state ctx
    (fun mark => (below mark).1) (fun mark => (below mark).2) label original pulled

end TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep.agreeOn_strictDescendants
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep.underWith_eq_of_residual_signs
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingResidualOrientationStep.relativeSign_eq_one_of_residual_signs
