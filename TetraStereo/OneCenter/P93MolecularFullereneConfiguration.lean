import TetraStereo.OneCenter.CIPObservedFullereneConfigurationPipeline
import TetraStereo.OneCenter.P94MolecularRingCycleScheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open BlueBookP94
open BlueBookP94.CoordinateRing
open P94MolecularRingCycleScheduler

/-!
# Molecule-bound P-93.5.6 fullerene configuration

The earlier P-93.5.6 classifier deliberately accepted an opaque list as the identity of a
caller-declared fullerene cage.  This module supplies the missing molecular boundary.  A cage is
now a canonical finite atom set together with a checked combinatorial face map on the normalized
raw molecular graph.

The certificate is intentionally explicit.  Every cage atom is an in-bounds carbon, the induced
cage graph is connected and cubic, every supplied face is a chordless induced molecular cycle of
length five or six, face carriers are unique and cover the cage, exactly twelve faces are
pentagons, the hexagon count and Euler characteristic are those of a spherical fullerene map, and
every cage edge occurs in exactly two faces.  This proves molecular cage identity and its finite
face decomposition.  It does not pretend that constitution alone derives the five P-93.5.6
substitution/chirality observations; those remain separately visible evidence in the input.
-/

/-- Source-facing molecular fullerene record.  `carrier` is a `Finset`, so physical cage identity
does not depend on caller ordering or duplicate atom numbers. -/
structure MolecularFullereneConfigurationInput where
  carrier : Finset ℕ
  faces : List (List ℕ)
  substitutionTest : FullereneSubstitutionTest
  descriptorEvidence : FullereneDescriptorEvidence

/-- Positive molecular bonds from one atom to other atoms in the proposed cage. -/
def molecularFullereneCageNeighbors
    (molecule : RawMolecule) (carrier : Finset ℕ) (atom : ℕ) : Finset ℕ :=
  carrier.filter fun neighbor => 0 < molecule.bondOrder atom neighbor

/-- Orientation-free finite list of the undirected bonds induced by a proposed cage. -/
def molecularFullereneCageEdges
    (molecule : RawMolecule) (carrier : Finset ℕ) : Finset (ℕ × ℕ) :=
  (carrier ×ˢ carrier).filter fun edge =>
    edge.1 < edge.2 ∧ 0 < molecule.bondOrder edge.1 edge.2

/-- A path witnessing connectivity inside the proposed cage.  The witness is finite and simple;
all its vertices lie in the carrier and every consecutive pair is an actual molecular bond. -/
def MolecularFullereneCagePath
    (molecule : RawMolecule) (carrier : Finset ℕ)
    (first second : ℕ) (path : List ℕ) : Prop :=
  path.Nodup ∧
    (∀ atom ∈ path, atom ∈ carrier) ∧
    path.head? = some first ∧
    path.getLast? = some second ∧
    P94ConformationUnit.ConsecutivelyBonded molecule path

noncomputable instance molecularFullereneCagePathDecidable
    (molecule : RawMolecule) (carrier : Finset ℕ)
    (first second : ℕ) (path : List ℕ) :
    Decidable (MolecularFullereneCagePath molecule carrier first second path) :=
  Classical.propDecidable _

/-- Every pair of cage atoms is joined by a path that remains inside the cage. -/
def MolecularFullereneCageConnected
    (molecule : RawMolecule) (carrier : Finset ℕ) : Prop :=
  carrier.Nonempty ∧
    ∀ first ∈ carrier, ∀ second ∈ carrier,
      ∃ path, MolecularFullereneCagePath molecule carrier first second path

noncomputable instance molecularFullereneCageConnectedDecidable
    (molecule : RawMolecule) (carrier : Finset ℕ) :
    Decidable (MolecularFullereneCageConnected molecule carrier) :=
  Classical.propDecidable _

/-- One supplied face is exactly a chordless induced molecular cycle on the cage and has a
fullerene face size. -/
def MolecularFullereneFaceJudgment
    (molecule : RawMolecule) (carrier : Finset ℕ) (face : List ℕ) : Prop :=
  IndependentP94RingTraversal molecule face ∧
    face.toFinset ⊆ carrier ∧
    (face.length = 5 ∨ face.length = 6)

noncomputable instance molecularFullereneFaceJudgmentDecidable
    (molecule : RawMolecule) (carrier : Finset ℕ) (face : List ℕ) :
    Decidable (MolecularFullereneFaceJudgment molecule carrier face) :=
  Classical.propDecidable _

/-- Independent source-backed meaning of a checked fullerene cage and combinatorial spherical
face map on one raw molecular graph. -/
structure MolecularFullereneCarrierJudgment
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) : Prop where
  minimumSize : 20 ≤ input.carrier.card
  carbonAtoms : ∀ atom ∈ input.carrier,
    ∃ spec, molecule.atomAt? atom = some spec ∧ spec.element = .C
  cubic : ∀ atom ∈ input.carrier,
    (molecularFullereneCageNeighbors molecule input.carrier atom).card = 3
  connected : MolecularFullereneCageConnected molecule input.carrier
  facesNodup : (input.faces.map List.toFinset).Nodup
  facesValid : ∀ face ∈ input.faces,
    MolecularFullereneFaceJudgment molecule input.carrier face
  facesCover : ∀ atom,
    atom ∈ input.carrier ↔ ∃ face ∈ input.faces, atom ∈ face
  twelvePentagons :
    input.faces.countP (fun face => decide (face.length = 5)) = 12
  hexagonCount :
    input.faces.countP (fun face => decide (face.length = 6)) =
      input.carrier.card / 2 - 10
  twoFacesPerCageEdge : ∀ left ∈ input.carrier, ∀ right ∈ input.carrier,
    left < right →
      (0 < molecule.bondOrder left right ↔
        input.faces.countP
          (fun face => decide (IsNamedCycleEdge face left right)) = 2)
  eulerCharacteristicTwo :
    input.carrier.card + input.faces.length =
      (molecularFullereneCageEdges molecule input.carrier).card + 2

noncomputable instance molecularFullereneCarrierJudgmentDecidable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) :
    Decidable (MolecularFullereneCarrierJudgment molecule input) :=
  Classical.propDecidable _

/-- Canonical legacy payload consumed by the already-proved P-93.5.6 classifier.  Sorting the
finite carrier makes the cage identity executable and independent of `Finset.toList`'s arbitrary
choice while preserving the same finite atom set. -/
def MolecularFullereneConfigurationInput.toFullereneConfigurationInput
    (input : MolecularFullereneConfigurationInput) : FullereneConfigurationInput :=
  { unit := input.carrier.sort (· ≤ ·)
    substitutionTest := input.substitutionTest
    descriptorEvidence := input.descriptorEvidence }

/-- Admit a caller record only after proving its cage against the molecular graph. -/
noncomputable def molecularFullereneConfigurationInput?
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) :
    Option FullereneConfigurationInput :=
  if MolecularFullereneCarrierJudgment molecule input then
    some input.toFullereneConfigurationInput
  else
    none

/-- Local admission is exact: success contains the canonical atom-set identity and is equivalent
to the independent molecular fullerene carrier judgment. -/
@[simp] theorem molecularFullereneConfigurationInput?_eq_some_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (legacy : FullereneConfigurationInput) :
    molecularFullereneConfigurationInput? molecule input = some legacy ↔
      MolecularFullereneCarrierJudgment molecule input ∧
        legacy = input.toFullereneConfigurationInput := by
  by_cases valid : MolecularFullereneCarrierJudgment molecule input
  · simp [molecularFullereneConfigurationInput?, valid, eq_comm]
  · simp [molecularFullereneConfigurationInput?, valid]

/-- Refusal has no opaque failure case: it is exactly failure of the independent cage/map
judgment. -/
@[simp] theorem molecularFullereneConfigurationInput?_eq_none_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) :
    molecularFullereneConfigurationInput? molecule input = none ↔
      ¬MolecularFullereneCarrierJudgment molecule input := by
  by_cases valid : MolecularFullereneCarrierJudgment molecule input
  · simp [molecularFullereneConfigurationInput?, valid]
  · simp [molecularFullereneConfigurationInput?, valid]

/-- All and only molecule-validated fullerene records, converted to canonical downstream input. -/
noncomputable def validatedMolecularFullereneConfigurationInputs
    (molecule : RawMolecule) (inputs : List MolecularFullereneConfigurationInput) :
    List FullereneConfigurationInput :=
  inputs.filterMap (molecularFullereneConfigurationInput? molecule)

/-- Exact finite-family membership at the graph-validation boundary. -/
theorem mem_validatedMolecularFullereneConfigurationInputs_iff
    (molecule : RawMolecule) (inputs : List MolecularFullereneConfigurationInput)
    (legacy : FullereneConfigurationInput) :
    legacy ∈ validatedMolecularFullereneConfigurationInputs molecule inputs ↔
      ∃ input ∈ inputs,
        MolecularFullereneCarrierJudgment molecule input ∧
          legacy = input.toFullereneConfigurationInput := by
  simp [validatedMolecularFullereneConfigurationInputs,
    molecularFullereneConfigurationInput?_eq_some_iff]

/-- Run the conflict-aware P-93.5.6 family analyzer only on molecule-validated cages. -/
noncomputable def analyzeMolecularFullereneConfigurations
    (molecule : RawMolecule) (inputs : List MolecularFullereneConfigurationInput) :
    List FullereneConfigurationAssignment :=
  analyzeFullereneConfigurations
    (validatedMolecularFullereneConfigurationInputs molecule inputs)

/-- Independent complete meaning of a molecule-backed emitted fullerene assignment.  It includes
one checked molecular cage source, the independent local P-93.5.6 classification/materialization
judgment, and agreement among every validated record naming the same canonical atom set. -/
def MolecularFullereneConfigurationAssignmentJudgment
    (molecule : RawMolecule) (inputs : List MolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    MolecularFullereneCarrierJudgment molecule input ∧
      FullereneConfigurationAssignmentJudgment
        input.toFullereneConfigurationInput assignment ∧
      FullereneConfigurationAssignmentAgreement
        (validatedMolecularFullereneConfigurationInputs molecule inputs) assignment

/-- The molecule-backed analyzer has exact no-invention/no-omission semantics. -/
theorem mem_analyzeMolecularFullereneConfigurations_iff
    (molecule : RawMolecule) (inputs : List MolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    assignment ∈ analyzeMolecularFullereneConfigurations molecule inputs ↔
      MolecularFullereneConfigurationAssignmentJudgment molecule inputs assignment := by
  rw [analyzeMolecularFullereneConfigurations,
    mem_analyzeFullereneConfigurations_iff]
  unfold ConflictFreeFullereneConfigurationAssignmentJudgment
  unfold FullereneConfigurationCandidateJudgment
  unfold MolecularFullereneConfigurationAssignmentJudgment
  constructor
  · rintro ⟨⟨legacy, legacyPresent, localJudged⟩, agreement⟩
    rcases (mem_validatedMolecularFullereneConfigurationInputs_iff
      molecule inputs legacy).mp legacyPresent with
      ⟨input, inputPresent, carrierJudged, legacyEq⟩
    subst legacy
    exact ⟨input, inputPresent, carrierJudged, localJudged, agreement⟩
  · rintro ⟨input, inputPresent, carrierJudged, localJudged, agreement⟩
    exact ⟨⟨input.toFullereneConfigurationInput,
      (mem_validatedMolecularFullereneConfigurationInputs_iff molecule inputs
        input.toFullereneConfigurationInput).mpr
          ⟨input, inputPresent, carrierJudged, rfl⟩,
      localJudged⟩, agreement⟩

/-- Equivalent constructor-level form used when the validated family is embedded into a larger
report pipeline. -/
theorem molecularFullereneConfigurationAssignmentJudgment_iff_conflictFree
    (molecule : RawMolecule) (inputs : List MolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    MolecularFullereneConfigurationAssignmentJudgment molecule inputs assignment ↔
      ConflictFreeFullereneConfigurationAssignmentJudgment
        (validatedMolecularFullereneConfigurationInputs molecule inputs) assignment := by
  rw [← mem_analyzeMolecularFullereneConfigurations_iff]
  exact mem_analyzeFullereneConfigurations_iff
    (validatedMolecularFullereneConfigurationInputs molecule inputs) assignment

/-- Every molecule-backed emitted assignment contains exactly the descriptor kinds required by
its independently proved P-93.5.6 chirality class. -/
theorem MolecularFullereneConfigurationAssignmentJudgment.requirements_exact
    (molecule : RawMolecule) (inputs : List MolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment)
    (judged : MolecularFullereneConfigurationAssignmentJudgment molecule inputs assignment) :
    assignment.payloads.map FullereneDescriptorPayload.requirement =
      RequiredFullereneDescriptorKinds assignment.chiralityType := by
  rcases judged with ⟨input, _inputPresent, _carrierJudged, localJudged, _agreement⟩
  exact localJudged.requirements_exact input.toFullereneConfigurationInput assignment

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
