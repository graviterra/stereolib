import TetraStereo.OneCenter.P93MolecularFullereneConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open P94MolecularRingCycleScheduler

/-!
# Oriented fullerene symmetry and the P-93.5.6 substitution test

P-93.5.6 classifies a single fullerene unit by three increasingly detailed chirality checks:
the parent cage, the substitution sites with every substituent replaced by the same achiral test
group `T`, and the substitution sites with identities/nonidentities retained using achiral test
groups.  This module derives those three answers from a finite oriented face map rather than
accepting them as unrelated Booleans.

The whole original derivative is the final source test and can contain internal substituent
stereogenicity not encoded by a coloring of cage sites.  Its chirality remains explicit evidence.
Likewise, the identity labels and the set of chiral substituent sites are transparent upstream
evidence; later molecule-to-substituent refinement can replace them without changing the finite
oriented-map semantics proved here.
-/

/-- A directed edge in the supplied cyclic orientation of one fullerene face. -/
def IsForwardNamedCycleEdge (face : List ℕ) (left right : ℕ) : Prop :=
  ∃ leftMember : left ∈ face, face.next left leftMember = right

noncomputable instance isForwardNamedCycleEdgeDecidable
    (face : List ℕ) (left right : ℕ) :
    Decidable (IsForwardNamedCycleEdge face left right) :=
  Classical.propDecidable _

/-- The supplied face orientations form a coherent orientation: the two incident faces traverse
each undirected cage edge in opposite directions. -/
def OrientedMolecularFullereneFaceMapJudgment
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) : Prop :=
  MolecularFullereneCarrierJudgment molecule input ∧
    ∀ left ∈ input.carrier, ∀ right ∈ input.carrier,
      left < right → 0 < molecule.bondOrder left right →
        input.faces.countP
            (fun face => decide (IsForwardNamedCycleEdge face left right)) = 1 ∧
          input.faces.countP
            (fun face => decide (IsForwardNamedCycleEdge face right left)) = 1

noncomputable instance orientedMolecularFullereneFaceMapJudgmentDecidable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput) :
    Decidable (OrientedMolecularFullereneFaceMapJudgment molecule input) :=
  Classical.propDecidable _

/-- Typed atoms of the canonical fullerene carrier. -/
abbrev MolecularFullereneCarrierAtom
    (input : MolecularFullereneConfigurationInput) :=
  { atom : ℕ // atom ∈ input.carrier }

/-- Extend a carrier permutation to a total atom-number map.  The fallback is used only outside
the carrier; every validated face atom takes the typed branch. -/
def mapMolecularFullereneCarrierAtom
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (atom : ℕ) : ℕ :=
  if member : atom ∈ input.carrier then
    (symmetry ⟨atom, member⟩).1
  else
    atom

/-- Apply a carrier permutation to one oriented face traversal. -/
def mapMolecularFullereneFace
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input))
    (face : List ℕ) : List ℕ :=
  face.map (mapMolecularFullereneCarrierAtom input symmetry)

/-- A permutation of cage atoms preserves the complete induced cage adjacency relation. -/
def MolecularFullereneCarrierAutomorphism
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Prop :=
  ∀ left right : MolecularFullereneCarrierAtom input,
    (0 < molecule.bondOrder left.1 right.1) ↔
      0 < molecule.bondOrder (symmetry left).1 (symmetry right).1

noncomputable instance molecularFullereneCarrierAutomorphismDecidable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Decidable (MolecularFullereneCarrierAutomorphism molecule input symmetry) :=
  Classical.propDecidable _

/-- A cage automorphism reverses the coherent face-map orientation.  Reversal is compared only
up to cyclic rotation, so no arbitrary first vertex of a face affects the relation. -/
def MolecularFullereneFaceOrientationReversing
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Prop :=
  ∀ face ∈ input.faces,
    ∃ target ∈ input.faces,
      List.IsRotated (mapMolecularFullereneFace input symmetry face).reverse target

noncomputable instance molecularFullereneFaceOrientationReversingDecidable
    (input : MolecularFullereneConfigurationInput)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Decidable (MolecularFullereneFaceOrientationReversing input symmetry) :=
  Classical.propDecidable _

/-- A finite cage coloring is preserved by a carrier permutation. -/
def MolecularFullereneColoringPreserved
    (input : MolecularFullereneConfigurationInput) (color : ℕ → ℕ)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) : Prop :=
  ∀ atom : MolecularFullereneCarrierAtom input,
    color atom.1 = color (symmetry atom).1

noncomputable instance molecularFullereneColoringPreservedDecidable
    (input : MolecularFullereneConfigurationInput) (color : ℕ → ℕ)
    (symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input)) :
    Decidable (MolecularFullereneColoringPreserved input color symmetry) :=
  Classical.propDecidable _

/-- Independent combinatorial chirality of a colored oriented fullerene cage: the face map is
valid and no adjacency- and color-preserving cage automorphism reverses its orientation. -/
def MolecularFullereneColoringChiral
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ) : Prop :=
  OrientedMolecularFullereneFaceMapJudgment molecule input ∧
    ¬∃ symmetry : Equiv.Perm (MolecularFullereneCarrierAtom input),
      MolecularFullereneCarrierAutomorphism molecule input symmetry ∧
        MolecularFullereneFaceOrientationReversing input symmetry ∧
          MolecularFullereneColoringPreserved input color symmetry

noncomputable instance molecularFullereneColoringChiralDecidable
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ) :
    Decidable (MolecularFullereneColoringChiral molecule input color) :=
  Classical.propDecidable _

/-- Boolean realization of the independent finite oriented-map chirality proposition. -/
noncomputable def molecularFullereneColoringChiral
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ) : Bool :=
  decide (MolecularFullereneColoringChiral molecule input color)

/-- Exactness of the finite colored-cage chirality decision. -/
@[simp] theorem molecularFullereneColoringChiral_eq_true_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (color : ℕ → ℕ) :
    molecularFullereneColoringChiral molecule input color = true ↔
      MolecularFullereneColoringChiral molecule input color := by
  simp [molecularFullereneColoringChiral]

/-- Transparent evidence for the two formal achiral-substituent replacement stages and for the
remaining whole-derivative stage.  Equal positive identity labels denote constitutionally
identical substituents; `0` is reserved for an unsubstituted cage site. -/
structure MolecularFullereneSubstitutionEvidence where
  substitutedSites : Finset ℕ
  actualIdentityClassAt : List ℕ
  originalDerivativeChiral : Bool
  chiralSubstituentSites : Finset ℕ

/-- The site evidence is total on every substituted cage atom and does not name external sites. -/
def MolecularFullereneSubstitutionEvidenceJudgment
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence) : Prop :=
  evidence.substitutedSites ⊆ input.carrier ∧
    evidence.chiralSubstituentSites ⊆ evidence.substitutedSites ∧
    ∀ atom ∈ evidence.substitutedSites,
      ∃ identityClass,
        evidence.actualIdentityClassAt[atom]? = some identityClass

noncomputable instance molecularFullereneSubstitutionEvidenceJudgmentDecidable
    (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    Decidable (MolecularFullereneSubstitutionEvidenceJudgment input evidence) :=
  Classical.propDecidable _

/-- Uncolored parent fullerene. -/
def molecularFullereneParentColor (_atom : ℕ) : ℕ := 0

/-- First substitution-test coloring: all occupied sites carry the same achiral test group `T`. -/
def molecularFullereneSameTestSubstituentColor
    (evidence : MolecularFullereneSubstitutionEvidence) (atom : ℕ) : ℕ :=
  if atom ∈ evidence.substitutedSites then 1 else 0

/-- Second substitution-test coloring: identities/nonidentities are retained, while the `+1`
keeps every substituted color distinct from the unsubstituted color `0`. -/
def molecularFullereneActualIdentityColor
    (evidence : MolecularFullereneSubstitutionEvidence) (atom : ℕ) : ℕ :=
  if atom ∈ evidence.substitutedSites then
    evidence.actualIdentityClassAt[atom]?.getD 0 + 1
  else
    0

/-- Derive the complete five-field P-93.5.6 test.  Three cage-stage chirality fields come from the
oriented automorphism semantics, `hasChiralSubstituent` comes from the explicit site set, and only
the final whole-original-molecule chirality remains independent evidence. -/
noncomputable def deriveMolecularFullereneSubstitutionTest
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence) : FullereneSubstitutionTest :=
  { parentChiral :=
      molecularFullereneColoringChiral molecule input molecularFullereneParentColor
    originalDerivativeChiral := evidence.originalDerivativeChiral
    allSubstituentsReplacedByAchiralTChiral :=
      molecularFullereneColoringChiral molecule input
        (molecularFullereneSameTestSubstituentColor evidence)
    substitutionPatternWithActualIdentitiesChiral :=
      molecularFullereneColoringChiral molecule input
        (molecularFullereneActualIdentityColor evidence)
    hasChiralSubstituent := decide evidence.chiralSubstituentSites.Nonempty }

@[simp] theorem deriveMolecularFullereneSubstitutionTest_parentChiral_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    (deriveMolecularFullereneSubstitutionTest molecule input evidence).parentChiral = true ↔
      MolecularFullereneColoringChiral molecule input molecularFullereneParentColor := by
  exact molecularFullereneColoringChiral_eq_true_iff molecule input
    molecularFullereneParentColor

@[simp] theorem deriveMolecularFullereneSubstitutionTest_sameTestSubstituentChiral_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    (deriveMolecularFullereneSubstitutionTest
      molecule input evidence).allSubstituentsReplacedByAchiralTChiral = true ↔
      MolecularFullereneColoringChiral molecule input
        (molecularFullereneSameTestSubstituentColor evidence) := by
  exact molecularFullereneColoringChiral_eq_true_iff molecule input
    (molecularFullereneSameTestSubstituentColor evidence)

@[simp] theorem deriveMolecularFullereneSubstitutionTest_actualIdentitiesChiral_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    (deriveMolecularFullereneSubstitutionTest
      molecule input evidence).substitutionPatternWithActualIdentitiesChiral = true ↔
      MolecularFullereneColoringChiral molecule input
        (molecularFullereneActualIdentityColor evidence) := by
  exact molecularFullereneColoringChiral_eq_true_iff molecule input
    (molecularFullereneActualIdentityColor evidence)

@[simp] theorem deriveMolecularFullereneSubstitutionTest_hasChiralSubstituent_iff
    (molecule : RawMolecule) (input : MolecularFullereneConfigurationInput)
    (evidence : MolecularFullereneSubstitutionEvidence) :
    (deriveMolecularFullereneSubstitutionTest
      molecule input evidence).hasChiralSubstituent = true ↔
      evidence.chiralSubstituentSites.Nonempty := by
  simp [deriveMolecularFullereneSubstitutionTest]

/-- Strict source record for the authoritative report. -/
structure SymmetryDerivedMolecularFullereneConfigurationInput where
  cage : MolecularFullereneConfigurationInput
  substitutionEvidence : MolecularFullereneSubstitutionEvidence

/-- The cage map is coherently oriented, substitution evidence is total, and the downstream test
is exactly the one derived from the finite symmetry semantics. -/
def SymmetryDerivedMolecularFullereneConfigurationInputJudgment
    (molecule : RawMolecule)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput) : Prop :=
  OrientedMolecularFullereneFaceMapJudgment molecule input.cage ∧
    MolecularFullereneSubstitutionEvidenceJudgment
      input.cage input.substitutionEvidence ∧
    input.cage.substitutionTest =
      deriveMolecularFullereneSubstitutionTest molecule input.cage input.substitutionEvidence

noncomputable instance symmetryDerivedMolecularFullereneConfigurationInputJudgmentDecidable
    (molecule : RawMolecule)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput) :
    Decidable (SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input) :=
  Classical.propDecidable _

/-- Admit a cage into the next pipeline layer only when its P-93.5.6 substitution test is the exact
symmetry-derived test for its oriented molecular face map. -/
noncomputable def symmetryDerivedMolecularFullereneConfigurationInput?
    (molecule : RawMolecule)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput) :
    Option MolecularFullereneConfigurationInput :=
  if SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input then
    some input.cage
  else
    none

@[simp] theorem symmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff
    (molecule : RawMolecule)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput)
    (cage : MolecularFullereneConfigurationInput) :
    symmetryDerivedMolecularFullereneConfigurationInput? molecule input = some cage ↔
      SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input ∧
        cage = input.cage := by
  by_cases valid :
      SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input
  · simp [symmetryDerivedMolecularFullereneConfigurationInput?, valid, eq_comm]
  · simp [symmetryDerivedMolecularFullereneConfigurationInput?, valid]

@[simp] theorem symmetryDerivedMolecularFullereneConfigurationInput?_eq_none_iff
    (molecule : RawMolecule)
    (input : SymmetryDerivedMolecularFullereneConfigurationInput) :
    symmetryDerivedMolecularFullereneConfigurationInput? molecule input = none ↔
      ¬SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input := by
  by_cases valid :
      SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input
  · simp [symmetryDerivedMolecularFullereneConfigurationInput?, valid]
  · simp [symmetryDerivedMolecularFullereneConfigurationInput?, valid]

/-- Finite family of all and only symmetry-derived molecular fullerene inputs. -/
noncomputable def validatedSymmetryDerivedMolecularFullereneConfigurationInputs
    (molecule : RawMolecule)
    (inputs : List SymmetryDerivedMolecularFullereneConfigurationInput) :
    List MolecularFullereneConfigurationInput :=
  inputs.filterMap (symmetryDerivedMolecularFullereneConfigurationInput? molecule)

/-- Exact source-family membership for the symmetry derivation boundary. -/
theorem mem_validatedSymmetryDerivedMolecularFullereneConfigurationInputs_iff
    (molecule : RawMolecule)
    (inputs : List SymmetryDerivedMolecularFullereneConfigurationInput)
    (cage : MolecularFullereneConfigurationInput) :
    cage ∈ validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule inputs ↔
      ∃ input ∈ inputs,
        SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input ∧
          cage = input.cage := by
  simp [validatedSymmetryDerivedMolecularFullereneConfigurationInputs,
    symmetryDerivedMolecularFullereneConfigurationInput?_eq_some_iff]

/-- Independent complete meaning of an emitted assignment sourced from an oriented-map symmetry
derivation.  The witness retains the exact strict source record, while agreement is checked over
the complete family after both symmetry and molecular-cage validation. -/
def SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
    (molecule : RawMolecule)
    (inputs : List SymmetryDerivedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ input ∈ inputs,
    SymmetryDerivedMolecularFullereneConfigurationInputJudgment molecule input ∧
      FullereneConfigurationAssignmentJudgment
        input.cage.toFullereneConfigurationInput assignment ∧
      FullereneConfigurationAssignmentAgreement
        (validatedMolecularFullereneConfigurationInputs molecule
          (validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule inputs))
        assignment

/-- The strict source-level assignment judgment is exactly the existing molecule-backed judgment
over the family admitted by the symmetry boundary. -/
theorem symmetryDerivedMolecularFullereneConfigurationAssignmentJudgment_iff_molecular
    (molecule : RawMolecule)
    (inputs : List SymmetryDerivedMolecularFullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
        molecule inputs assignment ↔
      MolecularFullereneConfigurationAssignmentJudgment molecule
        (validatedSymmetryDerivedMolecularFullereneConfigurationInputs molecule inputs)
        assignment := by
  unfold SymmetryDerivedMolecularFullereneConfigurationAssignmentJudgment
  unfold MolecularFullereneConfigurationAssignmentJudgment
  constructor
  · rintro ⟨input, inputPresent, strictJudged, localJudged, agreement⟩
    exact ⟨input.cage,
      (mem_validatedSymmetryDerivedMolecularFullereneConfigurationInputs_iff
        molecule inputs input.cage).mpr ⟨input, inputPresent, strictJudged, rfl⟩,
      strictJudged.1.1, localJudged, agreement⟩
  · rintro ⟨cage, cagePresent, _carrierJudged, localJudged, agreement⟩
    rcases (mem_validatedSymmetryDerivedMolecularFullereneConfigurationInputs_iff
      molecule inputs cage).mp cagePresent with
      ⟨input, inputPresent, strictJudged, cageEq⟩
    subst cage
    exact ⟨input, inputPresent, strictJudged, localJudged, agreement⟩

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
