import TetraStereo.OneCenter.ChemistrySemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Policy-free P-94 normalization readiness

This module identifies exactly when the fixed certified chemistry normalizer succeeds while
retaining the reviewed raw molecule literally.  It is upstream of the P-94 authority carrier:
neither external provenance policy nor provision judgment occurs in the predicate or proof.
The source-introduction prefix must satisfy the executable internal-consistency check.
-/

namespace TetraStereo.OneCenter
namespace RawMolecule

/-- Every written bond already has an explicit kind. -/
def BondsResolved (molecule : RawMolecule) : Prop :=
  ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified

/-- Exact source-side domain on which certified normalization succeeds and retains the raw
molecule as its parsed result. -/
def P94NormalizationReady (molecule : RawMolecule) : Prop :=
  molecule.StereochemicalAdmissible ∧
    molecule.ValenceOK ∧
    molecule.Rule2MassesKnown ∧
    molecule.BondsResolved ∧
    molecule.introductionPredecessorsValid? = true

theorem normalizeUnspecifiedBond_eq_self_of_resolved
    (molecule : RawMolecule) (bond : RawBond)
    (resolved : bond.kind ≠ .unspecified) :
    molecule.normalizeUnspecifiedBond bond = bond := by
  rcases bond with ⟨source, target, kind⟩
  cases kind <;> simp_all [normalizeUnspecifiedBond]

theorem normalizeUnspecifiedBond_kind_resolved
    (molecule : RawMolecule) (bond : RawBond) :
    (molecule.normalizeUnspecifiedBond bond).kind ≠ .unspecified := by
  rcases bond with ⟨source, target, kind⟩
  cases kind with
  | unspecified =>
      simp only [normalizeUnspecifiedBond]
      cases sourceObserved : molecule.atomAt? source with
      | none => simp
      | some left =>
          cases targetObserved : molecule.atomAt? target with
          | none => simp
          | some right =>
              simp [RawMolecule.defaultBondKind]
              split <;> simp
  | single | double | triple | aromatic | up | down =>
      simp [normalizeUnspecifiedBond]

theorem normalizeUnspecifiedBonds_bondsResolved (molecule : RawMolecule) :
    molecule.normalizeUnspecifiedBonds.BondsResolved := by
  intro bond membership
  rw [normalizeUnspecifiedBonds] at membership
  obtain ⟨original, _originalMembership, rfl⟩ := List.mem_map.mp membership
  exact molecule.normalizeUnspecifiedBond_kind_resolved original

theorem normalizeUnspecifiedBonds_eq_self_of_resolved
    (molecule : RawMolecule) (resolved : molecule.BondsResolved) :
    molecule.normalizeUnspecifiedBonds = molecule := by
  cases molecule with
  | mk atoms bonds neighborOrder introductionPredecessors =>
      simp only [BondsResolved] at resolved
      simp only [normalizeUnspecifiedBonds]
      congr 1
      induction bonds with
      | nil => rfl
      | cons bond rest inductionHypothesis =>
          have headResolved : bond.kind ≠ .unspecified :=
            resolved bond (by simp)
          have tailResolved : ∀ child, child ∈ rest →
              child.kind ≠ .unspecified := by
            intro child member
            exact resolved child (by simp [member])
          simp only [List.map_cons]
          rw [normalizeUnspecifiedBond_eq_self_of_resolved
            ⟨atoms, bond :: rest, neighborOrder, introductionPredecessors⟩ bond headResolved]
          exact congrArg (List.cons bond) (inductionHypothesis tailResolved)

theorem normalizeRawMoleculeCertified?_exists_parsed_eq_of_p94NormalizationReady
    (molecule : RawMolecule) (ready : molecule.P94NormalizationReady) :
    ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeCertified? molecule = some certified ∧
        certified.result.parsed = molecule := by
  rcases ready with ⟨⟨admissible, writtenExact⟩, valence, masses, resolved, introduction⟩
  have fixed := molecule.normalizeUnspecifiedBonds_eq_self_of_resolved resolved
  have admissibleCheck : molecule.admissible? = true :=
    molecule.admissible?_eq_true_iff.mpr admissible
  have writtenCheck : molecule.writtenNeighborExact? = true :=
    molecule.writtenNeighborExact?_eq_true_iff.mpr writtenExact
  have valenceCheck : molecule.valenceOK? = true :=
    molecule.valenceOK?_eq_true_iff.mpr valence
  have massCheck : molecule.rule2MassesKnown? = true :=
    molecule.rule2MassesKnown?_eq_true_iff.mpr masses
  have present : (normalizeRawMoleculeCertified? molecule).isSome = true := by
    simp [normalizeRawMoleculeCertified?, normalizeRawMolecule,
      ChemistryNormalizationResult.certify?, fixed, admissibleCheck, writtenCheck,
      valenceCheck, massCheck, introduction]
  obtain ⟨certified, computed⟩ := Option.isSome_iff_exists.mp present
  refine ⟨certified, computed, ?_⟩
  unfold normalizeRawMoleculeCertified? ChemistryNormalizationResult.certify? at computed
  simp only [normalizeRawMolecule] at computed
  simp [fixed, admissibleCheck, writtenCheck, valenceCheck, massCheck, introduction] at computed
  subst certified
  exact fixed

private theorem certified_result_eq_normalizeRawMolecule
    (molecule : RawMolecule) (certified : CertifiedChemistryNormalizationResult)
    (accepted : normalizeRawMoleculeCertified? molecule = some certified) :
    certified.result = normalizeRawMolecule molecule := by
  have introduction := ChemistryNormalizationResult.certify?_introduction_valid
    (normalizeRawMolecule molecule) certified accepted
  unfold normalizeRawMoleculeCertified? at accepted
  unfold ChemistryNormalizationResult.certify? at accepted
  rw [if_pos introduction] at accepted
  split at accepted <;> simp_all
  rcases accepted with ⟨_writtenExact, _valence, _masses, equality⟩
  subst certified
  rfl

theorem normalizeRawMoleculeCertified?_exists_parsed_eq_iff_p94NormalizationReady
    (molecule : RawMolecule) :
    (∃ certified : CertifiedChemistryNormalizationResult,
      normalizeRawMoleculeCertified? molecule = some certified ∧
        certified.result.parsed = molecule) ↔
      molecule.P94NormalizationReady := by
  constructor
  · rintro ⟨certified, accepted, parsedEq⟩
    have resultEq := certified_result_eq_normalizeRawMolecule molecule certified accepted
    have normalizedEq : certified.result.parsed = molecule.normalizeUnspecifiedBonds := by
      rw [resultEq]
      rfl
    have fixed : molecule.normalizeUnspecifiedBonds = molecule :=
      normalizedEq.symm.trans parsedEq
    have stereochemical : molecule.StereochemicalAdmissible :=
      parsedEq ▸ certified.stereochemicalAdmissible
    have valence : molecule.ValenceOK := parsedEq ▸ certified.valenceOK
    have masses : molecule.Rule2MassesKnown := parsedEq ▸ certified.rule2MassesKnown
    have resolved : molecule.BondsResolved := by
      rw [← fixed]
      exact molecule.normalizeUnspecifiedBonds_bondsResolved
    have introduction := ChemistryNormalizationResult.certify?_introduction_valid
      (normalizeRawMolecule molecule) certified accepted
    change molecule.normalizeUnspecifiedBonds.introductionPredecessorsValid? = true at introduction
    rw [fixed] at introduction
    exact ⟨stereochemical, valence, masses, resolved, introduction⟩
  · exact molecule.normalizeRawMoleculeCertified?_exists_parsed_eq_of_p94NormalizationReady

end RawMolecule
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.normalizeUnspecifiedBonds_eq_self_of_resolved
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.normalizeRawMoleculeCertified?_exists_parsed_eq_of_p94NormalizationReady
assert_kernel_only
  TetraStereo.OneCenter.RawMolecule.normalizeRawMoleculeCertified?_exists_parsed_eq_iff_p94NormalizationReady
