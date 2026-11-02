import TetraStereo.UniversalProof.NextFrontier.NativeNitrileParserPublic
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileValence
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileWrittenNeighbors

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

theorem raw_normalized_parsed (parity : TetrahedralInputParity) (n : Nat) :
    (normalizeRawMolecule (raw parity n)).parsed = raw parity n :=
  raw_normalization_identity parity n

/-- A concrete structural chemistry certificate, constructed from the independent family. -/
def rawCertified (parity : TetrahedralInputParity) (n : Nat) :
    CertifiedChemistryNormalizationResult where
  result := normalizeRawMolecule (raw parity n)
  admissible := by rw [raw_normalized_parsed]; exact raw_admissible parity n
  writtenNeighborExact := by rw [raw_normalized_parsed]; exact raw_written_exact parity n
  valenceOK := by rw [raw_normalized_parsed]; exact raw_valence_ok parity n
  rule2MassesKnown := by rw [raw_normalized_parsed]; exact raw_rule2_masses_known parity n

@[simp] theorem rawCertified_parsed (parity : TetrahedralInputParity) (n : Nat) :
    (rawCertified parity n).result.parsed = raw parity n :=
  raw_normalized_parsed parity n

/-- Actual checked intake returns the internally constructed certificate, for every chain length.
The provenance guard is discharged from the physical introduction table. -/
theorem actual_certified_raw_intake (parity : TetrahedralInputParity) (n : Nat) :
    normalizeRawMoleculeCertified? (raw parity n) = some (rawCertified parity n) := by
  have admissibleCheck : (normalizeRawMolecule (raw parity n)).parsed.admissible? = true := by
    rw [raw_normalized_parsed]
    exact (admissible?_eq_true_iff _).mpr (raw_admissible parity n)
  have writtenCheck :
      (normalizeRawMolecule (raw parity n)).parsed.writtenNeighborExact? = true := by
    rw [raw_normalized_parsed]
    exact (writtenNeighborExact?_eq_true_iff _).mpr (raw_written_exact parity n)
  have valenceCheck : (normalizeRawMolecule (raw parity n)).parsed.valenceOK? = true := by
    rw [raw_normalized_parsed]
    exact (valenceOK?_eq_true_iff _).mpr (raw_valence_ok parity n)
  have massCheck : (normalizeRawMolecule (raw parity n)).parsed.rule2MassesKnown? = true := by
    rw [raw_normalized_parsed]
    exact (rule2MassesKnown?_eq_true_iff _).mpr (raw_rule2_masses_known parity n)
  have introductionCheck :
      (normalizeRawMolecule (raw parity n)).parsed.introductionPredecessorsValid? = true := by
    rw [raw_normalized_parsed]
    exact raw_introduction_valid parity n
  unfold normalizeRawMoleculeCertified? ChemistryNormalizationResult.certify? rawCertified
  rw [if_pos introductionCheck, dif_pos admissibleCheck, dif_pos writtenCheck,
    dif_pos valenceCheck, dif_pos massCheck]

/-- Both annotated parities and every natural chain extension pass the actual parser and checked
chemistry intake. No parse-success, model, descriptor or normalization hypothesis is supplied. -/
theorem actual_certified_parse (parity : TetrahedralInputParity) (n : Nat) :
    parseAndNormalizeOpenSMILESCertified (smiles parity n) = .ok (rawCertified parity n) := by
  unfold parseAndNormalizeOpenSMILESCertified parseAndNormalizeOpenSMILES
  rw [actual_parse]
  change (match normalizeRawMoleculeCertified? (raw parity n) with
    | some certified => Except.ok certified
    | none => Except.error _) = _
  rw [actual_certified_raw_intake]

theorem actual_certified_expansion (parity : TetrahedralInputParity) (n : Nat) :
    (rawCertified parity n).result.parsed.withExplicitHydrogens = expanded parity n := by
  rw [rawCertified_parsed]
  rfl

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
