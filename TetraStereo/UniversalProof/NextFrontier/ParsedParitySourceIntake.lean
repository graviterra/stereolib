import TetraStereo.UniversalProof.NextFrontier.FramedParsedParityFamily
import TetraStereo.UniversalProof.NativeOrdinarySourceInput

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000



























namespace TetraStereo.UniversalProof.ParsedParitySourceIntake

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.FramedParsedParityFamily
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement

/-- Fail-closed fallback for `raw`; proved unreachable by `familyMol_eq_some_raw`. -/
def emptyRaw : RawMolecule := { atoms := [], bonds := [], neighborOrder := [] }

/-- The actual parsed molecule of parity member `(c, l, r)`. -/
def raw (center leftArm rightArm : TetrahedralInputParity) : RawMolecule :=
  (familyMol? center leftArm rightArm).getD emptyRaw

/-! ## Actual parse = `some raw` -/

/-- First prerequisite: the actual parser accepts every member and returns exactly `raw`.
This is the concrete `some`-valued strengthening of `family_parse_success` (`isOk = true`),
computed on the actual parser, not on a copied constructor. -/
theorem familyMol_eq_some_raw (center leftArm rightArm : TetrahedralInputParity) :
    familyMol? center leftArm rightArm = some (raw center leftArm rightArm) := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-! ## Exact concrete atoms / bonds / written rows -/

/-- Every member parses to 11 atoms and stores exactly the three chosen written parities at atoms
1 (center), 2 (left arm) and 7 (right arm), read back from the actual parse normal form. -/
theorem raw_structural (center leftArm rightArm : TetrahedralInputParity) :
    ((raw center leftArm rightArm).atomCount,
      ((raw center leftArm rightArm).atomAt? 1).bind (fun spec => spec.tetrahedral?),
      ((raw center leftArm rightArm).atomAt? 2).bind (fun spec => spec.tetrahedral?),
      ((raw center leftArm rightArm).atomAt? 7).bind (fun spec => spec.tetrahedral?)) =
      (11, some center, some leftArm, some rightArm) := by
  simpa [familyMol_eq_some_raw center leftArm rightArm] using
    family_structural center leftArm rightArm

/-- The parsed member has exactly 11 atoms. -/
theorem raw_atom_count (center leftArm rightArm : TetrahedralInputParity) :
    (raw center leftArm rightArm).atomCount = 11 := by
  have h := raw_structural center leftArm rightArm
  exact congrArg (fun t => t.1) h

/-- The actual center (atom 1) carries exactly the chosen center parity. -/
theorem raw_center_parity (center leftArm rightArm : TetrahedralInputParity) :
    ((raw center leftArm rightArm).atomAt? 1).bind (fun spec => spec.tetrahedral?) = some center := by
  have h := raw_structural center leftArm rightArm
  exact congrArg (fun t => t.2.1) h

/-- The actual left arm (atom 2) carries exactly the chosen left parity. -/
theorem raw_left_arm_parity (center leftArm rightArm : TetrahedralInputParity) :
    ((raw center leftArm rightArm).atomAt? 2).bind (fun spec => spec.tetrahedral?) = some leftArm := by
  have h := raw_structural center leftArm rightArm
  exact congrArg (fun t => t.2.2.1) h

/-- The actual right arm (atom 7) carries exactly the chosen right parity. -/
theorem raw_right_arm_parity (center leftArm rightArm : TetrahedralInputParity) :
    ((raw center leftArm rightArm).atomAt? 7).bind (fun spec => spec.tetrahedral?) = some rightArm := by
  have h := raw_structural center leftArm rightArm
  exact congrArg (fun t => t.2.2.2) h

/-! ## OrdinarySourceInput: the four physical fields -/

/-- Every parsed member is well-formed (bond endpoints distinct and in range). -/
theorem raw_well (center leftArm rightArm : TetrahedralInputParity) :
    (raw center leftArm rightArm).WellFormed :=
  (wellFormed_iff_all_bondEndpointsOK (raw center leftArm rightArm)).mpr (by
    cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel)

/-- Every parsed member has an exact written-neighbour view. -/
theorem raw_written (center leftArm rightArm : TetrahedralInputParity) :
    (raw center leftArm rightArm).WrittenNeighborExact :=
  (raw center leftArm rightArm).writtenNeighborExact?_eq_true_iff.mp (by
    cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel)

/-- Every atom of every parsed member is a known (non-wildcard) element. -/
theorem raw_known (center leftArm rightArm : TetrahedralInputParity) :
    ∀ spec ∈ (raw center leftArm rightArm).atoms, spec.element ≠ .wildcard := by
  have allKnown :
      (raw center leftArm rightArm).atoms.all (fun spec => decide (spec.element ≠ .wildcard)) = true := by
    cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel
  intro spec hmem
  exact of_decide_eq_true ((List.all_eq_true.mp allKnown) spec hmem)

/-- Every bond of every parsed member is a single bond. -/
theorem raw_single (center leftArm rightArm : TetrahedralInputParity) :
    ∀ bond ∈ (raw center leftArm rightArm).bonds, bond.kind = .single := by
  have allSingle :
      (raw center leftArm rightArm).bonds.all (fun bond => decide (bond.kind = .single)) = true := by
    cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel
  intro bond hmem
  exact of_decide_eq_true ((List.all_eq_true.mp allSingle) bond hmem)

/-- The complete ordinary source-input record for every parsed member, all four fields. -/
theorem raw_ordinary_source_input (center leftArm rightArm : TetrahedralInputParity) :
    OrdinarySourceInput (raw center leftArm rightArm) :=
  { well := raw_well center leftArm rightArm
    written := raw_written center leftArm rightArm
    known := raw_known center leftArm rightArm
    single := raw_single center leftArm rightArm }

/-- Every parsed member satisfies the lightweight valence table. -/
theorem raw_valence (center leftArm rightArm : TetrahedralInputParity) :
    (raw center leftArm rightArm).ValenceOK :=
  (raw center leftArm rightArm).valenceOK?_eq_true_iff.mp (by
    cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel)

/-! ## Actual written neighbour rows (center and arms) -/

/-- Centers 1, 2 and 7 each have exactly four written neighbours. -/
theorem raw_written_degree (center leftArm rightArm : TetrahedralInputParity) :
    ((raw center leftArm rightArm).writtenNeighbors 1).length = 4 ∧
    ((raw center leftArm rightArm).writtenNeighbors 2).length = 4 ∧
    ((raw center leftArm rightArm).writtenNeighbors 7).length = 4 := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-- The two tagged arms (atoms 2 and 7) are actual written neighbours of the center (atom 1). -/
theorem raw_center_arms_neighbors (center leftArm rightArm : TetrahedralInputParity) :
    2 ∈ (raw center leftArm rightArm).writtenNeighbors 1 ∧
    7 ∈ (raw center leftArm rightArm).writtenNeighbors 1 := by
  cases center <;> cases leftArm <;> cases rightArm <;> decide +kernel

/-! ## Converter instantiations at the actual parsed molecule -/

/-- The existing parser-to-source conversion holds at every parsed member. -/
theorem family_source_conversion (center leftArm rightArm : TetrahedralInputParity) :
    (raw center leftArm rightArm).toAuthoritativeChemicalInput? =
      some (ownSource (raw center leftArm rightArm)) :=
  actual_source_conversion (raw center leftArm rightArm)
    (raw_ordinary_source_input center leftArm rightArm)

/-- Structural agreement between the parsed member and its source record. -/
theorem family_structure_agreement (center leftArm rightArm : TetrahedralInputParity) :
    (raw center leftArm rightArm).AuthoritativeStructureAgreement
      (ownSource (raw center leftArm rightArm)) :=
  actual_structure_agreement (raw center leftArm rightArm)
    (raw_ordinary_source_input center leftArm rightArm)

/-- Annotation agreement between the parsed member and its source record. -/
theorem family_annotation_agreement (center leftArm rightArm : TetrahedralInputParity) :
    RawAnnotationAgreement (raw center leftArm rightArm)
      (ownSource (raw center leftArm rightArm)) :=
  actual_annotation_agreement (raw center leftArm rightArm)
    (raw_ordinary_source_input center leftArm rightArm)

/-- The parser-only converter introduces no second spatial evidence channel. -/
theorem family_source_no_spatial (center leftArm rightArm : TetrahedralInputParity) :
    (ownSource (raw center leftArm rightArm)).spatial? = none :=
  actual_source_no_spatial (raw center leftArm rightArm)


theorem family_annotation_audit_nil (center leftArm rightArm : TetrahedralInputParity) :
    rawAnnotationAgreementIssues (raw center leftArm rightArm)
      (ownSource (raw center leftArm rightArm)) = [] :=
  actual_annotation_audit_nil (raw center leftArm rightArm)
    (raw_ordinary_source_input center leftArm rightArm)

end TetraStereo.UniversalProof.ParsedParitySourceIntake
