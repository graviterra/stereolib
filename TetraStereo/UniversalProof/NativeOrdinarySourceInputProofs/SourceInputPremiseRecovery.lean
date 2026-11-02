import TetraStereo.UniversalProof.NativeOrdinarySourceInput
import TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment
import TetraStereo.OneCenter.AuthoritativeSemanticTetrahedralElementApplicability
import TetraStereo.OneCenter.AuthoritativeSemanticParserDiagramRule3Through6Analysis

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
open TetraStereo.UniversalProof.NonleafSourceParserAlignmentProofs.NonleafSourceParserAlignment










-- OrdinarySourceInput is re-exported from NativeOrdinarySourceInput.



-- ownSource is re-exported from NativeOrdinarySourceInput.


-- actual_source_conversion is re-exported from NativeOrdinarySourceInput.


-- actual_structure_agreement is re-exported from NativeOrdinarySourceInput.



-- actual_source_no_spatial is re-exported from NativeOrdinarySourceInput.


private theorem filterMap_nil_of_none {Alpha Beta : Type*} (values : List Alpha)
    (f : Alpha → Option Beta) (absent : ∀ value ∈ values, f value = none) :
    values.filterMap f = [] := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have head := absent first (by simp)
      have tail : ∀ value ∈ rest, f value = none := by
        intro value retained
        exact absent value (List.mem_cons_of_mem first retained)
      simp only [List.filterMap_cons, head]
      exact ih tail

private theorem enumerateFrom_member_lookup {Alpha : Type*} (values : List Alpha)
    (start : Nat) (indexed : Nat × Alpha) (retained : indexed ∈ enumerateFrom start values) :
    ∃ offset, indexed.1 = start + offset ∧ listGet? values offset = some indexed.2 := by
  induction values generalizing start with
  | nil => simp [enumerateFrom] at retained
  | cons first rest ih =>
      simp only [enumerateFrom, List.mem_cons] at retained
      rcases retained with equal | retained
      · subst indexed
        exact ⟨0, by simp, rfl⟩
      · obtain ⟨offset, indexEq, lookup⟩ := ih (start + 1) retained
        exact ⟨offset + 1, by omega, by simpa [listGet?] using lookup⟩

-- enumerate_member_lookup is re-exported from NativeOrdinarySourceInput.



-- copied_diagram_annotation_reflects is re-exported from NativeOrdinarySourceInput.



-- raw_annotation_has_copied_diagram is re-exported from NativeOrdinarySourceInput.


-- actual_raw_directions_nil is re-exported from NativeOrdinarySourceInput.


-- actual_copied_diagram_bonds_nil is re-exported from NativeOrdinarySourceInput.



-- structure_agreement_record_agreement is re-exported from NativeOrdinarySourceInput.


-- actual_annotation_agreement is re-exported from NativeOrdinarySourceInput.


-- actual_annotation_audit_nil is re-exported from NativeOrdinarySourceInput.



-- actual_source_no_double is re-exported from NativeOrdinarySourceInput.


-- actual_resolved_records is re-exported from NativeOrdinarySourceInput.



-- actualCenter is re-exported from NativeOrdinarySourceInput.


-- actualCenter_index is re-exported from NativeOrdinarySourceInput.


/-- Discharge together the independent source-input premises consumed by 171 and the proposed
whole-discovery own-model adapter. No desired source/model/output result is a premise. -/
theorem actual_source_input_premises (raw : RawMolecule) (input : OrdinarySourceInput raw)
    (atom : Fin raw.atomCount) (domain : AtomicCenterDomain raw atom.val)
    (spec : AtomSpec) (observed : raw.atomAt? atom.val = some spec)
    (eligible : BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element)
    (four : (raw.writtenNeighbors atom.val).length = 4) :
    RawAnnotationAgreement raw (ownSource raw) ∧
      (ownSource raw).NoAromaticCanonicalOrdinaryDoubleBond ∧
      ∃ center : (ownSource raw).AromaticCanonicalTetrahedralCenter,
        center.1.val = atom.val ∧ SourceAtomicDomain raw center.1.val := by
  refine ⟨actual_annotation_agreement raw input, actual_source_no_double raw input,
    actualCenter raw input atom spec observed eligible four, rfl, ?_⟩
  exact ⟨domain, fun bond retained _ => input.single bond retained⟩

/-- One internally constructed source handles every observed tag, without OnlyCenterTagged or
an existential caller-supplied model. The hypothesis observes independent first-Z/element/degree
facts on raw records; no successful conversion, source center, agreement or label is an input. -/
theorem actual_all_tag_source_premises (raw : RawMolecule) (input : OrdinarySourceInput raw)
    (physicalTags : ∀ index spec parity, raw.atomAt? index = some spec →
      spec.tetrahedral? = some parity →
      AtomicCenterDomain raw index ∧
        BlueBookP92.Perception.ConnectivityOnlyTetrahedralElement spec.element ∧
          (raw.writtenNeighbors index).length = 4) :
    RawAnnotationAgreement raw (ownSource raw) ∧
      (ownSource raw).NoAromaticCanonicalOrdinaryDoubleBond ∧
      (ownSource raw).spatial? = none ∧
      ∀ index spec parity, raw.atomAt? index = some spec → spec.tetrahedral? = some parity →
        ∃ center : (ownSource raw).AromaticCanonicalTetrahedralCenter,
          center.1.val = index ∧ SourceAtomicDomain raw center.1.val := by
  refine ⟨actual_annotation_agreement raw input, actual_source_no_double raw input,
    actual_source_no_spatial raw, ?_⟩
  intro index spec parity observed tagged
  obtain ⟨domain, eligible, four⟩ := physicalTags index spec parity observed tagged
  exact (actual_source_input_premises raw input ⟨index, domain.centerBound⟩
    domain spec observed eligible four).2.2

end TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
