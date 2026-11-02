import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSteroidSourceMeaningBatch
import TetraStereo.KernelOnly

set_option autoImplicit false



























namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace GlobalNonDescriptorSteroidSourceMeaning

open GlobalNonDescriptorSourceMeaningConstructor

/-! ## Frozen Table 1 note (2) observations -/

/-- Table 1 note (2): the three additional methyl groups of a trimethyl steroid are numbered
28 (attached to C-4 with α-configuration), 29 (attached to C-4 with β-configuration) and
30 (attached to C-14). -/
def table1TrimethylAdditionalMethylLocants : List Nat := [28, 29, 30]

/-- Table 1 note (2): the implied C-9 configuration of the named cycloartane parent is β.

This is the named-parent value only.  The generic `Steroid1989.impliedCoreFace 9` remains α. -/
def table1CycloartaneImpliedC9 : Steroid1989.LocatedFace := ⟨9, .beta⟩

/-! ## Actual assertion producer -/

theorem trimethyl_sourceAssertion_exact :
    sourceAssertion .trimethylSteroidConfigurationNumbering =
      .trimethylSteroidConfigurationNumbering table1TrimethylAdditionalMethylLocants := rfl

theorem trimethyl_sourceAssertion_locants_exact :
    sourceAssertion .trimethylSteroidConfigurationNumbering =
      .trimethylSteroidConfigurationNumbering [28, 29, 30] := rfl

theorem cycloartane_sourceAssertion_exact :
    sourceAssertion .cycloartaneC9ConfigurationImplication =
      .cycloartaneC9ConfigurationImplication table1CycloartaneImpliedC9 := rfl

theorem cycloartane_sourceAssertion_face_exact :
    sourceAssertion .cycloartaneC9ConfigurationImplication =
      .cycloartaneC9ConfigurationImplication ⟨9, .beta⟩ := rfl

/-! ## Actual family-batch consumer -/

theorem trimethyl_sourceMeaning_exact :
    (sourceMeaning .trimethylSteroidConfigurationNumbering).assertion =
      .trimethylSteroidConfigurationNumbering [28, 29, 30] := rfl

theorem cycloartane_sourceMeaning_exact :
    (sourceMeaning .cycloartaneC9ConfigurationImplication).assertion =
      .cycloartaneC9ConfigurationImplication ⟨9, .beta⟩ := rfl

/-- The family batch is compiled from exactly the `sourceMeaning` function pinned above; the
corrected payloads are therefore the ones the batch carries, not a second transcription. -/
theorem batch_entries_factor_through_sourceMeaning :
    batch.entries =
      rows.map (fun row =>
        rowResultEntry (IUPACNormativeProvision.steroid1989 row) row sourceMeaning) := rfl

/-! ## Generic steroid default versus named cycloartane parent -/

/-- The generic steroid implied core retains 9α. -/
theorem generic_impliedCoreFace9_alpha :
    Steroid1989.impliedCoreFace 9 = some .alpha := rfl

/-- The batch-level generic implied bridgehead list also retains 9α. -/
theorem generic_bridgehead_list_contains_9alpha :
    (⟨9, .alpha⟩ : Steroid1989.LocatedFace) ∈ impliedBridgeheadFaces := by decide

/-- The generic rule and the named parent remain distinct: the core default is 9α, while the
cycloartane assertion carries 9β. -/
theorem generic_core_9alpha_versus_named_cycloartane_9beta :
    Steroid1989.impliedCoreFace 9 = some .alpha ∧
      table1CycloartaneImpliedC9 = (⟨9, .beta⟩ : Steroid1989.LocatedFace) ∧
        (⟨9, .alpha⟩ : Steroid1989.LocatedFace) ≠ table1CycloartaneImpliedC9 :=
  ⟨rfl, rfl, by decide⟩

/-- The generic core face and the named cycloartane payload select different faces at C-9. -/
theorem generic_core_face9_differs_from_cycloartane_payload :
    Steroid1989.impliedCoreFace 9 ≠ some table1CycloartaneImpliedC9.face := by
  decide

/-! ## Reversion guards -/

/-- The trimethyl payload is not the Table 1 side-chain locant set. -/
theorem trimethyl_payload_is_not_side_chain_locants :
    sourceAssertion .trimethylSteroidConfigurationNumbering ≠
      .trimethylSteroidConfigurationNumbering [20, 22, 23, 24] := by decide

/-- The named cycloartane payload is not the generic α default. -/
theorem cycloartane_payload_is_not_generic_alpha :
    sourceAssertion .cycloartaneC9ConfigurationImplication ≠
      .cycloartaneC9ConfigurationImplication ⟨9, .alpha⟩ := by decide

/-- Consumer-level reversion guard: the batch-facing `sourceMeaning` payload is not the
side-chain locant set. -/
theorem trimethyl_sourceMeaning_is_not_side_chain_locants :
    (sourceMeaning .trimethylSteroidConfigurationNumbering).assertion ≠
      .trimethylSteroidConfigurationNumbering [20, 22, 23, 24] := by decide

/-- Consumer-level reversion guard: the batch-facing `sourceMeaning` payload is not 9α. -/
theorem cycloartane_sourceMeaning_is_not_generic_alpha :
    (sourceMeaning .cycloartaneC9ConfigurationImplication).assertion ≠
      .cycloartaneC9ConfigurationImplication ⟨9, .alpha⟩ := by decide

end GlobalNonDescriptorSteroidSourceMeaning
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.trimethyl_sourceAssertion_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.trimethyl_sourceAssertion_locants_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.cycloartane_sourceAssertion_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.cycloartane_sourceAssertion_face_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.trimethyl_sourceMeaning_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.cycloartane_sourceMeaning_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.batch_entries_factor_through_sourceMeaning
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.generic_impliedCoreFace9_alpha
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.generic_bridgehead_list_contains_9alpha
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.generic_core_9alpha_versus_named_cycloartane_9beta
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.generic_core_face9_differs_from_cycloartane_payload
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.trimethyl_payload_is_not_side_chain_locants
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.cycloartane_payload_is_not_generic_alpha
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.trimethyl_sourceMeaning_is_not_side_chain_locants
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSteroidSourceMeaning.cycloartane_sourceMeaning_is_not_generic_alpha
