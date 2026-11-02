import TetraStereo.OneCenter.OfficialSystemBranchPerception

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace OfficialSystemBranchPerception

open OneCenter

example
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : OneCenter.MultiCenterMolecule V) (left right : m.Center)
    (hsource : right ≠ left) :
    let env : OfficialDescriptorEnvironment m.Center :=
      ((OfficialDescriptorEnvironment.empty.assign left
        (OfficialDescriptorValue.rule5Descriptor OfficialRule5Descriptor.descriptorR)).assign
          right
          (OfficialDescriptorValue.rule5Descriptor OfficialRule5Descriptor.descriptorS))
    let leftSource : BranchEnvironmentSource m m.Center := { source := left, unit := left }
    let rightSource : BranchEnvironmentSource m m.Center := { source := right, unit := right }
    (officialContextOfEnvironmentSources env [leftSource, rightSource]).rule4bPair? =
      some OfficialDescriptorPairKind.unlike := by
  intro env leftSource rightSource
  have hleft : env.rule5Descriptor leftSource.unit =
      some OfficialRule5Descriptor.descriptorR := by
    simp [env, leftSource, OfficialDescriptorEnvironment.assign, hsource.symm]
  have hright : env.rule5Descriptor rightSource.unit =
      some OfficialRule5Descriptor.descriptorS := by
    simp [env, rightSource, OfficialDescriptorEnvironment.assign]
  have hctx :=
    officialContextOfEnvironmentSources_rule4bPair?_of_two_distinct_rule5
      (env := env) (left := leftSource) (right := rightSource) (rest := [])
      hsource hleft hright
  simpa [OfficialRule5Descriptor.pairKind_R_S] using hctx

example
    {V Unit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Unit]
    (m : OneCenter.MultiCenterMolecule V) (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit) {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel) (center : m.Center) (i : Fin 4) :
    m.officialBranchContextFromDetectorWithin output unitsAtCenter
        (scheduleFuel + 1) branchFuel center i =
      m.officialBranchContextFromDetectorWithin output unitsAtCenter
        scheduleFuel branchFuel center i := by
  exact m.officialBranchContextFromDetectorWithin_succ_eq_of_fixedAt output unitsAtCenter
    branchFuel h center i

example
    {V Unit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Unit]
    (m : OneCenter.MultiCenterMolecule V) (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit) {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel) (center : m.Center) (i j : Fin 4) :
    m.cipOfficialCompareAtFromBranchDetectorWithin output unitsAtCenter
        (scheduleFuel + 1) branchFuel center i j =
      m.cipOfficialCompareAtFromBranchDetectorWithin output unitsAtCenter
        scheduleFuel branchFuel center i j := by
  exact m.cipOfficialCompareAtFromBranchDetectorWithin_succ_eq_of_fixedAt output unitsAtCenter
    branchFuel h center i j

end OfficialSystemBranchPerception
end Examples
end TetraStereo
