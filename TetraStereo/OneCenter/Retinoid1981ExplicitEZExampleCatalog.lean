import TetraStereo.OneCenter.Retinoid1981StereoparentTableAuthorityInput
import TetraStereo.KernelOnly

set_option autoImplicit false
















namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace ExplicitEZExampleCatalog

open FigureGraphTranscription
open StereoparentTableAuthorityInput

inductive ExplicitEZExample where
  | ethylRetinoate
  | fluororetinoate
  | cisRetinol
  | cisRetinoicAcid
  | retroRetinalOxime
  | retroRetinylAcetate
  deriving DecidableEq, Repr

/-- Literal Ret-5.2 order: compound (9), fluorinated example, the two 13-cis examples, oxime,
then the retro-retinyl-acetate clarification. -/
def explicitEZExamples : List ExplicitEZExample :=
  [ .ethylRetinoate
  , .fluororetinoate
  , .cisRetinol
  , .cisRetinoicAcid
  , .retroRetinalOxime
  , .retroRetinylAcetate ]

def graphFor : ExplicitEZExample → HeavyAtomGraph
  | .ethylRetinoate => ethylRetinoateGraph
  | .fluororetinoate => fluororetinoateGraph
  | .cisRetinol => cisRetinolGraph
  | .cisRetinoicAcid => cisRetinoicAcidGraph
  | .retroRetinalOxime => retroRetinalOximeGraph
  | .retroRetinylAcetate => retroRetinylAcetateGraph

private def stripParentGeometry
    (claims : List DoubleBondConfigurationClaim) : List EZConfigurationClaim :=
  claims.map fun claim => ⟨claim.low, claim.high, claim.ez⟩

def claimsFor : ExplicitEZExample → List EZConfigurationClaim
  | .ethylRetinoate =>
      [ ⟨7, 8, .E⟩, ⟨9, 10, .E⟩, ⟨11, 12, .E⟩, ⟨13, 14, .E⟩ ]
  | .fluororetinoate => stripParentGeometry fluororetinoateConfigurationClaims
  | .cisRetinol => stripParentGeometry cisRetinoidConfigurationClaims
  | .cisRetinoicAcid => stripParentGeometry cisRetinoidConfigurationClaims
  | .retroRetinalOxime => retroRetinalOximeConfigurationClaims
  | .retroRetinylAcetate =>
      [ ⟨6, 7, .Z⟩, ⟨8, 9, .E⟩, ⟨10, 11, .E⟩, ⟨12, 13, .E⟩ ]

@[simp] theorem ethyl_retinoate_all_E_exact :
    claimsFor .ethylRetinoate =
      [ ⟨7, 8, .E⟩, ⟨9, 10, .E⟩, ⟨11, 12, .E⟩, ⟨13, 14, .E⟩ ] := by
  rfl

@[simp] theorem retro_retinyl_acetate_EZ_exact :
    claimsFor .retroRetinylAcetate =
      [ ⟨6, 7, .Z⟩, ⟨8, 9, .E⟩, ⟨10, 11, .E⟩, ⟨12, 13, .E⟩ ] := by
  rfl

structure ExplicitEZExampleEntry where
  sourceExample : ExplicitEZExample
  graph : HeavyAtomGraph
  claims : List EZConfigurationClaim
  deriving DecidableEq, Repr

def explicitEZExampleEntries : List ExplicitEZExampleEntry :=
  explicitEZExamples.map fun sourceExample =>
    ⟨sourceExample, graphFor sourceExample, claimsFor sourceExample⟩

@[simp] theorem explicit_ez_example_entry_count :
    explicitEZExampleEntries.length = 6 := by
  decide

@[simp] theorem explicit_ez_example_claim_counts_exact :
    explicitEZExampleEntries.map (fun entry => entry.claims.length) =
      [4, 4, 4, 4, 5, 4] := by
  decide

def explicitEZClaimLedger : List (ExplicitEZExample × Nat × Nat × EZ) :=
  explicitEZExampleEntries.flatMap fun entry =>
    entry.claims.map fun claim =>
      (entry.sourceExample, claim.low, claim.high, claim.ez)

@[simp] theorem explicit_ez_claim_ledger_count :
    explicitEZClaimLedger.length = 25 := by
  decide

def claimsAcceptedByGraph?
    (graph : HeavyAtomGraph) (claims : List EZConfigurationClaim) : Bool :=
  claims.all fun claim =>
    (doubleBondEdges graph).contains (claim.low, claim.high)

@[simp] theorem claimsAcceptedByGraph?_eq_true_iff
    (graph : HeavyAtomGraph) (claims : List EZConfigurationClaim) :
    claimsAcceptedByGraph? graph claims = true ↔
      EZConfigurationClaimsWellFormed graph claims := by
  rfl

@[simp] theorem explicit_ez_example_claims_all_accepted :
    explicitEZExampleEntries.all
      (fun entry => claimsAcceptedByGraph? entry.graph entry.claims) = true := by
  decide

theorem explicit_ez_example_claims_wellFormed
    (entry : ExplicitEZExampleEntry) (member : entry ∈ explicitEZExampleEntries) :
    EZConfigurationClaimsWellFormed entry.graph entry.claims := by
  apply (claimsAcceptedByGraph?_eq_true_iff entry.graph entry.claims).mp
  exact (List.all_eq_true.mp explicit_ez_example_claims_all_accepted) entry member

end ExplicitEZExampleCatalog
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitEZExampleCatalog.ethyl_retinoate_all_E_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitEZExampleCatalog.retro_retinyl_acetate_EZ_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitEZExampleCatalog.explicit_ez_example_claim_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitEZExampleCatalog.explicit_ez_claim_ledger_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitEZExampleCatalog.explicit_ez_example_claims_all_accepted
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitEZExampleCatalog.explicit_ez_example_claims_wellFormed
