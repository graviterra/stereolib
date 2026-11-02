import TetraStereo.OneCenter.Retinoid1981ExplicitEZExampleCatalog
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Ret-2 table polyene configuration

The Ret-2 table shares the A2a stereoparent skeleton, and Ret-5.2 states that its polyene chain is
trans at all four chain double bonds unless a contrary configuration is indicated. This module
compiles that inherited configuration across the exact ten-row table graph batch. The terminal
groups differ, but none changes the four A2a chain bonds or their E labels.

Structure (9) is independently described in Ret-5.2 as ethyl (all-E)-retinoate, so its compiled
claim list is reconciled exactly with the explicit-example catalog rather than accepted only from
the family default.
-/

namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace StereoparentTablePolyeneConfiguration

open FigureGraphTranscription
open StereoparentTableAuthorityInput
open ExplicitEZExampleCatalog

def inheritedAllTransPolyeneClaims : List DoubleBondConfigurationClaim :=
  [ ⟨7, 8, .trans, .E⟩
  , ⟨9, 10, .trans, .E⟩
  , ⟨11, 12, .trans, .E⟩
  , ⟨13, 14, .trans, .E⟩ ]

structure ConfiguredStereoparentTableEntry where
  row : SourceAudit.Ledger.StereoparentSubstituentRow
  graph : HeavyAtomGraph
  claims : List DoubleBondConfigurationClaim
  deriving DecidableEq, Repr

def ConfiguredStereoparentTableEntry.ezClaims
    (entry : ConfiguredStereoparentTableEntry) : List EZConfigurationClaim :=
  entry.claims.map fun claim => ⟨claim.low, claim.high, claim.ez⟩

def configuredStereoparentTableEntries : List ConfiguredStereoparentTableEntry :=
  stereoparentTableGraphEntries.map fun entry =>
    ⟨entry.row, entry.graph, inheritedAllTransPolyeneClaims⟩

@[simp] theorem configured_stereoparent_table_entry_count :
    configuredStereoparentTableEntries.length = 10 := by
  decide

@[simp] theorem configured_stereoparent_table_claim_counts_exact :
    configuredStereoparentTableEntries.map (fun entry => entry.claims.length) =
      [4, 4, 4, 4, 4, 4, 4, 4, 4, 4] := by
  decide

def stereoparentTablePolyeneClaimLedger : List DoubleBondConfigurationClaim :=
  configuredStereoparentTableEntries.flatMap fun entry => entry.claims

@[simp] theorem stereoparent_table_polyene_claim_ledger_count :
    stereoparentTablePolyeneClaimLedger.length = 40 := by
  decide

@[simp] theorem stereoparent_table_parent_geometry_all_trans :
    stereoparentTablePolyeneClaimLedger.all
      (fun claim => claim.parentGeometry == .trans) = true := by
  decide

@[simp] theorem stereoparent_table_EZ_all_E :
    stereoparentTablePolyeneClaimLedger.all (fun claim => claim.ez == .E) = true := by
  decide

@[simp] theorem configured_stereoparent_table_claims_all_accepted :
    configuredStereoparentTableEntries.all
      (fun entry => claimsAcceptedByGraph? entry.graph entry.ezClaims) = true := by
  decide

def structureNineEZClaims : List EZConfigurationClaim :=
  inheritedAllTransPolyeneClaims.map fun claim =>
    ⟨claim.low, claim.high, claim.ez⟩

@[simp] theorem structure_nine_claims_match_explicit_all_E_example :
    structureNineEZClaims = claimsFor .ethylRetinoate := by
  rfl

theorem configured_stereoparent_table_claims_wellFormed
    (entry : ConfiguredStereoparentTableEntry)
    (member : entry ∈ configuredStereoparentTableEntries) :
    DoubleBondConfigurationClaimsWellFormed entry.graph entry.claims := by
  have accepted :=
    (List.all_eq_true.mp configured_stereoparent_table_claims_all_accepted) entry member
  simpa [claimsAcceptedByGraph?, ConfiguredStereoparentTableEntry.ezClaims,
    DoubleBondConfigurationClaimsWellFormed] using accepted

end StereoparentTablePolyeneConfiguration
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTablePolyeneConfiguration.configured_stereoparent_table_claim_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTablePolyeneConfiguration.stereoparent_table_polyene_claim_ledger_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTablePolyeneConfiguration.stereoparent_table_parent_geometry_all_trans
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTablePolyeneConfiguration.stereoparent_table_EZ_all_E
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTablePolyeneConfiguration.configured_stereoparent_table_claims_all_accepted
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTablePolyeneConfiguration.structure_nine_claims_match_explicit_all_E_example
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.StereoparentTablePolyeneConfiguration.configured_stereoparent_table_claims_wellFormed
