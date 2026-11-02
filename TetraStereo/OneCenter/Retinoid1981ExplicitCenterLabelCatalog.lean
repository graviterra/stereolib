import TetraStereo.OneCenter.Retinoid1981StereoparentTablePolyeneConfiguration
import TetraStereo.KernelOnly

set_option autoImplicit false














namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace ExplicitCenterLabelCatalog

open FigureGraphTranscription
open FigureAuthorityInput
open StereoparentTableAuthorityInput

inductive AbsoluteSeries where
  | D
  | L
  deriving DecidableEq, Repr

inductive AnomericDescriptor where
  | alpha
  | beta
  deriving DecidableEq, Repr

inductive SourceCenterLabel where
  | rs (descriptor : RS)
  | aminoAcidSeries (series : AbsoluteSeries)
  | carbohydrateSeries (series : AbsoluteSeries)
  | anomer (descriptor : AnomericDescriptor)
  deriving DecidableEq, Repr

structure LocatedSourceCenterLabel where
  atomId : Nat
  label : SourceCenterLabel
  deriving DecidableEq, Repr

inductive ExplicitCenterLabelExample where
  | retinylideneLLysine
  | retinoylBetaDGlucopyranuronate
  | hydroxyRetinol3R
  | acetoxyRetinol3R
  deriving DecidableEq, Repr

/-- Literal source order: structures (8), (10), then the two Ret-5.1 examples. -/
def explicitCenterLabelExamples : List ExplicitCenterLabelExample :=
  [ .retinylideneLLysine
  , .retinoylBetaDGlucopyranuronate
  , .hydroxyRetinol3R
  , .acetoxyRetinol3R ]

def graphFor : ExplicitCenterLabelExample → HeavyAtomGraph
  | .retinylideneLLysine => lysylIminomethylGraph
  | .retinoylBetaDGlucopyranuronate => retinoylGlucuronideGraph
  | .hydroxyRetinol3R => hydroxyRetinolGraph
  | .acetoxyRetinol3R => acetoxyRetinolGraph

def claimsFor : ExplicitCenterLabelExample → List LocatedSourceCenterLabel
  | .retinylideneLLysine => [⟨26, .aminoAcidSeries .L⟩]
  | .retinoylBetaDGlucopyranuronate =>
      [⟨21, .anomer .beta⟩, ⟨25, .carbohydrateSeries .D⟩]
  | .hydroxyRetinol3R => [⟨3, .rs .R⟩]
  | .acetoxyRetinol3R => [⟨3, .rs .R⟩]

@[simp] theorem retinylidene_L_lysine_claim_exact :
    claimsFor .retinylideneLLysine = [⟨26, .aminoAcidSeries .L⟩] := by
  rfl

@[simp] theorem retinoyl_beta_D_glucopyranuronate_claims_exact :
    claimsFor .retinoylBetaDGlucopyranuronate =
      [⟨21, .anomer .beta⟩, ⟨25, .carbohydrateSeries .D⟩] := by
  rfl

@[simp] theorem glucopyranuronate_stereo_anchors_follow_A2b_embedding :
    retinoylGlucuronideSourceNodeMap.contains (1, 21) = true ∧
      retinoylGlucuronideSourceNodeMap.contains (5, 25) = true := by
  decide

@[simp] theorem hydroxy_acetoxy_3R_claims_exact :
    claimsFor .hydroxyRetinol3R = [⟨3, .rs .R⟩] ∧
      claimsFor .acetoxyRetinol3R = [⟨3, .rs .R⟩] := by
  decide

structure ExplicitCenterLabelEntry where
  sourceExample : ExplicitCenterLabelExample
  graph : HeavyAtomGraph
  claims : List LocatedSourceCenterLabel
  deriving DecidableEq, Repr

def explicitCenterLabelEntries : List ExplicitCenterLabelEntry :=
  explicitCenterLabelExamples.map fun sourceExample =>
    ⟨sourceExample, graphFor sourceExample, claimsFor sourceExample⟩

@[simp] theorem explicit_center_label_claim_counts_exact :
    explicitCenterLabelEntries.map (fun entry => entry.claims.length) = [1, 2, 1, 1] := by
  decide

def explicitCenterLabelLedger :
    List (ExplicitCenterLabelExample × Nat × SourceCenterLabel) :=
  explicitCenterLabelEntries.flatMap fun entry =>
    entry.claims.map fun claim =>
      (entry.sourceExample, claim.atomId, claim.label)

@[simp] theorem explicit_center_label_ledger_count :
    explicitCenterLabelLedger.length = 5 := by
  decide

def centerLabelsAcceptedByGraph?
    (graph : HeavyAtomGraph) (claims : List LocatedSourceCenterLabel) : Bool :=
  claims.all fun claim => graph.locants.contains claim.atomId

def CenterLabelsWellFormed
    (graph : HeavyAtomGraph) (claims : List LocatedSourceCenterLabel) : Prop :=
  centerLabelsAcceptedByGraph? graph claims = true

@[simp] theorem explicit_center_labels_all_accepted :
    explicitCenterLabelEntries.all
      (fun entry => centerLabelsAcceptedByGraph? entry.graph entry.claims) = true := by
  decide

theorem explicit_center_labels_wellFormed
    (entry : ExplicitCenterLabelEntry) (member : entry ∈ explicitCenterLabelEntries) :
    CenterLabelsWellFormed entry.graph entry.claims := by
  exact (List.all_eq_true.mp explicit_center_labels_all_accepted) entry member

end ExplicitCenterLabelCatalog
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.retinylidene_L_lysine_claim_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.retinoyl_beta_D_glucopyranuronate_claims_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.glucopyranuronate_stereo_anchors_follow_A2b_embedding
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.hydroxy_acetoxy_3R_claims_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.explicit_center_label_claim_counts_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.explicit_center_label_ledger_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.explicit_center_labels_all_accepted
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.ExplicitCenterLabelCatalog.explicit_center_labels_wellFormed
