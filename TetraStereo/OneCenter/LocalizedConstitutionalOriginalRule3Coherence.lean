import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3Key

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Full Rule-3 ordering can only refine a constitutional tie. -/
theorem rule3_descending_constitutional
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (descending : input.LocalizedRerootRecursiveRule3SpatialKeysDescending keys) :
    OfficialRuleMajorKey.Descending (keys.map (·.constitutional)) := by
  apply List.Pairwise.map (fun key => key.constitutional) _ descending
  intro left right ordered lower
  apply ordered
  simp [compareLocalizedRerootRecursiveRule3SpatialKeys, compareLex, Ordering.byKey, lower]

theorem projected_rule3_constitutional_key_list
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (R : input.LocalizedRerootCursor carrierFuel →
      input.LocalizedRerootRecursiveRule3SpatialKey → Prop)
    (project : ∀ cursor key, R cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional) :
    ∀ cursors keys, List.Forall₂ R cursors keys →
      input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors
        (keys.map (·.constitutional)) := by
  intro cursors keys derived
  induction derived with
  | nil => exact .nil fuel
  | cons head tail ih => exact .cons (project _ _ head) ih

/-- Every independent original full-key derivation contains a pure constitutional derivation.
No endpoint readiness, computed success, or assumptions on descriptor values are needed. -/
theorem descriptorRule3Key_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor key,
      input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
        target view fuel excluded cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor key meaning
      obtain ⟨children, frame, empty, _, rfl⟩ := meaning
      exact .terminal frame empty
  | succ fuel ih =>
      intro excluded cursor key meaning
      obtain ⟨children, observation, frame, _, terminal | branch⟩ := meaning
      · obtain ⟨empty, rfl⟩ := terminal
        exact .terminal frame empty
      · obtain ⟨childKeys, sorted, nonempty, derivations, ranking, descending, rfl⟩ := branch
        exact .branch frame nonempty
          (projected_rule3_constitutional_key_list input _ (ih excluded) children childKeys derivations)
          (ranking.map (·.constitutional)) (input.rule3_descending_constitutional sorted descending)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
