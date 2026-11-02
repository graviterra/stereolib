import TetraStereo.Examples.Rule5EssentialRemovedOutcomeCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

/-!
# Concrete production Rule-5 essential dependency

The central atom of `F[C@](Cl)([C@H](Br)I)[C@@H](Br)I` has two constitutionally equivalent
stereogenic carbon branches.  The production occurrence at center-relative address `[2]`
supplies the exact input fact certified in `Rule5EssentialInputCertificate`.  Removing only that
coordinate changes the actual combined Rules-4b/5/6 evaluator at the final occurrence.

There is no finite search and no native evaluation tactic.
-/

/-- On the constitutionally tied stereogenic branch pair, Rules 1--4c all tie and the literal
production Rule-5 call returns the first non-tie.  This makes the essential-input regression a
Rule-5 witness, rather than merely a change in the combined comparator. -/
theorem actualRule5_decides_branchPair :
    compareCursorBranchAt molecule fuel RawMolecule.CanonicalRuleStage.rule2
        (ligandCursor root sourceSlot) (ligandCursor root otherSlot) = some Ordering.eq ∧
      compareOccurrenceDescriptorAtTiedRoot? molecule encodedState fuel .rule4a
        (ligandCursor root sourceSlot) (ligandCursor root otherSlot) = some Ordering.eq ∧
      compareOccurrenceRule4b? molecule encodedState fuel
        (ligandCursor root sourceSlot) (ligandCursor root otherSlot) = some Ordering.eq ∧
      ordinaryRule4cStage? (mol := molecule) encodedState fuel
        (ligandCursor root sourceSlot) (ligandCursor root otherSlot) =
          some { ordering := Ordering.eq } ∧
      ∃ rule5,
        compareOccurrenceRule5? molecule encodedState fuel
          (ligandCursor root sourceSlot) (ligandCursor root otherSlot) = some rule5 ∧
        rule5.ordering ≠ Ordering.eq := by
  decide

theorem removed_derive_label :
    derive? discovery fuel withoutSource target = some removedTargetLabel := by
  unfold derive?
  rw [removed_ordinary_label]

theorem full_derive_label :
    derive? discovery fuel fullState target = some fullTargetLabel := by
  unfold derive?
  rw [full_ordinary_label]

theorem actualDerive_changes :
    derive? discovery fuel withoutSource target ≠
      derive? discovery fuel fullState target := by
  rw [removed_derive_label, full_derive_label]
  intro equal
  have labelEqual : removedTargetLabel = fullTargetLabel := Option.some.inj equal
  have factEqual := congrArg Label.fact labelEqual
  have uppercaseEqual := congrArg OccurrenceAuxFact.uppercase factEqual
  change true = false at uppercaseEqual
  cases uppercaseEqual

/-- A genuine semantic essential-input witness for the actual production occurrence system. -/
theorem actualProductionEssentialInput :
    (occurrenceSystem discovery fuel).EssentialInput source target := by
  exact essentialInput_of_derive_ne discovery fuel withoutSource fullState source target
    withoutSource_differsOnlyAt actualDerive_changes

end TetraStereo.Examples.Rule5EssentialDependency
