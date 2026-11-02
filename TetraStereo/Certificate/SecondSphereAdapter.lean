import TetraStereo.Certificate.ConstitutionalSource
import TetraStereo.UniversalProof.SecondSphereScheduledSourceView

set_option autoImplicit false

namespace TetraStereo.Certificate.SecondSphereAdapter

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.Certificate.Constitutional
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.SecondSphereScheduledSourceView

/-!
The held-out repeated-carbon family uses the same finite checker and source safe-order theorem.
The adapter supplies only physical slots and already derived source observations. It does not
reuse the family's existing comparison/sort theorem. These constitutional decisions are strict
before descriptor-dependent rules; this adapter alone is not a pseudoasymmetry certificate.
-/

noncomputable def slots (ps : List TetrahedralInputParity) (i : Fin ps.length) : Four (Fin 4) :=
  ⟨familyRoleSlot ps i 1 7 (by simp), familyRoleSlot ps i 1 2 (by simp),
    familyRoleSlot ps i 1 8 (by simp), familyRoleSlot ps i 1 6 (by simp)⟩

theorem slots_distinct (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (slots ps i).toList.Nodup := by
  simp only [slots, Four.toList, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, not_false_eq_true, and_true]
  repeat' constructor
  all_goals exact family_role_slots_ne ps i 1 _ _ (by simp) (by simp) (by decide)

theorem realization (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    SourcePrefixRealization (familySource ps) (familyFrame ps i 1) (familyViewKeys ps i view)
      (slots ps i) secondSphereObservations := by
  have children := family_one_child_observations ps i
  have projections := family_view_production_projections ps i view
  refine source_realization_two_spheres (familySource ps) (familyFrame ps i 1)
    (familyViewKeys ps i view) (slots ps i) 9 6 6 1 _ _
    (family_role_priority ps i 1 7 (by simp))
    (family_role_priority ps i 1 2 (by simp))
    (family_role_priority ps i 1 8 (by simp))
    (family_role_priority ps i 1 6 (by simp)) children.1 children.2 ?_ ?_
  · simpa [slots, rootLayer, childLayer, childLayerFrom, carbonRootLayer, bridgeChildLayer]
      using projections.1
  · simpa [slots, rootLayer, childLayer, childLayerFrom, carbonRootLayer, methylChildLayer]
      using projections.2

/-- No topology-specific sorting proof: only the common theorem and this adapter's realization. -/
theorem safe_order (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (view : (familySource ps).AromaticCanonicalDependencyView
      ((familySource ps).aromaticCanonicalFinalOccurrence 1 (familyCenter ps i))) :
    ∃ tracked,
      (familySource ps).safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?
        (familyViewKeys ps i view) = some tracked ∧
      tracked.highestFirst = (slots ps i).toList ∧ tracked.pseudoComparisons = 0 ∧
      (familySource ps).aromaticCanonicalOccurrenceRule3Through5OrderCoherent
        (familyViewKeys ps i view) tracked.highestFirst = true :=
  checked_source_safe_order (familySource ps) _ view 4 (familyFrame ps i 1)
    (family_roots_real ps i 1) (familyViewKeys ps i view) (family_view_keys_computed ps i view)
    (slots ps i) (slots_distinct ps i) secondSphereObservations (realization ps i view)
    second_sphere_checked

end TetraStereo.Certificate.SecondSphereAdapter
