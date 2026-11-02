import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Circular occurrence-budget retirement

The public two- and four-center circular solvers now retain their established names while routing
through traversal bounded only by molecular depth.  The older explicitly capped tree/search
primitives remain available for callers that deliberately request an operational budget, but they
are not consulted by these public circular entry points.
-/

theorem exactCircularPositionSolutions_eq_capFree
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (fuel : Nat) (unresolved : List Nat) :
    exactCircularPositionSolutions result mol fuel unresolved =
      exactCircularPositionSolutionsCapFree result mol fuel unresolved :=
  rfl

theorem nearestShallowCircularOccurrence?_eq_capFree
    (mol : RawMolecule) (centers : List Nat) (fuel center ligand : Nat) :
    nearestShallowCircularOccurrence? mol centers fuel center ligand =
      nearestShallowCircularOccurrenceCapFree? mol centers fuel center ligand :=
  rfl

theorem compareShallowCircularConstitution?_eq_authoritative
    (mol : RawMolecule) (fuel center left right : Nat) :
    compareShallowCircularConstitution? mol fuel center left right =
      match mol.compareBranchesAuthoritative? center left right with
      | some Ordering.eq =>
          if mol.hasConstitutionAutomorphismSwapping center left right then
            some Ordering.eq
          else none
      | verdict => verdict :=
  rfl

/-- The legacy `fuel` parameter no longer controls far-end Rule-3 reference perception. -/
theorem sharedRule3UnitHasIndependentFarReference_fuel_irrelevant
    (mol : RawMolecule) (firstFuel secondFuel : Nat)
    (left right : ChemistryNormalizationResult.Rule3GeometryOccurrence) :
    ChemistryNormalizationResult.sharedRule3UnitHasIndependentFarReference
        mol firstFuel left right =
      ChemistryNormalizationResult.sharedRule3UnitHasIndependentFarReference
        mol secondFuel left right :=
  rfl

/-- The legacy `fuel` parameter no longer controls coupled Rule-3 constitutional matching. -/
theorem hasCoupledRule3PerfectMatching_fuel_irrelevant
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (firstFuel secondFuel center : Nat) :
    result.hasCoupledRule3PerfectMatching mol firstFuel center =
      result.hasCoupledRule3PerfectMatching mol secondFuel center :=
  rfl

end TetraStereo.OneCenter
