import TetraStereo.OneCenter.IR9PolyhedralSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter.RedBookIR9

/-!
# Exact applicability boundary for higher-coordinate IR-9 geometry evidence

For coordination numbers five through nine, IR-9 asks the user to select the nearest idealized
Table IR-9.2 geometry but publishes no universal numerical metric or distortion threshold.  The
normative model therefore accepts an explicit nearest-idealized observation only in that exact
coordination range.  This module freezes the complete 16-geometry domain and proves its positive
and negative executable boundaries.
-/

/-- Exactly the Table IR-9.2 geometries to which the higher-coordinate nearest-idealized evidence
constructor may apply. -/
def higherCoordinationGeometries : List Geometry :=
  allGeometries.filter fun geometry => 5 ≤ geometry.coordinationNumber

@[simp] theorem higherCoordinationGeometries_length :
    higherCoordinationGeometries.length = 16 := by
  decide

theorem higherCoordinationGeometries_nodup :
    higherCoordinationGeometries.Nodup :=
  allGeometries_nodup.filter _

/-- Membership is exactly the source's coordination-number applicability condition. -/
@[simp] theorem mem_higherCoordinationGeometries_iff (geometry : Geometry) :
    geometry ∈ higherCoordinationGeometries ↔ 5 ≤ geometry.coordinationNumber := by
  simp [higherCoordinationGeometries]

/-- Executable recognition is defined exactly on the 16-geometry higher-coordinate domain. -/
theorem higherCoordinationNearestIdealized_isSome_iff (geometry : Geometry) :
    (GeometryRecognitionObservation.recognizedGeometry?
      (.higherCoordinationNearestIdealized geometry)).isSome = true ↔
        5 ≤ geometry.coordinationNumber := by
  by_cases applicable : 5 ≤ geometry.coordinationNumber <;>
    simp [GeometryRecognitionObservation.recognizedGeometry?, applicable]

/-- A positive result preserves the exact declared idealized geometry; it cannot silently return
another geometry with the same coordination number. -/
theorem higherCoordinationNearestIdealized_eq_some_iff
    (geometry output : Geometry) :
    GeometryRecognitionObservation.recognizedGeometry?
        (.higherCoordinationNearestIdealized geometry) = some output ↔
      5 ≤ geometry.coordinationNumber ∧ output = geometry := by
  by_cases applicable : 5 ≤ geometry.coordinationNumber <;>
    simp [GeometryRecognitionObservation.recognizedGeometry?, applicable, eq_comm]

/-- Every one of the exact 16 higher-coordinate Table geometries is accepted when supplied as the
nearest-idealized experimental/modeling judgment. -/
theorem higherCoordinationGeometry_recognized
    (geometry : Geometry) (member : geometry ∈ higherCoordinationGeometries) :
    GeometryRecognized (.higherCoordinationNearestIdealized geometry) geometry := by
  have applicable := (mem_higherCoordinationGeometries_iff geometry).mp member
  exact (higherCoordinationNearestIdealized_eq_some_iff geometry geometry).mpr
    ⟨applicable, rfl⟩

/-- The higher-coordinate constructor rejects every two-, three-, and four-coordinate geometry.
Those geometries must use their own typed IR-9 decision-tree evidence. -/
theorem higherCoordinationNearestIdealized_eq_none_of_lower
    (geometry : Geometry) (lower : geometry.coordinationNumber < 5) :
    GeometryRecognitionObservation.recognizedGeometry?
        (.higherCoordinationNearestIdealized geometry) = none := by
  have notApplicable : ¬ 5 ≤ geometry.coordinationNumber := by omega
  simp [GeometryRecognitionObservation.recognizedGeometry?, notApplicable]

end TetraStereo.OneCenter.RedBookIR9
