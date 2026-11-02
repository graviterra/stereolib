import TetraStereo.OneCenter.IR9TypedGeometryIngressTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Total configuration-index witnesses for the complete IR-9 vocabulary

Every geometry-specific index constructor is already proved against its source or finite-symmetry
semantics.  This module closes the outer production boundary: one canonical, duplicate-free
position frame and an in-range priority list exercise the executable router for every one of the
25 geometries.
-/

/-- Canonical valid priority numbers, one for every coordination position. -/
def canonicalPolyhedralPriorities (geometry : PolyhedralGeometry) :
    List PolyhedralPriorityNumber :=
  (List.range geometry.coordinationNumber).map fun position =>
    { number := position + 1 }

/-- Canonical distinguished positions for the geometry's complete index constructor. -/
def canonicalPolyhedralPositions (geometry : PolyhedralGeometry) : List Nat :=
  List.range ((geometry.configurationIndexArity?).getD 0)

@[simp] theorem canonicalPolyhedralPriorities_length (geometry : PolyhedralGeometry) :
    (canonicalPolyhedralPriorities geometry).length = geometry.coordinationNumber := by
  simp [canonicalPolyhedralPriorities]

/-- Every canonical priority number lies in the exact `1..coordinationNumber` source range. -/
theorem canonicalPolyhedralPriorities_valid
    (geometry : PolyhedralGeometry) (priority : PolyhedralPriorityNumber)
    (member : priority ∈ canonicalPolyhedralPriorities geometry) :
    priority.validFor geometry.coordinationNumber = true := by
  simp [canonicalPolyhedralPriorities] at member
  obtain ⟨position, bound, rfl⟩ := member
  simp [PolyhedralPriorityNumber.validFor]
  omega

@[simp] theorem canonicalPolyhedralPositions_length (geometry : PolyhedralGeometry) :
    (canonicalPolyhedralPositions geometry).length =
      geometry.configurationIndexArity?.getD 0 := by
  simp [canonicalPolyhedralPositions]

theorem canonicalPolyhedralPositions_nodup (geometry : PolyhedralGeometry) :
    (canonicalPolyhedralPositions geometry).Nodup :=
  List.nodup_range

/-- The full production configuration-index router succeeds on its canonical witness for every
geometry, including all finite-symmetry mathematical-index completions. -/
@[simp] theorem canonicalPolyhedralConfigurationIndex_isSome
    (geometry : PolyhedralGeometry) :
    (polyhedralConfigurationIndex? geometry
      (canonicalPolyhedralPriorities geometry)
      (canonicalPolyhedralPositions geometry)).isSome = true := by
  cases geometry <;> decide

/-- Consequently every one of the 25 production geometries has an executable configuration
index. -/
theorem every_polyhedral_geometry_has_configuration_index
    (geometry : PolyhedralGeometry) :
    ∃ index,
      polyhedralConfigurationIndex? geometry
        (canonicalPolyhedralPriorities geometry)
        (canonicalPolyhedralPositions geometry) = some index := by
  cases computed : polyhedralConfigurationIndex? geometry
      (canonicalPolyhedralPriorities geometry)
      (canonicalPolyhedralPositions geometry) with
  | none =>
      have present := canonicalPolyhedralConfigurationIndex_isSome geometry
      simp [computed] at present
  | some index => exact ⟨index, rfl⟩

/-- Canonical rendered descriptor witness for one geometry.  Its index is computed by the same
production router used by public geometry observations. -/
def canonicalPolyhedralDescriptor?
    (geometry : PolyhedralGeometry) : Option PolyhedralDescriptor := do
  let index ← polyhedralConfigurationIndex? geometry
    (canonicalPolyhedralPriorities geometry)
    (canonicalPolyhedralPositions geometry)
  some { geometry := geometry, configurationIndex := index }

@[simp] theorem canonicalPolyhedralDescriptor?_isSome (geometry : PolyhedralGeometry) :
    (canonicalPolyhedralDescriptor? geometry).isSome = true := by
  obtain ⟨index, computed⟩ := every_polyhedral_geometry_has_configuration_index geometry
  simp [canonicalPolyhedralDescriptor?, computed]

/-- The canonical descriptor constructor preserves the exact geometry; no configuration-index
route can silently relabel the polyhedron. -/
theorem canonicalPolyhedralDescriptor?_geometry
    (geometry : PolyhedralGeometry) (descriptor : PolyhedralDescriptor) :
    canonicalPolyhedralDescriptor? geometry = some descriptor →
      descriptor.geometry = geometry := by
  unfold canonicalPolyhedralDescriptor?
  cases computed : polyhedralConfigurationIndex? geometry
      (canonicalPolyhedralPriorities geometry)
      (canonicalPolyhedralPositions geometry) with
  | none => simp
  | some index =>
      intro emitted
      simp at emitted
      subst descriptor
      rfl

namespace PolyhedralDescriptor

/-- With no relative or absolute suffix, the complete descriptor renderer emits exactly the
normative geometry symbol. -/
@[simp] theorem geometryOnly_label (geometry : PolyhedralGeometry) :
    ({ geometry := geometry } : PolyhedralDescriptor).label = geometry.symbol := by
  cases geometry <;> rfl

end PolyhedralDescriptor

end TetraStereo.OneCenter
