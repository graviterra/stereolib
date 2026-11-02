import TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3SpatialUnitExact

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit

open TetraStereo.OneCenter TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry













/-- Actual source diagram point lookup: the drawing's own `atomPositions?` entry at the atom index.
No spatial record is consulted. -/
def aromaticCanonicalPlanarPointAt? (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) : Option CartesianPoint2 := do
  let diagram ← source.diagram?
  let positions ← diagram.atomPositions?
  positions[atom.val]?
/-- Independent source meaning of one actual drawing point: an actual diagram, its actual positions
list and the exact index entry. -/
def SemanticAromaticCanonicalPlanarPointAt (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) (point : CartesianPoint2) : Prop :=
  ∃ diagram, source.diagram? = some diagram ∧
    ∃ positions, diagram.atomPositions? = some positions ∧ positions[atom.val]? = some point
/-- The actual source diagram lookup succeeds exactly on the independent meaning. -/
theorem aromaticCanonicalPlanarPointAt?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) (point : CartesianPoint2) :
    aromaticCanonicalPlanarPointAt? source atom = some point ↔
      SemanticAromaticCanonicalPlanarPointAt source atom point := by
  change (source.diagram?.bind fun diagram =>
    diagram.atomPositions?.bind fun positions => positions[atom.val]?) = some point ↔ _
  simp only [SemanticAromaticCanonicalPlanarPointAt, Option.bind_eq_some_iff]
/-- The planar point lookup fails exactly when no actual drawing point exists. -/
theorem aromaticCanonicalPlanarPointAt?_eq_none_iff
    (source : AuthoritativeChemicalInput) (atom : source.AromaticCanonicalAtom) :
    aromaticCanonicalPlanarPointAt? source atom = none ↔
      ¬ ∃ point, SemanticAromaticCanonicalPlanarPointAt source atom point := by
  constructor
  · intro refused ⟨point, derived⟩
    rw [(aromaticCanonicalPlanarPointAt?_eq_some_iff source atom point).mpr derived] at refused
    exact absurd refused (by simp)
  · intro absent
    cases computed : aromaticCanonicalPlanarPointAt? source atom with
    | none => rfl
    | some point =>
      exact absurd ⟨point, (aromaticCanonicalPlanarPointAt?_eq_some_iff source atom point).mp computed⟩ absent
/-- A source with no diagram channel refuses every planar point. -/
theorem aromaticCanonicalPlanarPointAt?_eq_none_of_diagram_none
    (source : AuthoritativeChemicalInput) (atom : source.AromaticCanonicalAtom)
    (absent : source.diagram? = none) :
    aromaticCanonicalPlanarPointAt? source atom = none := by
  unfold aromaticCanonicalPlanarPointAt?
  simp [absent]
/-- A diagram with no positions channel refuses every planar point. -/
theorem aromaticCanonicalPlanarPointAt?_eq_none_of_positions_none
    (source : AuthoritativeChemicalInput) (atom : source.AromaticCanonicalAtom)
    (diagram : DiagramConfiguration) (diagramComputed : source.diagram? = some diagram)
    (absent : diagram.atomPositions? = none) :
    aromaticCanonicalPlanarPointAt? source atom = none := by
  unfold aromaticCanonicalPlanarPointAt?
  simp [diagramComputed, absent]



noncomputable def aromaticCanonicalPlanarRule3Unit?
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialUnitResult := by
  classical
  exact
    if source.AromaticCanonicalOrdinaryDoubleBond left right then do
      let leftReference ← source.aromaticCanonicalRule3ConstitutionalSeniorReference? left right
      let rightReference ← source.aromaticCanonicalRule3ConstitutionalSeniorReference? right left
      let leftPoint ← aromaticCanonicalPlanarPointAt? source left
      let rightPoint ← aromaticCanonicalPlanarPointAt? source right
      let leftReferencePoint ← aromaticCanonicalPlanarPointAt? source leftReference
      let rightReferencePoint ← aromaticCanonicalPlanarPointAt? source rightReference
      let geometry ← planarDoubleBondGeometry? leftPoint rightPoint
        leftReferencePoint rightReferencePoint
      some { leftReference, rightReference, geometry }
    else none
/-- Independent canonical meaning of a positive source-native planar Rule-3 unit. -/
def CanonicalAromaticCanonicalPlanarRule3Unit
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult) : Prop :=
  source.AromaticCanonicalOrdinaryDoubleBond left right ∧
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
      left right result.leftReference ∧
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
      right left result.rightReference ∧
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
      SemanticAromaticCanonicalPlanarPointAt source left leftPoint ∧
      SemanticAromaticCanonicalPlanarPointAt source right rightPoint ∧
      SemanticAromaticCanonicalPlanarPointAt source result.leftReference leftReferencePoint ∧
      SemanticAromaticCanonicalPlanarPointAt source result.rightReference rightReferencePoint ∧
      ((result.geometry = OfficialRule3Geometry.seqcis ∧
          SameSide leftPoint rightPoint leftReferencePoint rightReferencePoint) ∨
        (result.geometry = OfficialRule3Geometry.seqtrans ∧
          OppositeSide leftPoint rightPoint leftReferencePoint rightReferencePoint))


theorem aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult) :
    aromaticCanonicalPlanarRule3Unit? source left right = some result ↔
      CanonicalAromaticCanonicalPlanarRule3Unit source left right result := by
  classical
  constructor
  · intro computed
    unfold aromaticCanonicalPlanarRule3Unit? at computed
    by_cases ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right
    · rw [if_pos ordinary] at computed
      change ((source.aromaticCanonicalRule3ConstitutionalSeniorReference? left right).bind
        fun leftReference =>
        (source.aromaticCanonicalRule3ConstitutionalSeniorReference? right left).bind
          fun rightReference =>
          (aromaticCanonicalPlanarPointAt? source left).bind fun leftPoint =>
          (aromaticCanonicalPlanarPointAt? source right).bind fun rightPoint =>
          (aromaticCanonicalPlanarPointAt? source leftReference).bind fun leftReferencePoint =>
          (aromaticCanonicalPlanarPointAt? source rightReference).bind fun rightReferencePoint =>
          (planarDoubleBondGeometry? leftPoint rightPoint leftReferencePoint rightReferencePoint).bind
            fun geometry => some
              ({ leftReference := leftReference
                 rightReference := rightReference
                 geometry := geometry } : source.AromaticCanonicalRule3SpatialUnitResult)) =
        some result at computed
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at computed
      obtain ⟨leftReference, hLR, rightReference, hRR, leftPoint, hLP, rightPoint, hRP,
        leftReferencePoint, hLRP, rightReferencePoint, hRRP, geometry, hG, hResult⟩ := computed
      subst result
      refine ⟨ordinary, ?_, ?_, leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
        ?_, ?_, ?_, ?_, ?_⟩
      · exact (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical left right leftReference).mp hLR
      · exact (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical right left rightReference).mp hRR
      · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source left leftPoint).mp hLP
      · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source right rightPoint).mp hRP
      · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source leftReference leftReferencePoint).mp hLRP
      · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source rightReference rightReferencePoint).mp hRRP
      · exact (planarDoubleBondGeometry?_eq_some_iff leftPoint rightPoint leftReferencePoint rightReferencePoint geometry).mp hG
    · simp [ordinary] at computed
  · rintro ⟨ordinary, leftReferenceDerived, rightReferenceDerived,
      leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
      leftPointDerived, rightPointDerived, leftReferencePointDerived,
      rightReferencePointDerived, sideDerived⟩
    have hLR := (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
      left right result.leftReference).mpr leftReferenceDerived
    have hRR := (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
      right left result.rightReference).mpr rightReferenceDerived
    have hLP := (aromaticCanonicalPlanarPointAt?_eq_some_iff source left leftPoint).mpr leftPointDerived
    have hRP := (aromaticCanonicalPlanarPointAt?_eq_some_iff source right rightPoint).mpr rightPointDerived
    have hLRP := (aromaticCanonicalPlanarPointAt?_eq_some_iff source result.leftReference
      leftReferencePoint).mpr leftReferencePointDerived
    have hRRP := (aromaticCanonicalPlanarPointAt?_eq_some_iff source result.rightReference
      rightReferencePoint).mpr rightReferencePointDerived
    have hG := (planarDoubleBondGeometry?_eq_some_iff leftPoint rightPoint leftReferencePoint
      rightReferencePoint result.geometry).mpr sideDerived
    unfold aromaticCanonicalPlanarRule3Unit?
    simp [ordinary, hLR, hRR, hLP, hRP, hLRP, hRRP, hG]
/-- Every emitted planar unit retains the full canonical meaning. -/
theorem aromaticCanonicalPlanarRule3Unit?_sound
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult)
    (computed : aromaticCanonicalPlanarRule3Unit? source left right = some result) :
    CanonicalAromaticCanonicalPlanarRule3Unit source left right result :=
  (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source left right result).mp computed
/-- Every canonical planar unit is emitted by the reader. -/
theorem aromaticCanonicalPlanarRule3Unit?_complete
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult)
    (canonical : CanonicalAromaticCanonicalPlanarRule3Unit source left right result) :
    aromaticCanonicalPlanarRule3Unit? source left right = some result :=
  (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source left right result).mpr canonical
/-- Refusal is exactly absence of a canonical planar derivation. -/
theorem aromaticCanonicalPlanarRule3Unit?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom) :
    aromaticCanonicalPlanarRule3Unit? source left right = none ↔
      ¬ ∃ result, CanonicalAromaticCanonicalPlanarRule3Unit source left right result := by
  cases computed : aromaticCanonicalPlanarRule3Unit? source left right with
  | none =>
      simp only [true_iff]
      rintro ⟨result, derived⟩
      have positive :=
        (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source left right result).mpr derived
      rw [computed] at positive
      contradiction
  | some result =>
      simp only [reduceCtorEq, false_iff]
      intro absent
      exact absurd ⟨result,
        (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source left right result).mp computed⟩
        absent
/-- A non-ordinary source pair is refused before any reference or drawing lookup. -/
theorem aromaticCanonicalPlanarRule3Unit?_eq_none_of_not_ordinary
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (absent : ¬ source.AromaticCanonicalOrdinaryDoubleBond left right) :
    aromaticCanonicalPlanarRule3Unit? source left right = none := by
  unfold aromaticCanonicalPlanarRule3Unit?
  simp [absent]
/-- Degenerate refusal: when the actual selected senior references are collinear with the actual
drawn bond base, the planar classifier refuses and so does the unit reader. -/
theorem aromaticCanonicalPlanarRule3Unit?_eq_none_of_collinear
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (leftReference rightReference : source.AromaticCanonicalAtom)
    (leftPoint rightPoint leftReferencePoint rightReferencePoint : CartesianPoint2)
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right)
    (hLR : source.aromaticCanonicalRule3ConstitutionalSeniorReference? left right = some leftReference)
    (hRR : source.aromaticCanonicalRule3ConstitutionalSeniorReference? right left = some rightReference)
    (hLP : aromaticCanonicalPlanarPointAt? source left = some leftPoint)
    (hRP : aromaticCanonicalPlanarPointAt? source right = some rightPoint)
    (hLRP : aromaticCanonicalPlanarPointAt? source leftReference = some leftReferencePoint)
    (hRRP : aromaticCanonicalPlanarPointAt? source rightReference = some rightReferencePoint)
    (degenerate : planarDirectedArea leftPoint rightPoint leftReferencePoint = 0 ∨
      planarDirectedArea leftPoint rightPoint rightReferencePoint = 0) :
    aromaticCanonicalPlanarRule3Unit? source left right = none := by
  unfold aromaticCanonicalPlanarRule3Unit?
  simp [ordinary, hLR, hRR, hLP, hRP, hLRP, hRRP,
    (planarDoubleBondGeometry?_none_iff_collinear leftPoint rightPoint leftReferencePoint
      rightReferencePoint).mpr degenerate]


theorem CanonicalAromaticCanonicalPlanarRule3Unit.planar_some
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult)
    (canonical : CanonicalAromaticCanonicalPlanarRule3Unit source left right result) :
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
      SemanticAromaticCanonicalPlanarPointAt source left leftPoint ∧
      SemanticAromaticCanonicalPlanarPointAt source right rightPoint ∧
      SemanticAromaticCanonicalPlanarPointAt source result.leftReference leftReferencePoint ∧
      SemanticAromaticCanonicalPlanarPointAt source result.rightReference rightReferencePoint ∧
      planarDoubleBondGeometry? leftPoint rightPoint leftReferencePoint rightReferencePoint =
        some result.geometry := by
  obtain ⟨_, _, _, leftPoint, rightPoint, leftReferencePoint, rightReferencePoint,
    h1, h2, h3, h4, sideDerived⟩ := canonical
  refine ⟨leftPoint, rightPoint, leftReferencePoint, rightReferencePoint, h1, h2, h3, h4, ?_⟩
  rcases sideDerived with ⟨hcis, side⟩ | ⟨htrans, side⟩
  · rw [hcis]
    exact (planarDoubleBondGeometry?_eq_some_iff leftPoint rightPoint leftReferencePoint
      rightReferencePoint OfficialRule3Geometry.seqcis).mpr (Or.inl ⟨rfl, side⟩)
  · rw [htrans]
    exact (planarDoubleBondGeometry?_eq_some_iff leftPoint rightPoint leftReferencePoint
      rightReferencePoint OfficialRule3Geometry.seqtrans).mpr (Or.inr ⟨rfl, side⟩)
/-- A canonical planar unit is never labelled `nonstereogenic`; the label comes from an actual
nondegenerate side relation. -/
theorem CanonicalAromaticCanonicalPlanarRule3Unit.geometry_ne_nonstereogenic
    (source : AuthoritativeChemicalInput) (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult)
    (canonical : CanonicalAromaticCanonicalPlanarRule3Unit source left right result) :
    result.geometry ≠ OfficialRule3Geometry.nonstereogenic := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, sideDerived⟩ := canonical
  rintro h
  rcases sideDerived with ⟨hcis, _⟩ | ⟨htrans, _⟩
  · rw [h] at hcis; exact absurd hcis (by simp)
  · rw [h] at htrans; exact absurd htrans (by simp)
end TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit
