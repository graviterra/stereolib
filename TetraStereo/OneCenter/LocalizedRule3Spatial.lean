import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Molecule-backed spatial Rule 3 units

This module connects exact molecular constitution and exact spatial evidence to the two Rule-3
geometry classes.  It deliberately accepts only the first closed reference-selection domain:
each double-bond endpoint has exactly two explicit non-partner neighbours, and one of those two
branches is strictly senior under the complete localized Rules-1a--2 digraph comparison.  A
constitutional tie is refused; later-rule or implicit-position reference selection is not guessed.

The geometry calculation uses the same oriented double-bond axis at both endpoints.  Coplanarity
is checked exactly over rational coordinates.  Parallel side normals give `seqcis`, antiparallel
side normals give `seqtrans`, and noncoplanar or collinear evidence is refused.
-/

/-- Exact rational three-vector used only for double-bond spatial observations. -/
structure RationalVector3 where
  x : ℚ
  y : ℚ
  z : ℚ
  deriving DecidableEq, Repr

namespace RationalVector3

/-- Rational cross product. -/
def cross (left right : RationalVector3) : RationalVector3 :=
  { x := left.y * right.z - left.z * right.y
    y := left.z * right.x - left.x * right.z
    z := left.x * right.y - left.y * right.x }

/-- Rational dot product. -/
def dot (left right : RationalVector3) : ℚ :=
  left.x * right.x + left.y * right.y + left.z * right.z

end RationalVector3

namespace CartesianPoint3

/-- Vector directed from `source` to `target`. -/
def displacement (source target : CartesianPoint3) : RationalVector3 :=
  { x := target.x - source.x
    y := target.y - source.y
    z := target.z - source.z }

/-- Exact scalar triple product detecting whether both reference arms lie in one plane with the
double-bond axis. -/
def rule3Coplanarity (leftEndpoint rightEndpoint leftReference rightReference :
    CartesianPoint3) : ℚ :=
  let axis := displacement leftEndpoint rightEndpoint
  let leftArm := displacement leftEndpoint leftReference
  let rightArm := displacement rightEndpoint rightReference
  RationalVector3.dot axis (RationalVector3.cross leftArm rightArm)

/-- Dot product of the two side normals, both formed with the same directed double-bond axis.
Positive means that the senior references are on the same side; negative means opposite sides. -/
def rule3SideProduct (leftEndpoint rightEndpoint leftReference rightReference :
    CartesianPoint3) : ℚ :=
  let axis := displacement leftEndpoint rightEndpoint
  let leftArm := displacement leftEndpoint leftReference
  let rightArm := displacement rightEndpoint rightReference
  RationalVector3.dot (RationalVector3.cross axis leftArm)
    (RationalVector3.cross axis rightArm)

/-- Reversing the physical double-bond axis and exchanging the corresponding senior references
preserves exact coplanarity. -/
theorem rule3Coplanarity_swap
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3Coplanarity rightEndpoint leftEndpoint rightReference leftReference =
      rule3Coplanarity leftEndpoint rightEndpoint leftReference rightReference := by
  simp [rule3Coplanarity, displacement, RationalVector3.dot,
    RationalVector3.cross]
  ring

/-- The senior-ligand side relation is also invariant under endpoint reversal. -/
theorem rule3SideProduct_swap
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3SideProduct rightEndpoint leftEndpoint rightReference leftReference =
      rule3SideProduct leftEndpoint rightEndpoint leftReference rightReference := by
  simp [rule3SideProduct, displacement, RationalVector3.dot,
    RationalVector3.cross]
  ring

end CartesianPoint3

/-- Exact Rule-3 geometry from already selected senior references.  Noncoplanar and collinear
observations are refused rather than projected or tolerance-rounded. -/
def rule3GeometryOfSpatialReferences?
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    Option OfficialRule3Geometry :=
  if CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint
      leftReference rightReference = 0 then
    let sideProduct := CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint
      leftReference rightReference
    if 0 < sideProduct then some OfficialRule3Geometry.seqcis
    else if sideProduct < 0 then some OfficialRule3Geometry.seqtrans
    else none
  else none

/-- Exact Rule-3 spatial classification does not depend on which endpoint of the same physical
double bond is presented first. -/
theorem rule3GeometryOfSpatialReferences?_swap
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3GeometryOfSpatialReferences? rightEndpoint leftEndpoint
        rightReference leftReference =
      rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftReference rightReference := by
  simp [rule3GeometryOfSpatialReferences?, CartesianPoint3.rule3Coplanarity_swap,
    CartesianPoint3.rule3SideProduct_swap]

/-- Independent exact geometry relation for a Rule-3 double-bond frame. -/
def RationalRule3SpatialGeometry
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3)
    (geometry : OfficialRule3Geometry) : Prop :=
  CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint
      leftReference rightReference = 0 ∧
    match geometry with
    | .seqcis =>
        0 < CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint
          leftReference rightReference
    | .seqtrans =>
        CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint
          leftReference rightReference < 0
    | .nonstereogenic => False

/-- Successful spatial classification is exactly the independent rational relation. -/
theorem rule3GeometryOfSpatialReferences?_eq_some_iff
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3)
    (geometry : OfficialRule3Geometry) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftReference rightReference = some geometry ↔
      RationalRule3SpatialGeometry leftEndpoint rightEndpoint
        leftReference rightReference geometry := by
  let sideProduct := CartesianPoint3.rule3SideProduct leftEndpoint rightEndpoint
    leftReference rightReference
  cases geometry with
  | seqcis =>
      unfold rule3GeometryOfSpatialReferences? RationalRule3SpatialGeometry
      by_cases coplanar : CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint
          leftReference rightReference = 0
      · rw [if_pos coplanar]
        by_cases positive : 0 < sideProduct
        · simp [sideProduct, positive, coplanar]
        · rw [if_neg positive]
          by_cases negative : sideProduct < 0 <;>
            simp [sideProduct, positive, negative, coplanar]
      · simp [coplanar]
  | seqtrans =>
      unfold rule3GeometryOfSpatialReferences? RationalRule3SpatialGeometry
      by_cases coplanar : CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint
          leftReference rightReference = 0
      · rw [if_pos coplanar]
        by_cases positive : 0 < sideProduct
        · have notNegative : ¬ sideProduct < 0 := not_lt_of_ge positive.le
          simp [sideProduct, positive, notNegative, coplanar]
        · rw [if_neg positive]
          by_cases negative : sideProduct < 0 <;>
            simp [sideProduct, negative, coplanar]
      · simp [coplanar]
  | nonstereogenic =>
      unfold rule3GeometryOfSpatialReferences? RationalRule3SpatialGeometry
      by_cases coplanar : CartesianPoint3.rule3Coplanarity leftEndpoint rightEndpoint
          leftReference rightReference = 0
      · rw [if_pos coplanar]
        by_cases positive : 0 < sideProduct
        · simp [sideProduct, positive]
        · rw [if_neg positive]
          by_cases negative : sideProduct < 0 <;>
            simp [sideProduct, negative]
      · simp [coplanar]

/-- Spatial classification refuses exactly when no Rule-3 geometry satisfies the independent
relation. -/
theorem rule3GeometryOfSpatialReferences?_eq_none_iff
    (leftEndpoint rightEndpoint leftReference rightReference : CartesianPoint3) :
    rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftReference rightReference = none ↔
      ¬ ∃ geometry,
        RationalRule3SpatialGeometry leftEndpoint rightEndpoint
          leftReference rightReference geometry := by
  constructor
  · intro refused ⟨geometry, derived⟩
    have computed :=
      (rule3GeometryOfSpatialReferences?_eq_some_iff leftEndpoint rightEndpoint
        leftReference rightReference geometry).mpr derived
    rw [refused] at computed
    contradiction
  · intro absent
    cases computed : rule3GeometryOfSpatialReferences? leftEndpoint rightEndpoint
        leftReference rightReference with
    | none => rfl
    | some geometry =>
        exact (absent ⟨geometry,
          (rule3GeometryOfSpatialReferences?_eq_some_iff leftEndpoint rightEndpoint
            leftReference rightReference geometry).mp computed⟩).elim

namespace CertifiedLocalizedCIPInput

/-- Explicit non-partner neighbours of one proposed double-bond endpoint, in canonical atom-index
order.  Requiring exactly two entries below makes the current position model explicit. -/
def localizedRule3ExplicitSubstituents (input : CertifiedLocalizedCIPInput)
    (endpoint partner : input.Atom) : List input.Atom :=
  ((input.moleculeGraph.neighborFinset endpoint).erase partner).sort (· ≤ ·)

@[simp] theorem mem_localizedRule3ExplicitSubstituents_iff
    (input : CertifiedLocalizedCIPInput) (endpoint partner substituent : input.Atom) :
    substituent ∈ input.localizedRule3ExplicitSubstituents endpoint partner ↔
      input.moleculeGraph.Adj endpoint substituent ∧ substituent ≠ partner := by
  simp [localizedRule3ExplicitSubstituents, and_comm]

/-- Independent complete constitutional expansion of one endpoint substituent. -/
def DeclarativeLocalizedRule3BranchExpansion
    (input : CertifiedLocalizedCIPInput) (endpoint reference : input.Atom)
    (sources : OfficialRuleMajorKey.AddressedSourceLayers input.Atom) : Prop :=
  OfficialRuleMajorKey.DeclarativeAddressedExpansion input.moleculeGraph
      input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge endpoint reference) sources ∧
    MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge endpoint reference)

/-- Every explicit endpoint substituent is distinct from the endpoint itself. -/
theorem localizedRule3ExplicitSubstituent_ne_endpoint
    (input : CertifiedLocalizedCIPInput) (endpoint partner reference : input.Atom)
    (present : reference ∈ input.localizedRule3ExplicitSubstituents endpoint partner) :
    reference ≠ endpoint := by
  intro equality
  have adjacent :=
    (input.mem_localizedRule3ExplicitSubstituents_iff endpoint partner reference).mp present |>.1
  subst reference
  simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent

/-- The finite default bound exhausts the branch below every explicit Rule-3 reference. -/
theorem localizedRule3ExpansionCompleteWithin_default
    (input : CertifiedLocalizedCIPInput) (endpoint partner reference : input.Atom)
    (present : reference ∈ input.localizedRule3ExplicitSubstituents endpoint partner) :
    MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge endpoint reference) := by
  have referenceComplete :=
    input.moleculeGraph.officialExpansionCompleteWithin_rootFromEdge_default
      (input.localizedRule3ExplicitSubstituent_ne_endpoint endpoint partner reference present)
  have same := MoleculeGraph.officialExpansionCompleteWithin_iff_of_children_perm
    input.executableOfficialCIPChildren input.moleculeGraph.officialCIPChildren
    input.executableOfficialCIPChildren_perm_officialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge endpoint reference)
  exact same.mpr (by simpa using referenceComplete)

/-- Exact constitutional branch key used only to establish a Rule-3 senior reference. -/
noncomputable def localizedRule3BranchKey?
    (input : CertifiedLocalizedCIPInput) (endpoint reference : input.Atom) :
    Option (OfficialRuleMajorKey input.Atom) :=
  input.buildExecutableOfficialRuleMajorKey
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge endpoint reference)

/-- A compiled endpoint-reference key has independent, complete addressed-tree semantics. -/
theorem localizedRule3BranchKey?_sound
    (input : CertifiedLocalizedCIPInput) (endpoint partner reference : input.Atom)
    (present : reference ∈ input.localizedRule3ExplicitSubstituents endpoint partner)
    (key : OfficialRuleMajorKey input.Atom)
    (computed : input.localizedRule3BranchKey? endpoint reference = some key) :
    input.DeclarativeLocalizedRule3BranchExpansion endpoint reference key.sourceNodes := by
  constructor
  · unfold localizedRule3BranchKey? at computed
    exact input.moleculeGraph.buildOfficialRuleMajorKey_declarativeAddressedExpansion
      input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge endpoint reference) key computed
  · exact input.localizedRule3ExpansionCompleteWithin_default endpoint partner reference present

/-- Select a senior reference only in the closed explicit, constitutionally strict endpoint
domain.  Rules 4--6 cannot reverse a strict Rules-1a--2 result. -/
noncomputable def localizedRule3ConstitutionalSeniorReference?
    (input : CertifiedLocalizedCIPInput) (endpoint partner : input.Atom) : Option input.Atom :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] => do
      let firstKey ← input.localizedRule3BranchKey? endpoint first
      let secondKey ← input.localizedRule3BranchKey? endpoint second
      match OfficialRuleMajorKey.compare? firstKey secondKey with
      | some Ordering.gt => some first
      | some Ordering.lt => some second
      | some Ordering.eq | none => none
  | _ => none

/-- Independent senior-reference relation.  It reads complete addressed provenance trees freshly
and records a strict constitutional decision; it does not call the selector or cached-key
comparator. -/
def DeclarativeLocalizedRule3ConstitutionalSeniorReference
    (input : CertifiedLocalizedCIPInput) (endpoint partner reference : input.Atom) : Prop :=
  ∃ first second firstSources secondSources,
    input.localizedRule3ExplicitSubstituents endpoint partner = [first, second] ∧
      input.DeclarativeLocalizedRule3BranchExpansion endpoint first firstSources ∧
      input.DeclarativeLocalizedRule3BranchExpansion endpoint second secondSources ∧
      ((OfficialRuleMajorKey.compareAddressedSources input.moleculeGraph
          firstSources secondSources = Ordering.gt ∧ reference = first) ∨
       (OfficialRuleMajorKey.compareAddressedSources input.moleculeGraph
          firstSources secondSources = Ordering.lt ∧ reference = second))

/-- Every selected reference is justified by complete molecule-backed constitutional trees. -/
theorem localizedRule3ConstitutionalSeniorReference?_sound
    (input : CertifiedLocalizedCIPInput) (endpoint partner reference : input.Atom)
    (computed : input.localizedRule3ConstitutionalSeniorReference? endpoint partner =
      some reference) :
    input.DeclarativeLocalizedRule3ConstitutionalSeniorReference endpoint partner reference := by
  unfold localizedRule3ConstitutionalSeniorReference? at computed
  generalize candidatesIdentity :
      input.localizedRule3ExplicitSubstituents endpoint partner = candidates at computed
  cases candidates with
  | nil => simp at computed
  | cons first rest =>
      cases rest with
      | nil => simp at computed
      | cons second tail =>
          cases tail with
          | cons third tail => simp at computed
          | nil =>
              cases firstComputed : input.localizedRule3BranchKey? endpoint first with
              | none => simp [firstComputed] at computed
              | some firstKey =>
                  cases secondComputed : input.localizedRule3BranchKey? endpoint second with
                  | none => simp [firstComputed, secondComputed] at computed
                  | some secondKey =>
                      cases compared : OfficialRuleMajorKey.compare? firstKey secondKey with
                      | none => simp [firstComputed, secondComputed, compared] at computed
                      | some outcome =>
                          have firstPresent : first ∈
                              input.localizedRule3ExplicitSubstituents endpoint partner := by
                            rw [candidatesIdentity]
                            simp
                          have secondPresent : second ∈
                              input.localizedRule3ExplicitSubstituents endpoint partner := by
                            rw [candidatesIdentity]
                            simp
                          have firstDerived := input.localizedRule3BranchKey?_sound
                            endpoint partner first firstPresent firstKey firstComputed
                          have secondDerived := input.localizedRule3BranchKey?_sound
                            endpoint partner second secondPresent secondKey secondComputed
                          have firstAligned := input.buildExecutableOfficialRuleMajorKey_sourceAligned
                            (input.certified.input.molecule.atomCount + 1)
                            (OfficialCIPNode.rootFromEdge endpoint first) firstKey (by
                              exact firstComputed)
                          have secondAligned := input.buildExecutableOfficialRuleMajorKey_sourceAligned
                            (input.certified.input.molecule.atomCount + 1)
                            (OfficialCIPNode.rootFromEdge endpoint second) secondKey (by
                              exact secondComputed)
                          have freshComparison :
                              OfficialRuleMajorKey.compareAddressedSources input.moleculeGraph
                                  firstKey.sourceNodes secondKey.sourceNodes = outcome := by
                            rw [← OfficialRuleMajorKey.compare_eq_compareAddressedSources_of_sourceAligned
                              input.moleculeGraph firstKey secondKey firstAligned secondAligned]
                            exact OfficialRuleMajorKey.compare_eq_of_compare?_eq_some
                              firstKey secondKey outcome compared
                          cases outcome with
                          | eq => simp [firstComputed, secondComputed, compared] at computed
                          | gt =>
                              simp [firstComputed, secondComputed, compared] at computed
                              subst reference
                              exact ⟨first, second, firstKey.sourceNodes, secondKey.sourceNodes,
                                candidatesIdentity, firstDerived, secondDerived,
                                Or.inl ⟨freshComparison, rfl⟩⟩
                          | lt =>
                              simp [firstComputed, secondComputed, compared] at computed
                              subst reference
                              exact ⟨first, second, firstKey.sourceNodes, secondKey.sourceNodes,
                                candidatesIdentity, firstDerived, secondDerived,
                                Or.inr ⟨freshComparison, rfl⟩⟩

/-- Successful molecule-level Rule-3 spatial analysis retains both selected reference atoms. -/
structure LocalizedRule3SpatialUnitResult (input : CertifiedLocalizedCIPInput) where
  leftReference : input.Atom
  rightReference : input.Atom
  geometry : OfficialRule3Geometry
  deriving DecidableEq, Repr

/-- Analyze one proposed localized double bond.  Structural membership, complete constitutional
reference ranking, direct semantic coordinates, and exact geometry are all fail-closed. -/
noncomputable def localizedRule3SpatialUnit?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom) :
    Option input.LocalizedRule3SpatialUnitResult :=
  if input.moleculeGraph.bond left right = 2 then do
    let leftReference ← input.localizedRule3ConstitutionalSeniorReference? left right
    let rightReference ← input.localizedRule3ConstitutionalSeniorReference? right left
    let leftPoint ← input.spatialPointAt? left
    let rightPoint ← input.spatialPointAt? right
    let leftReferencePoint ← input.spatialPointAt? leftReference
    let rightReferencePoint ← input.spatialPointAt? rightReference
    let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
      leftReferencePoint rightReferencePoint
    some { leftReference, rightReference, geometry }
  else none

/-- Independent molecule-backed meaning of an accepted localized Rule-3 unit. -/
def DeclarativeLocalizedRule3SpatialUnit
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult) : Prop :=
  input.moleculeGraph.bond left right = 2 ∧
    input.DeclarativeLocalizedRule3ConstitutionalSeniorReference
      left right result.leftReference ∧
    input.DeclarativeLocalizedRule3ConstitutionalSeniorReference
      right left result.rightReference ∧
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
      input.SemanticSpatialPointAt left leftPoint ∧
      input.SemanticSpatialPointAt right rightPoint ∧
      input.SemanticSpatialPointAt result.leftReference leftReferencePoint ∧
      input.SemanticSpatialPointAt result.rightReference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint result.geometry

/-- Every emitted Rule-3 geometry is backed by the molecular double bond, two complete strict
constitutional reference derivations, direct semantic coordinates, and the exact rational
`seqcis/seqtrans` relation. -/
theorem localizedRule3SpatialUnit?_sound
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (result : input.LocalizedRule3SpatialUnitResult)
    (computed : input.localizedRule3SpatialUnit? left right = some result) :
    input.DeclarativeLocalizedRule3SpatialUnit left right result := by
  unfold localizedRule3SpatialUnit? at computed
  by_cases doubleBond : input.moleculeGraph.bond left right = 2
  · rw [if_pos doubleBond] at computed
    cases leftReferenceComputed :
        input.localizedRule3ConstitutionalSeniorReference? left right with
    | none => simp [leftReferenceComputed] at computed
    | some leftReference =>
        cases rightReferenceComputed :
            input.localizedRule3ConstitutionalSeniorReference? right left with
        | none => simp [leftReferenceComputed, rightReferenceComputed] at computed
        | some rightReference =>
            cases leftPointComputed : input.spatialPointAt? left with
            | none =>
                simp [leftReferenceComputed, rightReferenceComputed,
                  leftPointComputed] at computed
            | some leftPoint =>
                cases rightPointComputed : input.spatialPointAt? right with
                | none =>
                    simp [leftReferenceComputed, rightReferenceComputed,
                      leftPointComputed, rightPointComputed] at computed
                | some rightPoint =>
                    cases leftReferencePointComputed :
                        input.spatialPointAt? leftReference with
                    | none =>
                        simp [leftReferenceComputed, rightReferenceComputed,
                          leftPointComputed, rightPointComputed,
                          leftReferencePointComputed] at computed
                    | some leftReferencePoint =>
                        cases rightReferencePointComputed :
                            input.spatialPointAt? rightReference with
                        | none =>
                            simp [leftReferenceComputed, rightReferenceComputed,
                              leftPointComputed, rightPointComputed,
                              rightReferencePointComputed] at computed
                        | some rightReferencePoint =>
                            cases geometryComputed : rule3GeometryOfSpatialReferences?
                                leftPoint rightPoint leftReferencePoint rightReferencePoint with
                            | none =>
                                simp [leftReferenceComputed, rightReferenceComputed,
                                  leftPointComputed, rightPointComputed,
                                  leftReferencePointComputed, rightReferencePointComputed,
                                  geometryComputed] at computed
                            | some geometry =>
                                simp [leftReferenceComputed, rightReferenceComputed,
                                  leftPointComputed, rightPointComputed,
                                  leftReferencePointComputed, rightReferencePointComputed,
                                  geometryComputed] at computed
                                subst result
                                refine ⟨doubleBond,
                                  input.localizedRule3ConstitutionalSeniorReference?_sound
                                    left right leftReference leftReferenceComputed,
                                  input.localizedRule3ConstitutionalSeniorReference?_sound
                                    right left rightReference rightReferenceComputed,
                                  leftPoint, rightPoint, leftReferencePoint,
                                  rightReferencePoint, ?_, ?_, ?_, ?_, ?_⟩
                                · exact (input.spatialPointAt?_eq_some_iff left leftPoint).mp
                                    leftPointComputed
                                · exact (input.spatialPointAt?_eq_some_iff right rightPoint).mp
                                    rightPointComputed
                                · exact (input.spatialPointAt?_eq_some_iff
                                    leftReference leftReferencePoint).mp
                                      leftReferencePointComputed
                                · exact (input.spatialPointAt?_eq_some_iff
                                    rightReference rightReferencePoint).mp
                                      rightReferencePointComputed
                                · exact (rule3GeometryOfSpatialReferences?_eq_some_iff
                                    leftPoint rightPoint leftReferencePoint
                                      rightReferencePoint geometry).mp geometryComputed
  · simp [doubleBond] at computed

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
