import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOrdinaryCumuleneEnumeration
import TetraStereo.OneCenter.LocalizedRule3Spatial

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical Rule-3 spatial units

This module supplies the missing molecule-to-Rule-3 boundary on the original semantic source.
Endpoint references are not restricted to a two-entry pattern: every represented non-partner
neighbour is compiled through the complete exact Rules-1a--2 digraph, and a reference is accepted
only when it strictly outranks every distinct represented competitor.  Thus the construction also
covers the hydrogen-materialised molecules used by the admitted public pipeline.

The boundary remains deliberately fail-closed for positions that are not represented by atoms
(for example an unmaterialised hydrogen or lone pair).  Those require a separately proved virtual
ligand model; this module does not silently invent one.
-/

/-- All represented non-partner neighbours of one proposed order-two endpoint. -/
noncomputable def aromaticCanonicalRule3Substituents
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    List source.AromaticCanonicalAtom :=
  ((source.aromaticCanonicalNeighborFinset endpoint).erase partner).sort (· ≤ ·)

@[simp] theorem mem_aromaticCanonicalRule3Substituents_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner substituent : source.AromaticCanonicalAtom) :
    substituent ∈ source.aromaticCanonicalRule3Substituents endpoint partner ↔
      source.AromaticCanonicalAdjacent endpoint substituent ∧ substituent ≠ partner := by
  simp [aromaticCanonicalRule3Substituents, and_comm]

theorem aromaticCanonicalRule3Substituents_nodup
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalRule3Substituents endpoint partner).Nodup := by
  exact Finset.sort_nodup _ _

theorem aromaticCanonicalRule3Substituent_ne_endpoint
    (source : AuthoritativeChemicalInput)
    (endpoint partner substituent : source.AromaticCanonicalAtom)
    (present : substituent ∈
      source.aromaticCanonicalRule3Substituents endpoint partner) :
    substituent ≠ endpoint := by
  exact (source.mem_aromaticCanonicalRule3Substituents_iff
    endpoint partner substituent).mp present |>.1.1.symm

/-- Exact source-canonical Rules-1a--2 key for one represented endpoint substituent. -/
noncomputable def buildAromaticCanonicalRule3BranchKey?
    (source : AuthoritativeChemicalInput)
    (endpoint reference : source.AromaticCanonicalAtom) :
    Option (ExactOfficialRuleMajorKey source.AromaticCanonicalAtom) :=
  source.molecule.toLocalizedMoleculeGraph.buildObservedExactOfficialRuleMajorKey
    source.molecule.semanticExactOfficialRule1aObservation
    (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount)
    (source.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge endpoint reference)

/-- Independent complete addressed-tree meaning of one compiled endpoint branch. -/
def DeclarativeAromaticCanonicalRule3Branch
    (source : AuthoritativeChemicalInput)
    (endpoint reference : source.AromaticCanonicalAtom)
    (sources : OfficialRuleMajorKey.AddressedSourceLayers
      source.AromaticCanonicalAtom) : Prop :=
  ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion
      source.molecule.toLocalizedMoleculeGraph
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount)
      (source.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge endpoint reference) sources ∧
    MoleculeGraph.OfficialExpansionCompleteWithin
      (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount)
      (source.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge endpoint reference)

/-- A successful source branch key has an independently derived, exhaustive provenance tree. -/
theorem buildAromaticCanonicalRule3BranchKey?_sound
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (present : reference ∈
      source.aromaticCanonicalRule3Substituents endpoint partner)
    (key : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom)
    (computed : source.buildAromaticCanonicalRule3BranchKey? endpoint reference = some key) :
    source.DeclarativeAromaticCanonicalRule3Branch endpoint reference key.sourceNodes := by
  have exactComputed :
      source.molecule.toLocalizedMoleculeGraph.buildExactOfficialRuleMajorKey
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount)
          (source.molecule.atomCount + 1)
          (OfficialCIPNode.rootFromEdge endpoint reference) = some key := by
    rw [← source.molecule.toLocalizedMoleculeGraph
      |>.buildObservedExactOfficialRuleMajorKey_eq_exact
        source.molecule.semanticExactOfficialRule1aObservation
        source.molecule.semanticExactOfficialRule1aObservation_eq_independent]
    exact computed
  constructor
  · exact source.molecule.toLocalizedMoleculeGraph
      |>.buildExactOfficialRuleMajorKey_declarativeAddressedExpansion
        (source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount)
        (source.molecule.atomCount + 1)
        (OfficialCIPNode.rootFromEdge endpoint reference) key exactComputed
  · exact source.molecule.aromaticCanonicalExpansionCompleteWithin_rootFromEdge_default
      (source.aromaticCanonicalRule3Substituent_ne_endpoint
        endpoint partner reference present)

/-- A represented substituent paired with its complete constitutional branch key. -/
structure AromaticCanonicalRule3RankedSubstituent
    (source : AuthoritativeChemicalInput) where
  atom : source.AromaticCanonicalAtom
  key : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom

/-- Compile one represented endpoint substituent. -/
noncomputable def buildAromaticCanonicalRule3RankedSubstituent?
    (source : AuthoritativeChemicalInput)
    (endpoint reference : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3RankedSubstituent := do
  let key ← source.buildAromaticCanonicalRule3BranchKey? endpoint reference
  some { atom := reference, key := key }

/-- Independent pointwise relation between a candidate and its compiled branch. -/
def DeclarativeAromaticCanonicalRule3RankedSubstituent
    (source : AuthoritativeChemicalInput)
    (endpoint : source.AromaticCanonicalAtom)
    (reference : source.AromaticCanonicalAtom)
    (ranked : source.AromaticCanonicalRule3RankedSubstituent) : Prop :=
  ranked.atom = reference ∧
    source.DeclarativeAromaticCanonicalRule3Branch
      endpoint reference ranked.key.sourceNodes

theorem buildAromaticCanonicalRule3RankedSubstituent?_sound
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (present : reference ∈
      source.aromaticCanonicalRule3Substituents endpoint partner)
    (ranked : source.AromaticCanonicalRule3RankedSubstituent)
    (computed : source.buildAromaticCanonicalRule3RankedSubstituent?
      endpoint reference = some ranked) :
    source.DeclarativeAromaticCanonicalRule3RankedSubstituent
      endpoint reference ranked := by
  unfold buildAromaticCanonicalRule3RankedSubstituent? at computed
  cases keyComputed : source.buildAromaticCanonicalRule3BranchKey? endpoint reference with
  | none => simp [keyComputed] at computed
  | some key =>
      simp [keyComputed] at computed
      subst ranked
      exact ⟨rfl, source.buildAromaticCanonicalRule3BranchKey?_sound
        endpoint partner reference present key keyComputed⟩

private theorem mapM_buildAromaticCanonicalRule3RankedSubstituent?_sound
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    ∀ candidates ranked,
      candidates.mapM
          (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) = some ranked →
      (∀ reference, reference ∈ candidates → reference ∈
        source.aromaticCanonicalRule3Substituents endpoint partner) →
      List.Forall₂
        (source.DeclarativeAromaticCanonicalRule3RankedSubstituent endpoint)
        candidates ranked
  | [], ranked, computed, _sublist => by
      simp at computed
      subst ranked
      exact .nil
  | reference :: candidates, ranked, computed, sublist => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalRule3RankedSubstituent?
          endpoint reference with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : candidates.mapM
              (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst ranked
              have referencePresent : reference ∈
                  source.aromaticCanonicalRule3Substituents endpoint partner := by
                exact sublist reference (by simp)
              exact List.Forall₂.cons
                (source.buildAromaticCanonicalRule3RankedSubstituent?_sound
                  endpoint partner reference referencePresent head headComputed)
                (source.mapM_buildAromaticCanonicalRule3RankedSubstituent?_sound
                  endpoint partner candidates tail tailComputed (by
                    intro tailReference tailPresent
                    exact sublist tailReference (by simp [tailPresent])))

/-- Exact Rules-1a--2 comparison of two compiled source branches. -/
noncomputable def compareAromaticCanonicalRule3RankedSubstituents
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRule3RankedSubstituent →
      source.AromaticCanonicalRule3RankedSubstituent → Ordering :=
  Ordering.byKey AromaticCanonicalRule3RankedSubstituent.key
    (ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph)

theorem compareAromaticCanonicalRule3RankedSubstituents_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalRule3RankedSubstituents := by
  unfold compareAromaticCanonicalRule3RankedSubstituents
  letI : Std.TransCmp
      (ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph) :=
    ExactOfficialRuleMajorKey.compare_transCmp source.molecule.toLocalizedMoleculeGraph
  infer_instance

/-- Executable test that one candidate strictly beats every distinct represented candidate. -/
noncomputable def aromaticCanonicalRule3StrictlyOutranksAll
    (source : AuthoritativeChemicalInput)
    (candidate : source.AromaticCanonicalRule3RankedSubstituent)
    (ranked : List source.AromaticCanonicalRule3RankedSubstituent) : Bool :=
  ranked.all fun other =>
    if other.atom == candidate.atom then true
    else source.compareAromaticCanonicalRule3RankedSubstituents candidate other == Ordering.gt

/-- Independent strict-maximum relation. -/
def DeclarativeAromaticCanonicalRule3StrictlySenior
    (source : AuthoritativeChemicalInput)
    (ranked : List source.AromaticCanonicalRule3RankedSubstituent)
    (candidate : source.AromaticCanonicalRule3RankedSubstituent) : Prop :=
  candidate ∈ ranked ∧
    ∀ other, other ∈ ranked → other.atom ≠ candidate.atom →
      ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph
        candidate.key other.key = Ordering.gt

theorem aromaticCanonicalRule3StrictlyOutranksAll_eq_true_iff
    (source : AuthoritativeChemicalInput)
    (candidate : source.AromaticCanonicalRule3RankedSubstituent)
    (ranked : List source.AromaticCanonicalRule3RankedSubstituent) :
    source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked = true ↔
      ∀ other, other ∈ ranked → other.atom ≠ candidate.atom →
        ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph
          candidate.key other.key = Ordering.gt := by
  rw [aromaticCanonicalRule3StrictlyOutranksAll, List.all_eq_true]
  constructor
  · intro checked other present different
    have comparison := checked other present
    simpa [different, compareAromaticCanonicalRule3RankedSubstituents,
      Ordering.byKey] using comparison
  · intro strict other present
    by_cases same : other.atom = candidate.atom
    · simp [same]
    · simpa [same, compareAromaticCanonicalRule3RankedSubstituents,
        Ordering.byKey] using strict other present same

/-- Select the unique represented strict constitutional maximum, if it exists. -/
noncomputable def aromaticCanonicalRule3ConstitutionalSeniorReference?
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalAtom := do
  let candidates := source.aromaticCanonicalRule3Substituents endpoint partner
  let ranked ← candidates.mapM
    (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint)
  let senior ← ranked.find? fun candidate =>
    source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked
  some senior.atom

/-- Independent source meaning of an accepted endpoint reference. -/
def DeclarativeAromaticCanonicalRule3ConstitutionalSeniorReference
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom) : Prop :=
  ∃ candidates ranked senior,
    candidates = source.aromaticCanonicalRule3Substituents endpoint partner ∧
      List.Forall₂
        (source.DeclarativeAromaticCanonicalRule3RankedSubstituent endpoint)
        candidates ranked ∧
      source.DeclarativeAromaticCanonicalRule3StrictlySenior ranked senior ∧
      senior.atom = reference

/-- Every selected endpoint reference is a complete, independently justified strict maximum. -/
theorem aromaticCanonicalRule3ConstitutionalSeniorReference?_sound
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (computed : source.aromaticCanonicalRule3ConstitutionalSeniorReference?
      endpoint partner = some reference) :
    source.DeclarativeAromaticCanonicalRule3ConstitutionalSeniorReference
      endpoint partner reference := by
  unfold aromaticCanonicalRule3ConstitutionalSeniorReference? at computed
  let candidates := source.aromaticCanonicalRule3Substituents endpoint partner
  cases rankedComputed : candidates.mapM
      (source.buildAromaticCanonicalRule3RankedSubstituent? endpoint) with
  | none => simp [candidates, rankedComputed] at computed
  | some ranked =>
      cases seniorComputed : ranked.find? fun candidate =>
          source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked with
      | none => simp [candidates, rankedComputed, seniorComputed] at computed
      | some senior =>
          simp [candidates, rankedComputed, seniorComputed] at computed
          subst reference
          have seniorChecked :
              source.aromaticCanonicalRule3StrictlyOutranksAll senior ranked = true :=
            @List.find?_some _
              (fun candidate =>
                source.aromaticCanonicalRule3StrictlyOutranksAll candidate ranked)
              senior ranked seniorComputed
          have seniorPresent : senior ∈ ranked := by
            rcases (List.find?_eq_some_iff_append.mp seniorComputed).2 with
              ⟨before, after, rankedIdentity, _checked⟩
            rw [rankedIdentity]
            simp
          refine ⟨candidates, ranked, senior, rfl, ?_,
            ⟨seniorPresent,
              (source.aromaticCanonicalRule3StrictlyOutranksAll_eq_true_iff
                senior ranked).mp seniorChecked⟩, rfl⟩
          apply source.mapM_buildAromaticCanonicalRule3RankedSubstituent?_sound
            endpoint partner candidates ranked
          · exact rankedComputed
          · intro candidate candidatePresent
            exact candidatePresent

/-- Direct source meaning of an exact spatial point. -/
def SemanticAromaticCanonicalSpatialPointAt
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) (point : CartesianPoint3) : Prop :=
  ∃ spatial, source.spatial? = some spatial ∧
    spatial.positions[atom.val]? = some point

theorem aromaticCanonicalSpatialPointAt?_eq_some_iff
    (source : AuthoritativeChemicalInput)
    (atom : source.AromaticCanonicalAtom) (point : CartesianPoint3) :
    source.aromaticCanonicalSpatialPointAt? atom = some point ↔
      source.SemanticAromaticCanonicalSpatialPointAt atom point := by
  unfold aromaticCanonicalSpatialPointAt?
    SemanticAromaticCanonicalSpatialPointAt
  cases spatialComputed : source.spatial? with
  | none => simp
  | some spatial => simp

/-- Successful source-level spatial Rule-3 result. -/
structure AromaticCanonicalRule3SpatialUnitResult
    (source : AuthoritativeChemicalInput) where
  leftReference : source.AromaticCanonicalAtom
  rightReference : source.AromaticCanonicalAtom
  geometry : OfficialRule3Geometry

/-- Analyze an ordinary source-canonical double bond from strict constitutional references and
exact rational coordinates. -/
noncomputable def aromaticCanonicalRule3SpatialUnit?
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialUnitResult := by
  classical
  exact
    if source.AromaticCanonicalOrdinaryDoubleBond left right then do
      let leftReference ←
        source.aromaticCanonicalRule3ConstitutionalSeniorReference? left right
      let rightReference ←
        source.aromaticCanonicalRule3ConstitutionalSeniorReference? right left
      let leftPoint ← source.aromaticCanonicalSpatialPointAt? left
      let rightPoint ← source.aromaticCanonicalSpatialPointAt? right
      let leftReferencePoint ← source.aromaticCanonicalSpatialPointAt? leftReference
      let rightReferencePoint ← source.aromaticCanonicalSpatialPointAt? rightReference
      let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
        leftReferencePoint rightReferencePoint
      some { leftReference, rightReference, geometry }
    else none

/-- Independent positive meaning of an emitted source-canonical Rule-3 spatial unit. -/
def DeclarativeAromaticCanonicalRule3SpatialUnit
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult) : Prop :=
  source.AromaticCanonicalOrdinaryDoubleBond left right ∧
    source.DeclarativeAromaticCanonicalRule3ConstitutionalSeniorReference
      left right result.leftReference ∧
    source.DeclarativeAromaticCanonicalRule3ConstitutionalSeniorReference
      right left result.rightReference ∧
    ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
      source.SemanticAromaticCanonicalSpatialPointAt left leftPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt right rightPoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        result.leftReference leftReferencePoint ∧
      source.SemanticAromaticCanonicalSpatialPointAt
        result.rightReference rightReferencePoint ∧
      RationalRule3SpatialGeometry leftPoint rightPoint
        leftReferencePoint rightReferencePoint result.geometry

/-- Every emitted source-canonical Rule-3 geometry is backed by an ordinary nonaromatic double
bond, two exhaustive strict branch maxima, direct source coordinates, and exact rational geometry. -/
theorem aromaticCanonicalRule3SpatialUnit?_sound
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialUnitResult)
    (computed : source.aromaticCanonicalRule3SpatialUnit? left right = some result) :
    source.DeclarativeAromaticCanonicalRule3SpatialUnit left right result := by
  unfold aromaticCanonicalRule3SpatialUnit? at computed
  by_cases ordinary : source.AromaticCanonicalOrdinaryDoubleBond left right
  · rw [if_pos ordinary] at computed
    cases leftReferenceComputed :
        source.aromaticCanonicalRule3ConstitutionalSeniorReference? left right with
    | none => simp [leftReferenceComputed] at computed
    | some leftReference =>
        cases rightReferenceComputed :
            source.aromaticCanonicalRule3ConstitutionalSeniorReference? right left with
        | none => simp [leftReferenceComputed, rightReferenceComputed] at computed
        | some rightReference =>
            cases leftPointComputed : source.aromaticCanonicalSpatialPointAt? left with
            | none =>
                simp [leftReferenceComputed, rightReferenceComputed,
                  leftPointComputed] at computed
            | some leftPoint =>
                cases rightPointComputed : source.aromaticCanonicalSpatialPointAt? right with
                | none =>
                    simp [leftReferenceComputed, rightReferenceComputed,
                      leftPointComputed, rightPointComputed] at computed
                | some rightPoint =>
                    cases leftReferencePointComputed :
                        source.aromaticCanonicalSpatialPointAt? leftReference with
                    | none =>
                        simp [leftReferenceComputed, rightReferenceComputed,
                          leftPointComputed, rightPointComputed,
                          leftReferencePointComputed] at computed
                    | some leftReferencePoint =>
                        cases rightReferencePointComputed :
                            source.aromaticCanonicalSpatialPointAt? rightReference with
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
                                refine ⟨ordinary,
                                  source.aromaticCanonicalRule3ConstitutionalSeniorReference?_sound
                                    left right leftReference leftReferenceComputed,
                                  source.aromaticCanonicalRule3ConstitutionalSeniorReference?_sound
                                    right left rightReference rightReferenceComputed,
                                  leftPoint, rightPoint, leftReferencePoint,
                                  rightReferencePoint, ?_, ?_, ?_, ?_, ?_⟩
                                · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                    left leftPoint).mp leftPointComputed
                                · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                    right rightPoint).mp rightPointComputed
                                · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                    leftReference leftReferencePoint).mp
                                      leftReferencePointComputed
                                · exact (source.aromaticCanonicalSpatialPointAt?_eq_some_iff
                                    rightReference rightReferencePoint).mp
                                      rightReferencePointComputed
                                · exact (rule3GeometryOfSpatialReferences?_eq_some_iff
                                    leftPoint rightPoint leftReferencePoint
                                      rightReferencePoint geometry).mp geometryComputed
  · simp [ordinary] at computed

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
