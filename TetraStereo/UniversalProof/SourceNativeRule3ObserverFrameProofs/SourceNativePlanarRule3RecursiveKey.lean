import TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CanonicalFrameExact

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey

open TetraStereo.OneCenter
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit

























def CanonicalAromaticCanonicalPlanarRule3Node
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialNodeResult) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    node.current? = some result.right ∧
    node.parent? = some result.left ∧
    source.AromaticCanonicalOrdinaryDoubleBond result.left result.right ∧
    CanonicalAromaticCanonicalPlanarRule3Unit source result.left result.right result.unit

/-- Source-native planar tri-state node reader: structural nonunit `some none`, genuine ordinary
double bond with unresolved planar unit outer `none`, resolved genuine unit `some (some result)`.
No spatial record is consulted and no three-dimensional coordinate is fabricated. -/
noncomputable def aromaticCanonicalPlanarRule3Node?
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option (Option source.AromaticCanonicalRule3SpatialNodeResult) := by
  classical
  exact
    if node.provenance = OfficialCIPNodeProvenance.realAtom then
      match node.current?, node.parent? with
      | some current, some parent =>
          if source.AromaticCanonicalOrdinaryDoubleBond parent current then
            match aromaticCanonicalPlanarRule3Unit? source parent current with
            | none => none
            | some unit => some (some { left := parent, right := current, unit := unit })
          else some none
      | _, _ => some none
    else some none

/-- Positive planar node execution is exactly its canonical source relation. -/
theorem aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialNodeResult) :
    aromaticCanonicalPlanarRule3Node? source node = some (some result) ↔
      CanonicalAromaticCanonicalPlanarRule3Node source node result := by
  classical
  constructor
  · intro computed
    unfold aromaticCanonicalPlanarRule3Node? at computed
    by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
    · rw [if_pos real] at computed
      cases currentComputed : node.current? with
      | none => simp [currentComputed] at computed
      | some current =>
          cases parentComputed : node.parent? with
          | none => simp [currentComputed, parentComputed] at computed
          | some parent =>
              by_cases ordinary : source.AromaticCanonicalOrdinaryDoubleBond parent current
              · rw [currentComputed, parentComputed] at computed
                change (if source.AromaticCanonicalOrdinaryDoubleBond parent current then
                    match aromaticCanonicalPlanarRule3Unit? source parent current with
                    | none => none
                    | some unit => some (some
                        ({ left := parent, right := current, unit := unit } :
                          source.AromaticCanonicalRule3SpatialNodeResult))
                  else some none) = some (some result) at computed
                rw [if_pos ordinary] at computed
                cases unitComputed : aromaticCanonicalPlanarRule3Unit? source parent current with
                | none => simp [unitComputed] at computed
                | some unit =>
                    simp [unitComputed] at computed
                    subst result
                    exact ⟨real, currentComputed, parentComputed, ordinary,
                      (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical
                        source parent current unit).mp unitComputed⟩
              · simp [currentComputed, parentComputed, ordinary] at computed
    · simp [real] at computed
  · rintro ⟨real, current, parent, ordinary, unitDerived⟩
    have unitComputed :=
      (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical
        source result.left result.right result.unit).mpr unitDerived
    unfold aromaticCanonicalPlanarRule3Node?
    rw [if_pos real, current, parent]
    simp [ordinary, unitComputed]

/-- A structural nonunit computes to the resolved negative planar reading. -/
theorem aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (notEdge : ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node) :
    aromaticCanonicalPlanarRule3Node? source node = some none := by
  classical
  unfold aromaticCanonicalPlanarRule3Node?
  by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real]
    cases currentComputed : node.current? with
    | none => simp
    | some current =>
        cases parentComputed : node.parent? with
        | none => simp
        | some parent =>
            have notOrdinary :
                ¬ source.AromaticCanonicalOrdinaryDoubleBond parent current := by
              intro ordinary
              exact notEdge ⟨real, current, parent,
                currentComputed, parentComputed, ordinary⟩
            simp [notOrdinary]
  · simp [real]

/-- The resolved negative planar reading is exactly a structural nonunit; it is never produced by a
genuine ordinary double-bond node. -/
theorem aromaticCanonicalPlanarRule3Node?_eq_some_none_implies_not_edge
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (computed : aromaticCanonicalPlanarRule3Node? source node = some none) :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node := by
  classical
  rintro ⟨real, current, parent, currentComputed, parentComputed, ordinary⟩
  unfold aromaticCanonicalPlanarRule3Node? at computed
  rw [if_pos real, currentComputed, parentComputed] at computed
  change (if source.AromaticCanonicalOrdinaryDoubleBond parent current then
      match aromaticCanonicalPlanarRule3Unit? source parent current with
      | none => none
      | some unit => some (some
          ({ left := parent, right := current, unit := unit } :
            source.AromaticCanonicalRule3SpatialNodeResult))
    else some none) = some none at computed
  rw [if_pos ordinary] at computed
  cases unitComputed : aromaticCanonicalPlanarRule3Unit? source parent current <;>
    simp [unitComputed] at computed

/-- Independent tri-state planar node outcome: the resolved negative says exactly that the node has
no ordinary double-bond edge; the positive carries the canonical planar node. -/
def CanonicalAromaticCanonicalPlanarRule3NodeOutcome
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  | none => ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node
  | some result => CanonicalAromaticCanonicalPlanarRule3Node source node result

/-- Tri-state planar node execution is exactly the independent node-outcome relation. -/
theorem aromaticCanonicalPlanarRule3Node?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult) :
    aromaticCanonicalPlanarRule3Node? source node = some outcome ↔
      CanonicalAromaticCanonicalPlanarRule3NodeOutcome source node outcome := by
  cases outcome with
  | none =>
      exact ⟨aromaticCanonicalPlanarRule3Node?_eq_some_none_implies_not_edge source node,
        aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source node⟩
  | some result =>
      exact aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical source node result

/-- The outer `none` is exactly a genuine ordinary double-bond node whose actual planar unit has no
canonical derivation: an unresolved genuine unit is not a neutral reading. -/
theorem aromaticCanonicalPlanarRule3Node?_eq_none_iff_unresolved
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    aromaticCanonicalPlanarRule3Node? source node = none ↔
      source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node ∧
        ¬ ∃ result, CanonicalAromaticCanonicalPlanarRule3Node source node result := by
  classical
  constructor
  · intro computed
    unfold aromaticCanonicalPlanarRule3Node? at computed
    by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
    · rw [if_pos real] at computed
      cases currentComputed : node.current? with
      | none => simp [currentComputed] at computed
      | some current =>
          cases parentComputed : node.parent? with
          | none => simp [currentComputed, parentComputed] at computed
          | some parent =>
              by_cases ordinary : source.AromaticCanonicalOrdinaryDoubleBond parent current
              · rw [currentComputed, parentComputed] at computed
                change (if source.AromaticCanonicalOrdinaryDoubleBond parent current then
                    match aromaticCanonicalPlanarRule3Unit? source parent current with
                    | none => none
                    | some unit => some (some
                        ({ left := parent, right := current, unit := unit } :
                          source.AromaticCanonicalRule3SpatialNodeResult))
                  else some none) = none at computed
                rw [if_pos ordinary] at computed
                cases unitComputed : aromaticCanonicalPlanarRule3Unit? source parent current with
                | none =>
                    simp [unitComputed] at computed
                    refine ⟨⟨real, current, parent,
                      currentComputed, parentComputed, ordinary⟩, ?_⟩
                    rintro ⟨result, canonical⟩
                    obtain ⟨_, resultCurrent, resultParent, _, unitCanonical⟩ := canonical
                    cases result with
                    | mk left right unit =>
                        have rightEq : right = current :=
                          Option.some.inj (resultCurrent.symm.trans currentComputed)
                        have leftEq : left = parent :=
                          Option.some.inj (resultParent.symm.trans parentComputed)
                        have resolved :=
                          (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical
                            source left right unit).mpr unitCanonical
                        rw [leftEq, rightEq, unitComputed] at resolved
                        simp at resolved
                | some unit => simp [unitComputed] at computed
              · simp [currentComputed, parentComputed, ordinary] at computed
    · simp [real] at computed
  · rintro ⟨⟨real, current, parent, currentComputed, parentComputed, ordinary⟩, noCanonical⟩
    unfold aromaticCanonicalPlanarRule3Node?
    rw [if_pos real, currentComputed, parentComputed]
    change (if source.AromaticCanonicalOrdinaryDoubleBond parent current then
        match aromaticCanonicalPlanarRule3Unit? source parent current with
        | none => none
        | some unit => some (some
            ({ left := parent, right := current, unit := unit } :
              source.AromaticCanonicalRule3SpatialNodeResult))
      else some none) = none
    rw [if_pos ordinary]
    cases unitComputed : aromaticCanonicalPlanarRule3Unit? source parent current with
    | none => rfl
    | some unit =>
        exact absurd
          ⟨{ left := parent, right := current, unit := unit },
            ⟨real, currentComputed, parentComputed, ordinary,
              (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical
                source parent current unit).mp unitComputed⟩⟩
          noCanonical

/-- Common physical-unit exclusion applied strictly after planar observation.  An unresolved
genuine unit (outer `none`) is untouched; a resolved unit whose identity is excluded becomes
`some none`; a retained resolved unit is preserved with its provenance. -/
noncomputable def aromaticCanonicalPlanarRule3NodeExcept?
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option (Option source.AromaticCanonicalRule3SpatialNodeResult) :=
  match aromaticCanonicalPlanarRule3Node? source node with
  | none => none
  | some none => some none
  | some (some result) =>
      if excluded.contains result.physicalUnitId then some none
      else some (some result)

/-- Independent meaning of one exclusion-aware planar node outcome. -/
def CanonicalAromaticCanonicalPlanarRule3NodeExceptOutcome
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  | none =>
      (¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node) ∨
        ∃ result, CanonicalAromaticCanonicalPlanarRule3Node source node result ∧
          result.physicalUnitId ∈ excluded
  | some result =>
      CanonicalAromaticCanonicalPlanarRule3Node source node result ∧
        result.physicalUnitId ∉ excluded

/-- Common-exclusion planar node execution is exactly its independent outcome relation. -/
theorem aromaticCanonicalPlanarRule3NodeExcept?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult) :
    aromaticCanonicalPlanarRule3NodeExcept? source excluded node = some outcome ↔
      CanonicalAromaticCanonicalPlanarRule3NodeExceptOutcome
        source excluded node outcome := by
  constructor
  · intro computed
    unfold aromaticCanonicalPlanarRule3NodeExcept? at computed
    cases originalComputed : aromaticCanonicalPlanarRule3Node? source node with
    | none => simp [originalComputed] at computed
    | some original =>
        cases original with
        | none =>
            simp [originalComputed] at computed
            subst outcome
            exact Or.inl
              ((aromaticCanonicalPlanarRule3Node?_eq_some_iff_canonical
                source node none).mp originalComputed)
        | some result =>
            have positive :=
              (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical
                source node result).mp originalComputed
            by_cases excludedIdentity : result.physicalUnitId ∈ excluded
            · simp [originalComputed, excludedIdentity] at computed
              subst outcome
              exact Or.inr ⟨result, positive, excludedIdentity⟩
            · simp [originalComputed, excludedIdentity] at computed
              subst outcome
              exact ⟨positive, excludedIdentity⟩
  · intro canonical
    cases outcome with
    | none =>
        rcases canonical with notEdge | ⟨result, positive, excludedIdentity⟩
        · have original :=
            (aromaticCanonicalPlanarRule3Node?_eq_some_iff_canonical
              source node none).mpr notEdge
          simp [aromaticCanonicalPlanarRule3NodeExcept?, original]
        · have original :=
            (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical
              source node result).mpr positive
          simp [aromaticCanonicalPlanarRule3NodeExcept?, original, excludedIdentity]
    | some result =>
        rcases canonical with ⟨positive, freshIdentity⟩
        have original :=
          (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical
            source node result).mpr positive
        simp [aromaticCanonicalPlanarRule3NodeExcept?, original, freshIdentity]

/-- An unresolved genuine unit remains the outer `none` under any common exclusion list, since the
exclusion callback runs strictly after observation. -/
theorem aromaticCanonicalPlanarRule3NodeExcept?_eq_none_of_node_none
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (unresolved : aromaticCanonicalPlanarRule3Node? source node = none) :
    aromaticCanonicalPlanarRule3NodeExcept? source excluded node = none := by
  unfold aromaticCanonicalPlanarRule3NodeExcept?
  simp [unresolved]

/-- A resolved planar unit whose actual physical identity is excluded becomes `some none`, retaining
the independent planar node meaning as the excluded witness. -/
theorem aromaticCanonicalPlanarRule3NodeExcept?_eq_some_none_of_excluded
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialNodeResult)
    (resolved : CanonicalAromaticCanonicalPlanarRule3Node source node result)
    (excludedIdentity : result.physicalUnitId ∈ excluded) :
    aromaticCanonicalPlanarRule3NodeExcept? source excluded node = some none :=
  (aromaticCanonicalPlanarRule3NodeExcept?_eq_some_iff_canonical
    source excluded node none).mpr (Or.inr ⟨result, resolved, excludedIdentity⟩)

/-- Recursive planar key compilation: the generic Rules-1a--3 compiler at the source-native planar
node reader. -/
noncomputable def buildAromaticCanonicalPlanarRule3Key?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalUncancelledRule3SpatialKey :=
  source.buildAromaticCanonicalRule3SpatialKeyWith?
    (aromaticCanonicalPlanarRule3Node? source)

/-- Independent recursive planar Rule-3 key judgment. -/
abbrev CanonicalAromaticCanonicalPlanarRule3Key
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyWith (carrierFuel := carrierFuel)
    (CanonicalAromaticCanonicalPlanarRule3NodeOutcome source)

/-- Recursive planar key compilation is exactly the independent recursive judgment. -/
theorem buildAromaticCanonicalPlanarRule3Key?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    buildAromaticCanonicalPlanarRule3Key? source fuel cursor = some key ↔
      CanonicalAromaticCanonicalPlanarRule3Key source fuel cursor key := by
  unfold buildAromaticCanonicalPlanarRule3Key?
  exact source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    (aromaticCanonicalPlanarRule3Node? source)
    (CanonicalAromaticCanonicalPlanarRule3NodeOutcome source)
    (aromaticCanonicalPlanarRule3Node?_eq_some_iff_canonical source)
    fuel cursor key

/-- Every emitted recursive planar key retains the independent judgment. -/
theorem buildAromaticCanonicalPlanarRule3Key?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : buildAromaticCanonicalPlanarRule3Key? source fuel cursor = some key) :
    CanonicalAromaticCanonicalPlanarRule3Key source fuel cursor key :=
  (buildAromaticCanonicalPlanarRule3Key?_eq_some_iff_canonical source fuel cursor key).mp computed

/-- Every independent recursive planar key is emitted. -/
theorem buildAromaticCanonicalPlanarRule3Key?_complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (canonical : CanonicalAromaticCanonicalPlanarRule3Key source fuel cursor key) :
    buildAromaticCanonicalPlanarRule3Key? source fuel cursor = some key :=
  (buildAromaticCanonicalPlanarRule3Key?_eq_some_iff_canonical source fuel cursor key).mpr canonical

/-- Recursive planar key compilation under one global common exclusion list. -/
noncomputable def buildAromaticCanonicalPlanarRule3KeyExcept?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalUncancelledRule3SpatialKey :=
  source.buildAromaticCanonicalRule3SpatialKeyWith?
    (aromaticCanonicalPlanarRule3NodeExcept? source excluded)

/-- Independent recursive planar key judgment under one global common exclusion list. -/
abbrev CanonicalAromaticCanonicalPlanarRule3KeyExcept
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyWith (carrierFuel := carrierFuel)
    (CanonicalAromaticCanonicalPlanarRule3NodeExceptOutcome source excluded)

/-- Common-exclusion recursive planar key compilation is exactly its independent judgment. -/
theorem buildAromaticCanonicalPlanarRule3KeyExcept?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    buildAromaticCanonicalPlanarRule3KeyExcept? source excluded fuel cursor = some key ↔
      CanonicalAromaticCanonicalPlanarRule3KeyExcept source excluded fuel cursor key := by
  unfold buildAromaticCanonicalPlanarRule3KeyExcept?
  exact source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    (aromaticCanonicalPlanarRule3NodeExcept? source excluded)
    (CanonicalAromaticCanonicalPlanarRule3NodeExceptOutcome source excluded)
    (aromaticCanonicalPlanarRule3NodeExcept?_eq_some_iff_canonical source excluded)
    fuel cursor key

/-- Every emitted common-exclusion planar key retains the independent judgment. -/
theorem buildAromaticCanonicalPlanarRule3KeyExcept?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : buildAromaticCanonicalPlanarRule3KeyExcept? source excluded fuel cursor =
      some key) :
    CanonicalAromaticCanonicalPlanarRule3KeyExcept source excluded fuel cursor key :=
  (buildAromaticCanonicalPlanarRule3KeyExcept?_eq_some_iff_canonical
    source excluded fuel cursor key).mp computed

/-- Every independent common-exclusion planar key is emitted. -/
theorem buildAromaticCanonicalPlanarRule3KeyExcept?_complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (canonical : CanonicalAromaticCanonicalPlanarRule3KeyExcept source excluded fuel cursor key) :
    buildAromaticCanonicalPlanarRule3KeyExcept? source excluded fuel cursor = some key :=
  (buildAromaticCanonicalPlanarRule3KeyExcept?_eq_some_iff_canonical
    source excluded fuel cursor key).mpr canonical

end TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
