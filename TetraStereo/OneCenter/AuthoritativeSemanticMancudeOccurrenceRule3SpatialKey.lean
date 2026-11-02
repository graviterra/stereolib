import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3SpatialUnit
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRerootFrame

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Recursive source-canonical Rule-3 keys

This module lifts exact source-level Rule-3 units into the canonical occurrence zipper.  Each
child is compiled through Rules 1a--3 before sibling addresses are assigned, so a constitutional
tie cannot leak source enumeration order into the Rule-3 signature.

The key is explicitly `Uncancelled`: repeated occurrences of one physical unit are retained.
Opponent-independent physical-unit cancellation and coupled cyclic topology are the next layer.
-/

/-- One positive Rule-3 observation at a source-canonical provenance node. -/
structure AromaticCanonicalRule3SpatialNodeResult
    (source : AuthoritativeChemicalInput) where
  left : source.AromaticCanonicalAtom
  right : source.AromaticCanonicalAtom
  unit : source.AromaticCanonicalRule3SpatialUnitResult

/-- A provenance node is the real child end of an ordinary source-canonical order-two edge. -/
def AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    ∃ current parent,
      node.current? = some current ∧ node.parent? = some parent ∧
        source.AromaticCanonicalOrdinaryDoubleBond parent current

/-- Independent meaning of a positive node observation. -/
def DeclarativeAromaticCanonicalRule3SpatialNode
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialNodeResult) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    node.current? = some result.right ∧ node.parent? = some result.left ∧
    source.AromaticCanonicalOrdinaryDoubleBond result.left result.right ∧
    source.DeclarativeAromaticCanonicalRule3SpatialUnit
      result.left result.right result.unit

/-- Tri-state node observation: nonunit, resolved unit, or unresolved genuine unit. -/
noncomputable def aromaticCanonicalRule3SpatialNode?
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option (Option source.AromaticCanonicalRule3SpatialNodeResult) := by
  classical
  exact
    if node.provenance = OfficialCIPNodeProvenance.realAtom then
      match node.current?, node.parent? with
      | some current, some parent =>
          if source.AromaticCanonicalOrdinaryDoubleBond parent current then
            match source.aromaticCanonicalRule3SpatialUnit? parent current with
            | none => none
            | some unit => some (some { left := parent, right := current, unit := unit })
          else some none
      | _, _ => some none
    else some none

theorem aromaticCanonicalRule3SpatialNode?_sound
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialNodeResult)
    (computed : source.aromaticCanonicalRule3SpatialNode? node = some (some result)) :
    source.DeclarativeAromaticCanonicalRule3SpatialNode node result := by
  classical
  unfold aromaticCanonicalRule3SpatialNode? at computed
  by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real] at computed
    cases currentComputed : node.current? with
    | none => simp [currentComputed] at computed
    | some current =>
        cases parentComputed : node.parent? with
        | none => simp [currentComputed, parentComputed] at computed
        | some parent =>
            by_cases ordinary :
                source.AromaticCanonicalOrdinaryDoubleBond parent current
            · rw [currentComputed, parentComputed] at computed
              change (if source.AromaticCanonicalOrdinaryDoubleBond parent current then
                  match source.aromaticCanonicalRule3SpatialUnit? parent current with
                  | none => none
                  | some unit => some (some
                      ({ left := parent, right := current, unit := unit } :
                        source.AromaticCanonicalRule3SpatialNodeResult))
                else some none) = some (some result) at computed
              rw [if_pos ordinary] at computed
              cases unitComputed : source.aromaticCanonicalRule3SpatialUnit? parent current with
              | none => simp [unitComputed] at computed
              | some unit =>
                  simp [unitComputed] at computed
                  subst result
                  exact ⟨real, currentComputed, parentComputed, ordinary,
                    source.aromaticCanonicalRule3SpatialUnit?_sound
                      parent current unit unitComputed⟩
            · simp [currentComputed, parentComputed, ordinary] at computed
  · simp [real] at computed

theorem aromaticCanonicalRule3SpatialNode?_eq_some_none_implies_not_edge
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (computed : source.aromaticCanonicalRule3SpatialNode? node = some none) :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node := by
  classical
  rintro ⟨real, current, parent, currentComputed, parentComputed, ordinary⟩
  unfold aromaticCanonicalRule3SpatialNode? at computed
  rw [if_pos real, currentComputed, parentComputed] at computed
  change (if source.AromaticCanonicalOrdinaryDoubleBond parent current then
      match source.aromaticCanonicalRule3SpatialUnit? parent current with
      | none => none
      | some unit => some (some
          ({ left := parent, right := current, unit := unit } :
            source.AromaticCanonicalRule3SpatialNodeResult))
    else some none) = some none at computed
  rw [if_pos ordinary] at computed
  cases unitComputed : source.aromaticCanonicalRule3SpatialUnit? parent current <;>
    simp [unitComputed] at computed

/-- Independent meaning of a successfully resolved tri-state node observation. -/
inductive DeclarativeAromaticCanonicalRule3SpatialNodeOutcome
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  | structuralNonunit
      (notUnit : ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node) :
      source.DeclarativeAromaticCanonicalRule3SpatialNodeOutcome node none
  | geometry {result : source.AromaticCanonicalRule3SpatialNodeResult}
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNode node result) :
      source.DeclarativeAromaticCanonicalRule3SpatialNodeOutcome node (some result)

theorem aromaticCanonicalRule3SpatialNode?_outcome_sound
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult)
    (computed : source.aromaticCanonicalRule3SpatialNode? node = some outcome) :
    source.DeclarativeAromaticCanonicalRule3SpatialNodeOutcome node outcome := by
  cases outcome with
  | none =>
      exact DeclarativeAromaticCanonicalRule3SpatialNodeOutcome.structuralNonunit
        (source.aromaticCanonicalRule3SpatialNode?_eq_some_none_implies_not_edge
          node computed)
  | some result =>
      exact DeclarativeAromaticCanonicalRule3SpatialNodeOutcome.geometry
        (source.aromaticCanonicalRule3SpatialNode?_sound node result computed)

/-- Root observation layer. -/
def aromaticCanonicalRule3RootObservations
    (source : AuthoritativeChemicalInput) :
    Option source.AromaticCanonicalRule3SpatialNodeResult →
      List (List (OfficialSparseEntry source.AromaticCanonicalRule3SpatialNodeResult))
  | none => []
  | some result => [[([], result)]]

/-- Numeric Rule-3 projection of the same root observation. -/
def aromaticCanonicalRule3RootPriorities
    (source : AuthoritativeChemicalInput) :
    Option source.AromaticCanonicalRule3SpatialNodeResult →
      List (List (OfficialSparseEntry Nat))
  | none => []
  | some result => [[([], result.unit.geometry.priority)]]

/-- Bottom-up Rules-1a--3 source key before physical-unit cancellation. -/
structure AromaticCanonicalUncancelledRule3SpatialKey
    (source : AuthoritativeChemicalInput) where
  constitutional : ExactOfficialRuleMajorKey source.AromaticCanonicalAtom
  observations : List (List
    (OfficialSparseEntry source.AromaticCanonicalRule3SpatialNodeResult))
  rule3 : List (List (OfficialSparseEntry Nat))

/-- Exact Rules 1a--2 decide first; only their complete tie exposes Rule 3. -/
noncomputable def compareAromaticCanonicalUncancelledRule3SpatialKeys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.constitutional)
      (ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph))
    (Ordering.byKey (fun key => key.rule3)
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))

theorem compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalUncancelledRule3SpatialKeys := by
  letI : Std.TransCmp
      (ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph) :=
    ExactOfficialRuleMajorKey.compare_transCmp source.molecule.toLocalizedMoleculeGraph
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareAromaticCanonicalUncancelledRule3SpatialKeys
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

@[simp] theorem compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_gt
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (strict : ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph
      left.constitutional right.constitutional = Ordering.gt) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right = Ordering.gt := by
  simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, compareLex,
    Ordering.byKey, strict]

@[simp] theorem compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_eq
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (tied : ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph
      left.constitutional right.constitutional = Ordering.eq) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule3 right.rule3 := by
  simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, compareLex,
    Ordering.byKey, tied]

/-- Descending structural insertion under the cumulative Rules-1a--3 comparator. -/
def insertAromaticCanonicalUncancelledRule3SpatialKey
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalUncancelledRule3SpatialKey →
      List source.AromaticCanonicalUncancelledRule3SpatialKey
  | [] => [key]
  | head :: tail =>
      match compare key head with
      | .lt => head :: insertAromaticCanonicalUncancelledRule3SpatialKey compare key tail
      | .eq | .gt => key :: head :: tail

def sortAromaticCanonicalUncancelledRule3SpatialKeys
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering) :
    List source.AromaticCanonicalUncancelledRule3SpatialKey →
      List source.AromaticCanonicalUncancelledRule3SpatialKey
  | [] => []
  | key :: keys =>
      insertAromaticCanonicalUncancelledRule3SpatialKey compare key
        (sortAromaticCanonicalUncancelledRule3SpatialKeys compare keys)

theorem insertAromaticCanonicalUncancelledRule3SpatialKey_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    ∀ keys,
      (insertAromaticCanonicalUncancelledRule3SpatialKey compare key keys).Perm
        (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertAromaticCanonicalUncancelledRule3SpatialKey
      cases comparison : compare key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (insertAromaticCanonicalUncancelledRule3SpatialKey_perm
              compare key tail)).trans (List.Perm.swap key head tail)

theorem sortAromaticCanonicalUncancelledRule3SpatialKeys_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering) :
    ∀ keys,
      (sortAromaticCanonicalUncancelledRule3SpatialKeys compare keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (insertAromaticCanonicalUncancelledRule3SpatialKey_perm compare key
        (sortAromaticCanonicalUncancelledRule3SpatialKeys compare keys)).trans
          (List.Perm.cons key
            (sortAromaticCanonicalUncancelledRule3SpatialKeys_perm compare keys))

def AromaticCanonicalUncancelledRule3SpatialKeysDescending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) : Prop :=
  keys.Pairwise fun left right => compare left right ≠ Ordering.lt

theorem insertAromaticCanonicalUncancelledRule3SpatialKey_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering)
    [Std.TransCmp compare]
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    ∀ keys,
      AromaticCanonicalUncancelledRule3SpatialKeysDescending compare keys →
      AromaticCanonicalUncancelledRule3SpatialKeysDescending compare
        (insertAromaticCanonicalUncancelledRule3SpatialKey compare key keys)
  | [], _ => by
      simp [insertAromaticCanonicalUncancelledRule3SpatialKey,
        AromaticCanonicalUncancelledRule3SpatialKeysDescending]
  | head :: tail, sorted => by
      have headOverTail : ∀ observed ∈ tail,
          compare head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted :
          AromaticCanonicalUncancelledRule3SpatialKeysDescending compare tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertAromaticCanonicalUncancelledRule3SpatialKey
      cases comparison : compare key head with
      | gt =>
          rw [AromaticCanonicalUncancelledRule3SpatialKeysDescending,
            List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [AromaticCanonicalUncancelledRule3SpatialKeysDescending,
            List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted :=
            insertAromaticCanonicalUncancelledRule3SpatialKey_descending
              compare key tail tailSorted
          rw [AromaticCanonicalUncancelledRule3SpatialKeysDescending,
            List.pairwise_cons]
          constructor
          · intro observed present
            have permutation :=
              insertAromaticCanonicalUncancelledRule3SpatialKey_perm
                compare key tail
            have sourcePresent : observed ∈ key :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse : compare head key = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortAromaticCanonicalUncancelledRule3SpatialKeys_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalUncancelledRule3SpatialKey →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Ordering)
    [Std.TransCmp compare] :
    ∀ keys,
      AromaticCanonicalUncancelledRule3SpatialKeysDescending compare
        (sortAromaticCanonicalUncancelledRule3SpatialKeys compare keys)
  | [] => by
      simp [sortAromaticCanonicalUncancelledRule3SpatialKeys,
        AromaticCanonicalUncancelledRule3SpatialKeysDescending]
  | key :: keys =>
      insertAromaticCanonicalUncancelledRule3SpatialKey_descending compare key
        (sortAromaticCanonicalUncancelledRule3SpatialKeys compare keys)
        (sortAromaticCanonicalUncancelledRule3SpatialKeys_descending compare keys)

def aromaticCanonicalRule3ObservationChildLayerCount
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalUncancelledRule3SpatialKey) : Nat :=
  children.foldl (fun longest child => max longest child.observations.length) 0

def mergeAromaticCanonicalRule3ObservationChildren
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List (List (OfficialSparseEntry source.AromaticCanonicalRule3SpatialNodeResult)) :=
  let count := aromaticCanonicalRule3ObservationChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2
        (child.1.observations.getD depth [])

def aromaticCanonicalRule3PriorityChildLayerCount
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalUncancelledRule3SpatialKey) : Nat :=
  children.foldl (fun longest child => max longest child.rule3.length) 0

def mergeAromaticCanonicalRule3PriorityChildren
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List (List (OfficialSparseEntry Nat)) :=
  let count := aromaticCanonicalRule3PriorityChildLayerCount children
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.rule3.getD depth [])

/-- Compile one source-canonical occurrence branch bottom-up through Rule 3. -/
noncomputable def buildAromaticCanonicalUncancelledRule3SpatialKey?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalUncancelledRule3SpatialKey
  | 0, cursor => do
      let children := source.aromaticCanonicalRerootChildren cursor
      let observation ← source.aromaticCanonicalRule3SpatialNode? cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }
      else none
  | fuel + 1, cursor => do
      let children := source.aromaticCanonicalRerootChildren cursor
      let observation ← source.aromaticCanonicalRule3SpatialNode? cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }
      else
        let childKeys ← children.mapM
          (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel)
        let compare := source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        let sorted := sortAromaticCanonicalUncancelledRule3SpatialKeys compare childKeys
        some
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := source.aromaticCanonicalRule3RootObservations observation ++
              mergeAromaticCanonicalRule3ObservationChildren sorted
            rule3 := source.aromaticCanonicalRule3RootPriorities observation ++
              mergeAromaticCanonicalRule3PriorityChildren sorted }

mutual

inductive DeclarativeAromaticCanonicalUncancelledRule3SpatialKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
  | zeroLeaf {cursor children observation}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNodeOutcome
        cursor.occurrence.1.node observation) :
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKey 0 cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          observations := source.aromaticCanonicalRule3RootObservations observation
          rule3 := source.aromaticCanonicalRule3RootPriorities observation }
  | successorLeaf {fuel cursor children observation}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNodeOutcome
        cursor.occurrence.1.node observation) :
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKey (fuel + 1) cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          observations := source.aromaticCanonicalRule3RootObservations observation
          rule3 := source.aromaticCanonicalRule3RootPriorities observation }
  | successorBranch {fuel cursor children observation childKeys sorted}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (nonterminal : children ≠ [])
      (observed : source.DeclarativeAromaticCanonicalRule3SpatialNodeOutcome
        cursor.occurrence.1.node observation)
      (childrenDerived :
        source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
          fuel children childKeys)
      (permutation : sorted.Perm childKeys)
      (descending : AromaticCanonicalUncancelledRule3SpatialKeysDescending
        source.compareAromaticCanonicalUncancelledRule3SpatialKeys sorted) :
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKey
        (fuel + 1) cursor
        { constitutional := ExactOfficialRuleMajorKey.assemble
            (MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node false)
            (sorted.map fun child => child.constitutional)
          observations := source.aromaticCanonicalRule3RootObservations observation ++
            mergeAromaticCanonicalRule3ObservationChildren sorted
          rule3 := source.aromaticCanonicalRule3RootPriorities observation ++
            mergeAromaticCanonicalRule3PriorityChildren sorted }

inductive DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
      List source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
  | nil (fuel : Nat) :
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList fuel [] []
  | cons {fuel cursor cursors key keys}
      (head : source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKey
        fuel cursor key)
      (tail : source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
        fuel cursors keys) :
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
        fuel (cursor :: cursors) (key :: keys)

end

private theorem mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (sound : ∀ (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalUncancelledRule3SpatialKey),
      source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel cursor = some key →
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKey fuel cursor key) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey),
      cursors.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) =
          some keys →
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
        fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact .nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed :
          source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact .cons (sound cursor head headComputed)
                (mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound
                  source sound cursors tail tailComputed)

/-- Every executable uncancelled key satisfies the independent recursive source semantics. -/
theorem buildAromaticCanonicalUncancelledRule3SpatialKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalUncancelledRule3SpatialKey),
      source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel cursor = some key →
      source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKey fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalUncancelledRule3SpatialKey? at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      cases observationComputed :
          source.aromaticCanonicalRule3SpatialNode? cursor.occurrence.1.node with
      | none => simp [observationComputed] at computed
      | some observation =>
          by_cases terminal : children = []
          · simp [children, observationComputed, terminal] at computed
            subst key
            exact .zeroLeaf
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
              (source.aromaticCanonicalRule3SpatialNode?_outcome_sound
                cursor.occurrence.1.node observation observationComputed)
          · simp [children, observationComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalUncancelledRule3SpatialKey? at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      cases observationComputed :
          source.aromaticCanonicalRule3SpatialNode? cursor.occurrence.1.node with
      | none => simp [observationComputed] at computed
      | some observation =>
          by_cases terminal : children = []
          · simp [children, observationComputed, terminal] at computed
            subst key
            exact .successorLeaf
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
              (source.aromaticCanonicalRule3SpatialNode?_outcome_sound
                cursor.occurrence.1.node observation observationComputed)
          · cases childKeysComputed : children.mapM
                (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) with
            | none =>
                simp [children, observationComputed, terminal,
                  childKeysComputed] at computed
            | some childKeys =>
                let compare :=
                  source.compareAromaticCanonicalUncancelledRule3SpatialKeys
                let sorted :=
                  sortAromaticCanonicalUncancelledRule3SpatialKeys compare childKeys
                simp [children, observationComputed, terminal, childKeysComputed] at computed
                subst key
                letI : Std.TransCmp compare :=
                  source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
                exact .successorBranch
                  (source.aromaticCanonicalRerootChildren_sound cursor) terminal
                  (source.aromaticCanonicalRule3SpatialNode?_outcome_sound
                    cursor.occurrence.1.node observation observationComputed)
                  (mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound
                    source
                    (source.buildAromaticCanonicalUncancelledRule3SpatialKey?_sound fuel)
                    children childKeys childKeysComputed)
                  (sortAromaticCanonicalUncancelledRule3SpatialKeys_perm
                    compare childKeys)
                  (sortAromaticCanonicalUncancelledRule3SpatialKeys_descending
                    compare childKeys)

/-- Pointwise lifting of uncancelled Rule-3 builder soundness through `List.mapM`.  This public
boundary lets downstream structural theorems reason over the declarative key list without
duplicating the executable `mapM` case split. -/
theorem mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound_list
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (computed : cursors.mapM
      (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) = some keys) :
    source.DeclarativeAromaticCanonicalUncancelledRule3SpatialKeyList
      fuel cursors keys :=
  mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_sound source
    (source.buildAromaticCanonicalUncancelledRule3SpatialKey?_sound fuel)
    cursors keys computed

/-- The source-recursive Rule-3 compiler has no Kekule-selection input. -/
theorem buildAromaticCanonicalUncancelledRule3SpatialKey_source_fixed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel cursor =
      source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel cursor :=
  rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
