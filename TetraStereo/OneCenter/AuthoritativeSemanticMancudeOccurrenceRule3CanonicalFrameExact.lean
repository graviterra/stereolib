import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3FuelCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3SpatialUnitExact

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact source-canonical Rule-3 frame semantics

This module removes the recursive Rule-3 tree compiler from the proof boundary.  A generic
structural compiler is characterized by independent node outcomes, exact stable insertion, and
exact stable sorting.  Both the uncancelled pass and the common-exclusion pass are instances of
that theorem.  The physical-topology resolver is also proved equivalent to its exhaustive
declarative relation, yielding an exact two-pass frame theorem.

The leaf geometry relation is supplied by the exact source spatial-unit theorem: constitutional
branch expansion, stable priority sorting, strict senior-reference selection, coordinate lookup,
and rational geometry are all relational.  Thus recursive occurrence traversal, sibling order,
topology selection, common cancellation, and the positive leaf are no longer opaque executable
premises.
-/

/-- Canonical positive meaning of one Rule-3 node, including the relational source spatial unit. -/
def CanonicalAromaticCanonicalRule3SpatialNode
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialNodeResult) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    node.current? = some result.right ∧
    node.parent? = some result.left ∧
    source.AromaticCanonicalOrdinaryDoubleBond result.left result.right ∧
    source.CanonicalAromaticCanonicalRule3SpatialUnit
      result.left result.right result.unit

/-- Positive node execution is exactly its canonical source relation. -/
theorem aromaticCanonicalRule3SpatialNode?_eq_some_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (result : source.AromaticCanonicalRule3SpatialNodeResult) :
    source.aromaticCanonicalRule3SpatialNode? node = some (some result) ↔
      source.CanonicalAromaticCanonicalRule3SpatialNode node result := by
  classical
  constructor
  · intro computed
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
                cases unitComputed :
                    source.aromaticCanonicalRule3SpatialUnit? parent current with
                | none => simp [unitComputed] at computed
                | some unit =>
                    simp [unitComputed] at computed
                    subst result
                    exact ⟨real, currentComputed, parentComputed, ordinary,
                      (source.aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
                        parent current unit).mp unitComputed⟩
              · simp [currentComputed, parentComputed, ordinary] at computed
    · simp [real] at computed
  · rintro ⟨real, current, parent, ordinary, unitDerived⟩
    have unitComputed :=
      (source.aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
        result.left result.right result.unit).mpr unitDerived
    unfold aromaticCanonicalRule3SpatialNode?
    rw [if_pos real, current, parent]
    simp [ordinary, unitComputed]

/-- Canonical successful tri-state node result. -/
def CanonicalAromaticCanonicalRule3SpatialNodeOutcome
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  | none => ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node
  | some result => source.CanonicalAromaticCanonicalRule3SpatialNode node result

/-- Tri-state node execution is exactly the canonical node-outcome relation. -/
theorem aromaticCanonicalRule3SpatialNode?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult) :
    source.aromaticCanonicalRule3SpatialNode? node = some outcome ↔
      source.CanonicalAromaticCanonicalRule3SpatialNodeOutcome node outcome := by
  cases outcome with
  | none =>
      exact ⟨source.aromaticCanonicalRule3SpatialNode?_eq_some_none_implies_not_edge node,
        source.aromaticCanonicalRule3SpatialNode?_eq_some_none_of_not_edge node⟩
  | some result =>
      exact source.aromaticCanonicalRule3SpatialNode?_eq_some_some_iff_canonical
        node result

/-- Canonical outcome after applying a common physical-unit exclusion policy. -/
def CanonicalAromaticCanonicalRule3SpatialNodeExceptOutcome
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  | none =>
      (¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node) ∨
        ∃ result, source.CanonicalAromaticCanonicalRule3SpatialNode node result ∧
          result.physicalUnitId ∈ excluded
  | some result =>
      source.CanonicalAromaticCanonicalRule3SpatialNode node result ∧
        result.physicalUnitId ∉ excluded

/-- Common-exclusion node execution is exactly its canonical outcome relation. -/
theorem aromaticCanonicalRule3SpatialNodeExcept?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom)
    (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult) :
    source.aromaticCanonicalRule3SpatialNodeExcept? excluded node = some outcome ↔
      source.CanonicalAromaticCanonicalRule3SpatialNodeExceptOutcome
        excluded node outcome := by
  constructor
  · intro computed
    unfold aromaticCanonicalRule3SpatialNodeExcept? at computed
    cases originalComputed : source.aromaticCanonicalRule3SpatialNode? node with
    | none => simp [originalComputed] at computed
    | some original =>
        cases original with
        | none =>
            simp [originalComputed] at computed
            subst outcome
            exact Or.inl
              ((source.aromaticCanonicalRule3SpatialNode?_eq_some_iff_canonical
                node none).mp originalComputed)
        | some result =>
            have positive :=
              (source.aromaticCanonicalRule3SpatialNode?_eq_some_some_iff_canonical
                node result).mp originalComputed
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
            (source.aromaticCanonicalRule3SpatialNode?_eq_some_iff_canonical
              node none).mpr notEdge
          simp [aromaticCanonicalRule3SpatialNodeExcept?, original]
        · have original :=
            (source.aromaticCanonicalRule3SpatialNode?_eq_some_some_iff_canonical
              node result).mpr positive
          simp [aromaticCanonicalRule3SpatialNodeExcept?, original, excludedIdentity]
    | some result =>
        rcases canonical with ⟨positive, freshIdentity⟩
        have original :=
          (source.aromaticCanonicalRule3SpatialNode?_eq_some_some_iff_canonical
            node result).mpr positive
        simp [aromaticCanonicalRule3SpatialNodeExcept?, original, freshIdentity]

/-- Generic Rule-3 recursive compiler parameterized by the exact node reader. -/
noncomputable def buildAromaticCanonicalRule3SpatialKeyWith?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (observe : OfficialCIPNode source.AromaticCanonicalAtom →
      Option (Option source.AromaticCanonicalRule3SpatialNodeResult)) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalUncancelledRule3SpatialKey
  | 0, cursor => do
      let children := source.aromaticCanonicalRerootChildren cursor
      let observation ← observe cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }
      else none
  | fuel + 1, cursor => do
      let children := source.aromaticCanonicalRerootChildren cursor
      let observation ← observe cursor.occurrence.1.node
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }
      else
        let childKeys ← children.mapM
          (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel)
        let sorted := sortAromaticCanonicalUncancelledRule3SpatialKeys
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys childKeys
        some
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := source.aromaticCanonicalRule3RootObservations observation ++
              mergeAromaticCanonicalRule3ObservationChildren sorted
            rule3 := source.aromaticCanonicalRule3RootPriorities observation ++
              mergeAromaticCanonicalRule3PriorityChildren sorted }

/-- The production uncancelled compiler is the generic compiler at the ordinary node reader. -/
theorem buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_with
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :
    source.buildAromaticCanonicalUncancelledRule3SpatialKey?
        (carrierFuel := carrierFuel) =
      source.buildAromaticCanonicalRule3SpatialKeyWith?
        source.aromaticCanonicalRule3SpatialNode? := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      funext cursor
      unfold buildAromaticCanonicalUncancelledRule3SpatialKey?
        buildAromaticCanonicalRule3SpatialKeyWith?
      rw [ih]

/-- The production exclusion compiler is the generic compiler at the exclusion-aware reader. -/
theorem buildAromaticCanonicalRule3SpatialKeyExcept?_eq_with
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    source.buildAromaticCanonicalRule3SpatialKeyExcept?
        (carrierFuel := carrierFuel) excluded =
      source.buildAromaticCanonicalRule3SpatialKeyWith?
        (source.aromaticCanonicalRule3SpatialNodeExcept? excluded) := by
  funext fuel
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      funext cursor
      unfold buildAromaticCanonicalRule3SpatialKeyExcept?
        buildAromaticCanonicalRule3SpatialKeyWith?
      rw [ih]

/-- Canonical insertion under the complete Rules-1a--3 comparator. -/
inductive DeclarativeInsertAromaticCanonicalRule3SpatialKey
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    List source.AromaticCanonicalUncancelledRule3SpatialKey →
      List source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
  | nil : DeclarativeInsertAromaticCanonicalRule3SpatialKey source key [] [key]
  | beforeEq {head tail}
      (compared : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        key head = .eq) :
      DeclarativeInsertAromaticCanonicalRule3SpatialKey source key
        (head :: tail) (key :: head :: tail)
  | beforeGt {head tail}
      (compared : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        key head = .gt) :
      DeclarativeInsertAromaticCanonicalRule3SpatialKey source key
        (head :: tail) (key :: head :: tail)
  | afterLt {head tail inserted}
      (compared : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        key head = .lt)
      (tailDerived : DeclarativeInsertAromaticCanonicalRule3SpatialKey
        source key tail inserted) :
      DeclarativeInsertAromaticCanonicalRule3SpatialKey source key
        (head :: tail) (head :: inserted)

/-- Executable Rule-3 insertion is exactly its structural derivation. -/
theorem insertAromaticCanonicalUncancelledRule3SpatialKey_eq_iff_canonical
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    ∀ keys result,
      insertAromaticCanonicalUncancelledRule3SpatialKey
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys key keys = result ↔
        source.DeclarativeInsertAromaticCanonicalRule3SpatialKey key keys result
  | [], result => by
      constructor
      · intro computed
        simp [insertAromaticCanonicalUncancelledRule3SpatialKey] at computed
        subst result
        exact .nil
      · intro derived
        cases derived
        rfl
  | head :: tail, result => by
      cases comparison : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          key head with
      | eq =>
          constructor
          · intro computed
            simp [insertAromaticCanonicalUncancelledRule3SpatialKey, comparison] at computed
            subst result
            exact .beforeEq comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [insertAromaticCanonicalUncancelledRule3SpatialKey, compared]
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared _ => simp [comparison] at compared
      | gt =>
          constructor
          · intro computed
            simp [insertAromaticCanonicalUncancelledRule3SpatialKey, comparison] at computed
            subst result
            exact .beforeGt comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [insertAromaticCanonicalUncancelledRule3SpatialKey, compared]
            | afterLt compared _ => simp [comparison] at compared
      | lt =>
          constructor
          · intro computed
            simp only [insertAromaticCanonicalUncancelledRule3SpatialKey,
              comparison] at computed
            cases result with
            | nil => simp at computed
            | cons resultHead resultTail =>
                simp at computed
                rcases computed with ⟨rfl, computed⟩
                exact .afterLt comparison
                  ((source.insertAromaticCanonicalUncancelledRule3SpatialKey_eq_iff_canonical
                    key tail resultTail).mp computed)
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared tailDerived =>
                simp only [insertAromaticCanonicalUncancelledRule3SpatialKey,
                  compared, List.cons.injEq, true_and]
                exact
                  (source.insertAromaticCanonicalUncancelledRule3SpatialKey_eq_iff_canonical
                    key tail _).mpr tailDerived

/-- Canonical stable sort for Rules-1a--3 sibling keys. -/
inductive DeclarativeSortAromaticCanonicalRule3SpatialKeys
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalUncancelledRule3SpatialKey →
      List source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
  | nil : DeclarativeSortAromaticCanonicalRule3SpatialKeys source [] []
  | cons {key keys sortedTail result}
      (tail : DeclarativeSortAromaticCanonicalRule3SpatialKeys source keys sortedTail)
      (inserted : source.DeclarativeInsertAromaticCanonicalRule3SpatialKey
        key sortedTail result) :
      DeclarativeSortAromaticCanonicalRule3SpatialKeys source (key :: keys) result

/-- Executable Rule-3 sorting is exactly its structural derivation. -/
theorem sortAromaticCanonicalUncancelledRule3SpatialKeys_eq_iff_canonical
    (source : AuthoritativeChemicalInput) :
    ∀ keys result,
      sortAromaticCanonicalUncancelledRule3SpatialKeys
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys keys = result ↔
        source.DeclarativeSortAromaticCanonicalRule3SpatialKeys keys result
  | [], result => by
      constructor
      · intro computed
        simp [sortAromaticCanonicalUncancelledRule3SpatialKeys] at computed
        subst result
        exact .nil
      · intro derived
        cases derived
        rfl
  | key :: keys, result => by
      constructor
      · intro computed
        unfold sortAromaticCanonicalUncancelledRule3SpatialKeys at computed
        let sortedTail := sortAromaticCanonicalUncancelledRule3SpatialKeys
          source.compareAromaticCanonicalUncancelledRule3SpatialKeys keys
        exact .cons
          ((source.sortAromaticCanonicalUncancelledRule3SpatialKeys_eq_iff_canonical
            keys sortedTail).mp rfl)
          ((source.insertAromaticCanonicalUncancelledRule3SpatialKey_eq_iff_canonical
            key sortedTail result).mp computed)
      · intro derived
        cases derived with
        | cons tail inserted =>
            unfold sortAromaticCanonicalUncancelledRule3SpatialKeys
            rw [(source.sortAromaticCanonicalUncancelledRule3SpatialKeys_eq_iff_canonical
              _ _).mpr tail]
            exact
              (source.insertAromaticCanonicalUncancelledRule3SpatialKey_eq_iff_canonical
                key _ result).mpr inserted

mutual
  /-- Generic canonical recursive Rule-3 key derivation. -/
  inductive CanonicalAromaticCanonicalRule3SpatialKeyWith
      (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
      (NodeOutcome : OfficialCIPNode source.AromaticCanonicalAtom →
        Option source.AromaticCanonicalRule3SpatialNodeResult → Prop) :
      Nat → source.AromaticCanonicalRerootCursor carrierFuel →
        source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
    | terminal {fuel cursor children observation}
        (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
        (empty : children = [])
        (observed : NodeOutcome cursor.occurrence.1.node observation) :
        CanonicalAromaticCanonicalRule3SpatialKeyWith source NodeOutcome fuel cursor
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            observations := source.aromaticCanonicalRule3RootObservations observation
            rule3 := source.aromaticCanonicalRule3RootPriorities observation }
    | branch {fuel cursor children observation childKeys sorted}
        (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
        (nonempty : children ≠ [])
        (observed : NodeOutcome cursor.occurrence.1.node observation)
        (childDerivations : CanonicalAromaticCanonicalRule3SpatialKeyWithList
          source NodeOutcome fuel children childKeys)
        (ranking : source.DeclarativeSortAromaticCanonicalRule3SpatialKeys
          childKeys sorted) :
        CanonicalAromaticCanonicalRule3SpatialKeyWith source NodeOutcome
          (fuel + 1) cursor
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            observations := source.aromaticCanonicalRule3RootObservations observation ++
              mergeAromaticCanonicalRule3ObservationChildren sorted
            rule3 := source.aromaticCanonicalRule3RootPriorities observation ++
              mergeAromaticCanonicalRule3PriorityChildren sorted }

  /-- Pointwise generic canonical Rule-3 child derivations. -/
  inductive CanonicalAromaticCanonicalRule3SpatialKeyWithList
      (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
      (NodeOutcome : OfficialCIPNode source.AromaticCanonicalAtom →
        Option source.AromaticCanonicalRule3SpatialNodeResult → Prop) :
      Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
        List source.AromaticCanonicalUncancelledRule3SpatialKey → Prop
    | nil (fuel : Nat) :
        CanonicalAromaticCanonicalRule3SpatialKeyWithList
          source NodeOutcome fuel [] []
    | cons {fuel cursor cursors key keys}
        (head : CanonicalAromaticCanonicalRule3SpatialKeyWith
          source NodeOutcome fuel cursor key)
        (tail : CanonicalAromaticCanonicalRule3SpatialKeyWithList
          source NodeOutcome fuel cursors keys) :
        CanonicalAromaticCanonicalRule3SpatialKeyWithList
          source NodeOutcome fuel (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (observe : OfficialCIPNode source.AromaticCanonicalAtom →
      Option (Option source.AromaticCanonicalRule3SpatialNodeResult))
    (NodeOutcome : OfficialCIPNode source.AromaticCanonicalAtom →
      Option source.AromaticCanonicalRule3SpatialNodeResult → Prop)
    (nodeExact : ∀ (node : OfficialCIPNode source.AromaticCanonicalAtom)
      (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult),
        observe node = some outcome ↔ NodeOutcome node outcome)
    (exact : ∀ (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalUncancelledRule3SpatialKey),
      source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel cursor = some key ↔
        source.CanonicalAromaticCanonicalRule3SpatialKeyWith
          NodeOutcome fuel cursor key) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey),
      cursors.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel) =
          some keys ↔
        source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
          NodeOutcome fuel cursors keys
  | [], keys => by
      constructor
      · intro computed
        simp at computed
        subst keys
        exact .nil fuel
      · intro derived
        cases derived
        rfl
  | cursor :: cursors, keys => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : source.buildAromaticCanonicalRule3SpatialKeyWith?
            observe fuel cursor with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : cursors.mapM
                (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel) with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst keys
                exact .cons ((exact cursor head).mp headComputed)
                  ((source.mapM_buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                    observe NodeOutcome nodeExact exact cursors tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            rw [List.mapM_cons, (exact _ _).mpr head]
            rw [(source.mapM_buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
              observe NodeOutcome nodeExact exact _ _).mpr tail]
            rfl

/-- Generic recursive Rule-3 compilation is exactly the canonical derivation. -/
theorem buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (observe : OfficialCIPNode source.AromaticCanonicalAtom →
      Option (Option source.AromaticCanonicalRule3SpatialNodeResult))
    (NodeOutcome : OfficialCIPNode source.AromaticCanonicalAtom →
      Option source.AromaticCanonicalRule3SpatialNodeResult → Prop)
    (nodeExact : ∀ (node : OfficialCIPNode source.AromaticCanonicalAtom)
      (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult),
        observe node = some outcome ↔ NodeOutcome node outcome) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalUncancelledRule3SpatialKey),
      source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel cursor = some key ↔
        source.CanonicalAromaticCanonicalRule3SpatialKeyWith
          NodeOutcome fuel cursor key
  | 0, cursor, key => by
      constructor
      · intro computed
        unfold buildAromaticCanonicalRule3SpatialKeyWith? at computed
        let children := source.aromaticCanonicalRerootChildren cursor
        cases observationComputed : observe cursor.occurrence.1.node with
        | none => simp [observationComputed] at computed
        | some observation =>
            by_cases terminal : children = []
            · simp [children, observationComputed, terminal] at computed
              subst key
              exact .terminal (source.aromaticCanonicalRerootChildren_sound cursor)
                terminal ((nodeExact _ _).mp observationComputed)
            · simp [children, observationComputed, terminal] at computed
      · intro derived
        cases derived with
        | @terminal _ _ children observation frame empty observed =>
            have childrenEq :
                source.aromaticCanonicalRerootChildren cursor = children := by
              simpa [aromaticCanonicalRerootChildren?] using
                (source.aromaticCanonicalRerootChildren?_eq_some_iff
                  cursor children).mpr frame
            have observationComputed := (nodeExact _ _).mpr observed
            unfold buildAromaticCanonicalRule3SpatialKeyWith?
            simp [childrenEq, empty, observationComputed]
  | fuel + 1, cursor, key => by
      constructor
      · intro computed
        unfold buildAromaticCanonicalRule3SpatialKeyWith? at computed
        let children := source.aromaticCanonicalRerootChildren cursor
        cases observationComputed : observe cursor.occurrence.1.node with
        | none => simp [observationComputed] at computed
        | some observation =>
            by_cases terminal : children = []
            · simp [children, observationComputed, terminal] at computed
              subst key
              exact .terminal (source.aromaticCanonicalRerootChildren_sound cursor)
                terminal ((nodeExact _ _).mp observationComputed)
            · cases childKeysComputed : children.mapM
                  (source.buildAromaticCanonicalRule3SpatialKeyWith? observe fuel) with
              | none =>
                  simp [children, observationComputed, terminal,
                    childKeysComputed] at computed
              | some childKeys =>
                  simp [children, observationComputed, terminal,
                    childKeysComputed] at computed
                  subst key
                  exact .branch
                    (source.aromaticCanonicalRerootChildren_sound cursor)
                    terminal ((nodeExact _ _).mp observationComputed)
                    ((source.mapM_buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                      observe NodeOutcome nodeExact
                      (fun child childKey =>
                        source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                          observe NodeOutcome nodeExact fuel child childKey)
                      children childKeys).mp childKeysComputed)
                    ((source.sortAromaticCanonicalUncancelledRule3SpatialKeys_eq_iff_canonical
                      childKeys _).mp rfl)
      · intro derived
        cases derived with
        | @terminal _ _ children observation frame empty observed =>
            have childrenEq :
                source.aromaticCanonicalRerootChildren cursor = children := by
              simpa [aromaticCanonicalRerootChildren?] using
                (source.aromaticCanonicalRerootChildren?_eq_some_iff
                  cursor children).mpr frame
            have observationComputed := (nodeExact _ _).mpr observed
            unfold buildAromaticCanonicalRule3SpatialKeyWith?
            simp [childrenEq, empty, observationComputed]
        | @branch _ _ children observation childKeys sorted frame nonempty observed
            childDerivations ranking =>
            have childrenEq :
                source.aromaticCanonicalRerootChildren cursor = children := by
              simpa [aromaticCanonicalRerootChildren?] using
                (source.aromaticCanonicalRerootChildren?_eq_some_iff
                  cursor children).mpr frame
            have observationComputed := (nodeExact _ _).mpr observed
            have childKeysComputed :=
              (source.mapM_buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                observe NodeOutcome nodeExact
                (fun child childKey =>
                  source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                    observe NodeOutcome nodeExact fuel child childKey)
                children childKeys).mpr childDerivations
            have sortedComputed :=
              (source.sortAromaticCanonicalUncancelledRule3SpatialKeys_eq_iff_canonical
                childKeys sorted).mpr ranking
            unfold buildAromaticCanonicalRule3SpatialKeyWith?
            simp [childrenEq, nonempty, observationComputed,
              childKeysComputed, sortedComputed]

/-- Canonical recursive relation for the uncancelled Rule-3 pass. -/
abbrev CanonicalAromaticCanonicalUncancelledRule3SpatialKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyWith
    (carrierFuel := carrierFuel) source.CanonicalAromaticCanonicalRule3SpatialNodeOutcome

abbrev CanonicalAromaticCanonicalUncancelledRule3SpatialKeyList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat} :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
    (carrierFuel := carrierFuel) source.CanonicalAromaticCanonicalRule3SpatialNodeOutcome

/-- The uncancelled production pass is exactly its canonical recursive relation. -/
theorem buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel cursor = some key ↔
      source.CanonicalAromaticCanonicalUncancelledRule3SpatialKey fuel cursor key := by
  rw [source.buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_with]
  exact source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    source.aromaticCanonicalRule3SpatialNode?
    source.CanonicalAromaticCanonicalRule3SpatialNodeOutcome
    source.aromaticCanonicalRule3SpatialNode?_eq_some_iff_canonical fuel cursor key

/-- Pointwise uncancelled compilation is exactly pointwise canonical derivation. -/
theorem mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    cursors.mapM (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) =
        some keys ↔
      source.CanonicalAromaticCanonicalUncancelledRule3SpatialKeyList
        fuel cursors keys := by
  rw [source.buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_with]
  exact source.mapM_buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    source.aromaticCanonicalRule3SpatialNode?
    source.CanonicalAromaticCanonicalRule3SpatialNodeOutcome
    source.aromaticCanonicalRule3SpatialNode?_eq_some_iff_canonical
    (fun cursor key =>
      source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
        source.aromaticCanonicalRule3SpatialNode?
        source.CanonicalAromaticCanonicalRule3SpatialNodeOutcome
        source.aromaticCanonicalRule3SpatialNode?_eq_some_iff_canonical
        fuel cursor key) cursors keys

/-- Canonical recursive relation for the common-exclusion Rule-3 pass. -/
abbrev CanonicalAromaticCanonicalRule3SpatialKeyExcept
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyWith
    (carrierFuel := carrierFuel)
    (source.CanonicalAromaticCanonicalRule3SpatialNodeExceptOutcome excluded)

abbrev CanonicalAromaticCanonicalRule3SpatialKeyExceptList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
    (carrierFuel := carrierFuel)
    (source.CanonicalAromaticCanonicalRule3SpatialNodeExceptOutcome excluded)

/-- The common-exclusion production pass is exactly its canonical recursive relation. -/
theorem buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel cursor = some key ↔
      source.CanonicalAromaticCanonicalRule3SpatialKeyExcept
        excluded fuel cursor key := by
  rw [source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_with]
  exact source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    (source.aromaticCanonicalRule3SpatialNodeExcept? excluded)
    (source.CanonicalAromaticCanonicalRule3SpatialNodeExceptOutcome excluded)
    (source.aromaticCanonicalRule3SpatialNodeExcept?_eq_some_iff_canonical excluded)
    fuel cursor key

/-- Pointwise common-exclusion compilation is exactly pointwise canonical derivation. -/
theorem mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    cursors.mapM (source.buildAromaticCanonicalRule3SpatialKeyExcept?
        excluded fuel) = some keys ↔
      source.CanonicalAromaticCanonicalRule3SpatialKeyExceptList
        excluded fuel cursors keys := by
  rw [source.buildAromaticCanonicalRule3SpatialKeyExcept?_eq_with]
  exact source.mapM_buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
    (source.aromaticCanonicalRule3SpatialNodeExcept? excluded)
    (source.CanonicalAromaticCanonicalRule3SpatialNodeExceptOutcome excluded)
    (source.aromaticCanonicalRule3SpatialNodeExcept?_eq_some_iff_canonical excluded)
    (fun cursor key =>
      source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
        (source.aromaticCanonicalRule3SpatialNodeExcept? excluded)
        (source.CanonicalAromaticCanonicalRule3SpatialNodeExceptOutcome excluded)
        (source.aromaticCanonicalRule3SpatialNodeExcept?_eq_some_iff_canonical excluded)
        fuel cursor key) cursors keys

/-- The exhaustive physical-topology resolver is exactly its independent uniqueness relation. -/
theorem aromaticCanonicalRule3PhysicalTopologyResolution?_eq_some_iff_declarative
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (resolution : source.AromaticCanonicalRule3PhysicalTopologyResolution) :
    source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some resolution ↔
      source.DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution
        keys resolution := by
  constructor
  · exact source.aromaticCanonicalRule3PhysicalTopologyResolution?_sound
      keys resolution
  · intro derived
    unfold aromaticCanonicalRule3PhysicalTopologyResolution?
    generalize foundIdentity :
      source.aromaticCanonicalRule3CoupledUnitPairs keys = found
    cases derived with
    | ordinary absent =>
        cases found with
        | nil => rfl
        | cons pair tail =>
            have pairDerived :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys pair).mp (by
                rw [foundIdentity]
                simp)
            exact (absent pair pairDerived).elim
    | @coupled pair pairDerived unique =>
        cases found with
        | nil =>
            have present :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys pair).mpr
                pairDerived
            rw [foundIdentity] at present
            simp at present
        | cons first tail =>
            have firstDerived :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys first).mp (by
                rw [foundIdentity]
                simp)
            have firstEq := unique first firstDerived
            subst first
            cases tail with
            | nil => rfl
            | cons second rest =>
                have secondDerived :=
                  (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys second).mp (by
                    rw [foundIdentity]
                    simp)
                have secondEq := unique second secondDerived
                subst second
                have nodup := source.aromaticCanonicalRule3CoupledUnitPairs_nodup keys
                rw [foundIdentity] at nodup
                simp at nodup

/-- Exact canonical relation for the complete two-pass Rule-3 frame. -/
def CanonicalAromaticCanonicalRule3CanonicalKeyFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) : Prop :=
  source.CanonicalAromaticCanonicalUncancelledRule3SpatialKeyList
      fuel cursors frame.rawKeys ∧
    source.DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution
      frame.rawKeys frame.resolution ∧
    frame.excluded = source.aromaticCanonicalRule3ExcludedPhysicalUnits
      frame.rawKeys frame.resolution ∧
    source.CanonicalAromaticCanonicalRule3SpatialKeyExceptList
      frame.excluded fuel cursors frame.keys

/-- The complete two-pass Rule-3 frame succeeds exactly on the canonical independent relation. -/
theorem buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) :
    source.buildAromaticCanonicalRule3CanonicalKeyFrame? fuel cursors = some frame ↔
      source.CanonicalAromaticCanonicalRule3CanonicalKeyFrame fuel cursors frame := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalRule3CanonicalKeyFrame? at computed
    cases rawComputed : cursors.mapM
        (source.buildAromaticCanonicalUncancelledRule3SpatialKey? fuel) with
    | none => simp [rawComputed] at computed
    | some rawKeys =>
        cases resolutionComputed :
            source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys with
        | none => simp [rawComputed, resolutionComputed] at computed
        | some resolution =>
            let excluded :=
              source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
            cases keysComputed : cursors.mapM
                (source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel) with
            | none =>
                simp [rawComputed, resolutionComputed, excluded, keysComputed] at computed
            | some keys =>
                simp [rawComputed, resolutionComputed, excluded, keysComputed] at computed
                subst frame
                exact ⟨
                  (source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_some_iff_canonical
                    fuel cursors rawKeys).mp rawComputed,
                  (source.aromaticCanonicalRule3PhysicalTopologyResolution?_eq_some_iff_declarative
                    rawKeys resolution).mp resolutionComputed,
                  rfl,
                  (source.mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
                    excluded fuel cursors keys).mp keysComputed⟩
  · rintro ⟨rawDerived, resolutionDerived, excludedEq, keysDerived⟩
    have rawComputed :=
      (source.mapM_buildAromaticCanonicalUncancelledRule3SpatialKey?_eq_some_iff_canonical
        fuel cursors frame.rawKeys).mpr rawDerived
    have resolutionComputed :=
      (source.aromaticCanonicalRule3PhysicalTopologyResolution?_eq_some_iff_declarative
        frame.rawKeys frame.resolution).mpr resolutionDerived
    have keysComputed :=
      (source.mapM_buildAromaticCanonicalRule3SpatialKeyExcept?_eq_some_iff_canonical
        frame.excluded fuel cursors frame.keys).mpr keysDerived
    have canonicalKeysComputed :
        cursors.mapM
            (source.buildAromaticCanonicalRule3SpatialKeyExcept?
              (source.aromaticCanonicalRule3ExcludedPhysicalUnits
                frame.rawKeys frame.resolution) fuel) = some frame.keys := by
      rw [← excludedEq]
      exact keysComputed
    have frameEq :
        ({ rawKeys := frame.rawKeys
           resolution := frame.resolution
           excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits
             frame.rawKeys frame.resolution
           keys := frame.keys } : source.AromaticCanonicalRule3CanonicalKeyFrame) = frame := by
      cases frame
      simp_all
    simpa [buildAromaticCanonicalRule3CanonicalKeyFrame?, rawComputed,
      resolutionComputed, canonicalKeysComputed] using
      congrArg (fun value =>
        (some value : Option source.AromaticCanonicalRule3CanonicalKeyFrame)) frameEq

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
