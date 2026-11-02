import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondExactReadinessCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact recursive meaning of the strengthened Rules 1a--6 promoted key

The production promoted-key builder previously had a kernel-checked soundness theorem, but no
converse.  The relations below expose its deterministic recursive normal form without mentioning
an `Option` result: the Rules-1a--5 prior is canonical, the zipper child frame is the production
source-canonical frame, every child is recursively canonical, and the child keys are sorted and
merged by the lawful strengthened comparator.
-/

/-- Canonical pointwise Rule-3 compilation preserves the source cursor count. -/
theorem CanonicalAromaticCanonicalRule3SpatialKeyExceptList.length_eq
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (canonical : source.CanonicalAromaticCanonicalRule3SpatialKeyExceptList
      excluded fuel cursors keys) :
    keys.length = cursors.length :=
  match canonical with
  | .nil _ => rfl
  | .cons _ tail => by
      simp [CanonicalAromaticCanonicalRule3SpatialKeyExceptList.length_eq tail]

/-- Hence the resolved common Rule-3 frame has exactly one key per input cursor. -/
theorem CanonicalAromaticCanonicalRule3CanonicalKeyFrame.keys_length_eq
    {source : AuthoritativeChemicalInput} {carrierFuel fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {frame : source.AromaticCanonicalRule3CanonicalKeyFrame}
    (canonical : source.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
      fuel cursors frame) :
    frame.keys.length = cursors.length :=
  canonical.2.2.2.length_eq

mutual

/-- Canonical recursive normal form of one strengthened promoted key. -/
inductive CanonicalAromaticCanonicalRule3Through6PromotedKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalRule3Through6PromotedKey → Prop
  | zeroLeaf {cursor prior}
      (priorCanonical :
        source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view 0 cursor prior)
      (terminal : source.aromaticCanonicalRerootChildren cursor = []) :
      source.CanonicalAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference 0 cursor
          { prior := prior
            promotion :=
              [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
  | successorLeaf {fuel cursor prior}
      (priorCanonical :
        source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view (fuel + 1) cursor prior)
      (terminal : source.aromaticCanonicalRerootChildren cursor = []) :
      source.CanonicalAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference (fuel + 1) cursor
          { prior := prior
            promotion :=
              [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
  | successorBranch {fuel cursor prior childKeys}
      (priorCanonical :
        source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view (fuel + 1) cursor prior)
      (nonterminal : source.aromaticCanonicalRerootChildren cursor ≠ [])
      (childrenCanonical :
        source.CanonicalAromaticCanonicalRule3Through6PromotedKeyList
          excluded target view reference fuel
          (source.aromaticCanonicalRerootChildren cursor) childKeys) :
      source.CanonicalAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference (fuel + 1) cursor
          { prior := prior
            promotion :=
              [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] ++
                mergeAromaticCanonicalRule3Through6PromotionChildren
                  source.compareAromaticCanonicalRule3Through6PromotedKeys
                  (sortAromaticCanonicalRule3Through6PromotedKeys
                    source.compareAromaticCanonicalRule3Through6PromotedKeys childKeys) }

/-- Pointwise canonical promoted-key relation for an ordered child frame. -/
inductive CanonicalAromaticCanonicalRule3Through6PromotedKeyList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
      List source.AromaticCanonicalRule3Through6PromotedKey → Prop
  | nil (fuel : Nat) :
      source.CanonicalAromaticCanonicalRule3Through6PromotedKeyList
        excluded target view reference fuel [] []
  | cons {fuel cursor cursors key keys}
      (head : source.CanonicalAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference fuel cursor key)
      (tail : source.CanonicalAromaticCanonicalRule3Through6PromotedKeyList
        excluded target view reference fuel cursors keys) :
      source.CanonicalAromaticCanonicalRule3Through6PromotedKeyList
        excluded target view reference fuel (cursor :: cursors) (key :: keys)

end

private theorem mapM_buildAromaticCanonicalRule3Through6PromotedKey?_eq_some_iff_canonical_of_pointwise
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom)
    (pointwise : ∀ cursor key,
      source.buildAromaticCanonicalRule3Through6PromotedKey?
          excluded target view reference fuel cursor = some key ↔
        source.CanonicalAromaticCanonicalRule3Through6PromotedKey
          excluded target view reference fuel cursor key) :
    ∀ cursors keys,
      cursors.mapM (source.buildAromaticCanonicalRule3Through6PromotedKey?
          excluded target view reference fuel) = some keys ↔
        source.CanonicalAromaticCanonicalRule3Through6PromotedKeyList
          excluded target view reference fuel cursors keys
  | [], keys => by
      constructor
      · intro computed
        simp at computed
        subst keys
        exact .nil fuel
      · intro canonical
        cases canonical
        rfl
  | cursor :: cursors, keys => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : source.buildAromaticCanonicalRule3Through6PromotedKey?
            excluded target view reference fuel cursor with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : cursors.mapM
                (source.buildAromaticCanonicalRule3Through6PromotedKey?
                  excluded target view reference fuel) with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst keys
                exact .cons ((pointwise cursor head).mp headComputed)
                  ((mapM_buildAromaticCanonicalRule3Through6PromotedKey?_eq_some_iff_canonical_of_pointwise
                    source excluded target view reference pointwise cursors tail).mp
                      tailComputed)
      · intro canonical
        cases canonical with
        | cons head tail =>
            rw [List.mapM_cons, (pointwise _ _).mpr head]
            rw [(mapM_buildAromaticCanonicalRule3Through6PromotedKey?_eq_some_iff_canonical_of_pointwise
              source excluded target view reference pointwise _ _).mpr tail]
            rfl

/-- The strengthened promoted-key builder is complete as well as sound: it succeeds with exactly
the recursively canonical normal form above. -/
theorem buildAromaticCanonicalRule3Through6PromotedKey?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalRule3Through6PromotedKey?
          excluded target view reference fuel cursor = some key ↔
        source.CanonicalAromaticCanonicalRule3Through6PromotedKey
          excluded target view reference fuel cursor key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key
      constructor
      · intro computed
        unfold buildAromaticCanonicalRule3Through6PromotedKey? at computed
        cases priorComputed :
            source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
              excluded target view 0 cursor with
        | none => simp [priorComputed] at computed
        | some prior =>
            simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
            by_cases terminal : source.aromaticCanonicalRerootChildren cursor = []
            · simp [terminal] at computed
              subst key
              exact .zeroLeaf
                ((source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                  excluded target view 0 cursor prior).mp priorComputed)
                terminal
            · simp [terminal] at computed
      · intro canonical
        cases canonical with
        | zeroLeaf priorCanonical terminal =>
            have priorComputed :=
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                excluded target view 0 cursor _).mpr priorCanonical
            simp [buildAromaticCanonicalRule3Through6PromotedKey?, priorComputed,
              aromaticCanonicalRerootChildren?, terminal]
  | succ fuel inductionHypothesis =>
      intro cursor key
      have listExact :=
        mapM_buildAromaticCanonicalRule3Through6PromotedKey?_eq_some_iff_canonical_of_pointwise
          source excluded target view reference inductionHypothesis
      constructor
      · intro computed
        unfold buildAromaticCanonicalRule3Through6PromotedKey? at computed
        cases priorComputed :
            source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
              excluded target view (fuel + 1) cursor with
        | none => simp [priorComputed] at computed
        | some prior =>
            simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
            let children := source.aromaticCanonicalRerootChildren cursor
            by_cases terminal : children = []
            · simp [children, terminal] at computed
              subst key
              exact .successorLeaf
                ((source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                  excluded target view (fuel + 1) cursor prior).mp priorComputed)
                terminal
            · cases childKeysComputed : children.mapM
                  (source.buildAromaticCanonicalRule3Through6PromotedKey?
                    excluded target view reference fuel) with
              | none => simp [children, terminal, childKeysComputed] at computed
              | some childKeys =>
                  let compare :=
                    source.compareAromaticCanonicalRule3Through6PromotedKeys
                  let sorted :=
                    sortAromaticCanonicalRule3Through6PromotedKeys compare childKeys
                  simp [children, terminal, childKeysComputed] at computed
                  subst key
                  simpa [children, compare, sorted] using
                    (CanonicalAromaticCanonicalRule3Through6PromotedKey.successorBranch
                      ((source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                        excluded target view (fuel + 1) cursor prior).mp priorComputed)
                      terminal
                      ((listExact children childKeys).mp childKeysComputed))
      · intro canonical
        cases canonical with
        | successorLeaf priorCanonical terminal =>
            have priorComputed :=
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                excluded target view (fuel + 1) cursor _).mpr priorCanonical
            simp [buildAromaticCanonicalRule3Through6PromotedKey?, priorComputed,
              aromaticCanonicalRerootChildren?, terminal]
        | successorBranch priorCanonical nonterminal childrenCanonical =>
            have priorComputed :=
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                excluded target view (fuel + 1) cursor _).mpr priorCanonical
            have childKeysComputed := (listExact _ _).mpr childrenCanonical
            simp [buildAromaticCanonicalRule3Through6PromotedKey?, priorComputed,
              aromaticCanonicalRerootChildren?, nonterminal, childKeysComputed]

/-- Canonical promoted keys retain the earlier independent declarative Rules-1a--6 meaning. -/
theorem CanonicalAromaticCanonicalRule3Through6PromotedKey.sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRule3Through6PromotedKey)
    (canonical : source.CanonicalAromaticCanonicalRule3Through6PromotedKey
      excluded target view reference fuel cursor key) :
    source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
      excluded target view reference fuel cursor key := by
  apply source.buildAromaticCanonicalRule3Through6PromotedKey?_sound
  exact (source.buildAromaticCanonicalRule3Through6PromotedKey?_eq_some_iff_canonical
    excluded target view reference fuel cursor key).mpr canonical

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
