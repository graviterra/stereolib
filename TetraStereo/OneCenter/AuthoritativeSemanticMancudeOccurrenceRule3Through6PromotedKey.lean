import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule6PromotedKey

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical recursive Rules 3--6 integration

The physical Rule-3 topology is resolved once for the complete ligand frame.  This module then
threads that one exclusion set through every recursive branch used by Rule 6.  Consequently a
child is reranked by Rules 1a--5, including Rule 3, before reference promotion is consulted.

The older `AromaticCanonicalRule6PromotedKey` remains useful as the independently certified
Rules-1a--2,4--6 construction.  The key below is the strengthened construction that closes the
Rule-3 hierarchy gap.
-/

/-- One recursively promoted key with the complete certified pre-Rule-6 key. -/
structure AromaticCanonicalRule3Through6PromotedKey
    (source : AuthoritativeChemicalInput) where
  prior : source.AromaticCanonicalOccurrenceRule3Through5Key
  promotion : List (List (OfficialSparseEntry Nat))

/-- Promotion layers are compared only after a complete Rules-1a--5 tie. -/
noncomputable def compareAromaticCanonicalRule3Through6PromotedKeys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.prior)
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys)
    (Ordering.byKey (fun key => key.promotion)
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))

theorem compareAromaticCanonicalRule3Through6PromotedKeys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalRule3Through6PromotedKeys := by
  letI : Std.TransCmp source.compareAromaticCanonicalOccurrenceRule3Through5Keys :=
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareAromaticCanonicalRule3Through6PromotedKeys
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

def insertAromaticCanonicalRule3Through6PromotedKey
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering)
    (key : source.AromaticCanonicalRule3Through6PromotedKey) :
    List source.AromaticCanonicalRule3Through6PromotedKey →
      List source.AromaticCanonicalRule3Through6PromotedKey
  | [] => [key]
  | head :: tail =>
      match compare key head with
      | .lt => head :: insertAromaticCanonicalRule3Through6PromotedKey compare key tail
      | .eq | .gt => key :: head :: tail

def sortAromaticCanonicalRule3Through6PromotedKeys
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering) :
    List source.AromaticCanonicalRule3Through6PromotedKey →
      List source.AromaticCanonicalRule3Through6PromotedKey
  | [] => []
  | key :: keys =>
      insertAromaticCanonicalRule3Through6PromotedKey compare key
        (sortAromaticCanonicalRule3Through6PromotedKeys compare keys)

theorem insertAromaticCanonicalRule3Through6PromotedKey_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering)
    (key : source.AromaticCanonicalRule3Through6PromotedKey) :
    ∀ keys,
      (insertAromaticCanonicalRule3Through6PromotedKey compare key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertAromaticCanonicalRule3Through6PromotedKey
      cases comparison : compare key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (insertAromaticCanonicalRule3Through6PromotedKey_perm compare key tail)).trans
              (List.Perm.swap key head tail)

theorem sortAromaticCanonicalRule3Through6PromotedKeys_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering) :
    ∀ keys, (sortAromaticCanonicalRule3Through6PromotedKeys compare keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (insertAromaticCanonicalRule3Through6PromotedKey_perm compare key
        (sortAromaticCanonicalRule3Through6PromotedKeys compare keys)).trans
          (List.Perm.cons key
            (sortAromaticCanonicalRule3Through6PromotedKeys_perm compare keys))

def AromaticCanonicalRule3Through6PromotedKeysDescending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering)
    (keys : List source.AromaticCanonicalRule3Through6PromotedKey) : Prop :=
  keys.Pairwise fun left right => compare left right ≠ Ordering.lt

theorem insertAromaticCanonicalRule3Through6PromotedKey_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering)
    [Std.TransCmp compare]
    (key : source.AromaticCanonicalRule3Through6PromotedKey) :
    ∀ keys,
      AromaticCanonicalRule3Through6PromotedKeysDescending compare keys →
      AromaticCanonicalRule3Through6PromotedKeysDescending compare
        (insertAromaticCanonicalRule3Through6PromotedKey compare key keys)
  | [], _ => by
      simp [insertAromaticCanonicalRule3Through6PromotedKey,
        AromaticCanonicalRule3Through6PromotedKeysDescending]
  | head :: tail, sorted => by
      have headOverTail : ∀ observed ∈ tail,
          compare head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : AromaticCanonicalRule3Through6PromotedKeysDescending compare tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertAromaticCanonicalRule3Through6PromotedKey
      cases comparison : compare key head with
      | gt =>
          rw [AromaticCanonicalRule3Through6PromotedKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [AromaticCanonicalRule3Through6PromotedKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted := insertAromaticCanonicalRule3Through6PromotedKey_descending
            compare key tail tailSorted
          rw [AromaticCanonicalRule3Through6PromotedKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation :=
              insertAromaticCanonicalRule3Through6PromotedKey_perm compare key tail
            have sourcePresent : observed ∈ key :: tail := (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse : compare head key = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortAromaticCanonicalRule3Through6PromotedKeys_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering)
    [Std.TransCmp compare] :
    ∀ keys,
      AromaticCanonicalRule3Through6PromotedKeysDescending compare
        (sortAromaticCanonicalRule3Through6PromotedKeys compare keys)
  | [] => by
      simp [sortAromaticCanonicalRule3Through6PromotedKeys,
        AromaticCanonicalRule3Through6PromotedKeysDescending]
  | key :: keys =>
      insertAromaticCanonicalRule3Through6PromotedKey_descending compare key
        (sortAromaticCanonicalRule3Through6PromotedKeys compare keys)
        (sortAromaticCanonicalRule3Through6PromotedKeys_descending compare keys)

/-- Maximum number of promotion layers among a child list. -/
def aromaticCanonicalRule3Through6PromotionChildLayerCount
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalRule3Through6PromotedKey) : Nat :=
  children.foldl (fun longest child => max longest child.promotion.length) 0

def aromaticCanonicalRule3Through6RankedChildTail
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering)
    (previous : source.AromaticCanonicalRule3Through6PromotedKey) (rank : Nat) :
    List source.AromaticCanonicalRule3Through6PromotedKey →
      List (source.AromaticCanonicalRule3Through6PromotedKey × Nat)
  | [] => []
  | child :: children =>
      let childRank := if compare child previous = Ordering.eq then rank else rank + 1
      (child, childRank) ::
        aromaticCanonicalRule3Through6RankedChildTail compare child childRank children

def aromaticCanonicalRule3Through6RankedChildren
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering) :
    List source.AromaticCanonicalRule3Through6PromotedKey →
      List (source.AromaticCanonicalRule3Through6PromotedKey × Nat)
  | [] => []
  | child :: children =>
      (child, 0) :: aromaticCanonicalRule3Through6RankedChildTail compare child 0 children

def mergeAromaticCanonicalRule3Through6PromotionChildren
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule3Through6PromotedKey →
      source.AromaticCanonicalRule3Through6PromotedKey → Ordering)
    (children : List source.AromaticCanonicalRule3Through6PromotedKey) :
    List (List (OfficialSparseEntry Nat)) :=
  let count := aromaticCanonicalRule3Through6PromotionChildLayerCount children
  let ranked := aromaticCanonicalRule3Through6RankedChildren compare children
  (List.range count).map fun depth =>
    ranked.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.promotion.getD depth [])

/-- Assemble the complete pre-Rule-6 key for one branch under a fixed Rule-3 policy. -/
noncomputable def buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    Option source.AromaticCanonicalOccurrenceRule3Through5Key := do
  let rule3 ← source.buildAromaticCanonicalRule3SpatialKeyExcept? excluded fuel cursor
  let rule45 ← source.buildAromaticCanonicalRerootCompoundRule45Key?
    target view fuel cursor
  some { rule3, rule45 }

def DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalOccurrenceRule3Through5Key) : Prop :=
  source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept
      excluded fuel cursor key.rule3 ∧
    source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
      target view fuel cursor key.rule45

theorem buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalOccurrenceRule3Through5Key)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
      excluded target view fuel cursor = some key) :
    source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
      excluded target view fuel cursor key := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyExcept? at computed
  cases rule3Computed : source.buildAromaticCanonicalRule3SpatialKeyExcept?
      excluded fuel cursor with
  | none => simp [rule3Computed] at computed
  | some rule3 =>
      cases rule45Computed : source.buildAromaticCanonicalRerootCompoundRule45Key?
          target view fuel cursor with
      | none => simp [rule3Computed, rule45Computed] at computed
      | some rule45 =>
          simp [rule3Computed, rule45Computed] at computed
          subst key
          exact ⟨
            source.buildAromaticCanonicalRule3SpatialKeyExcept?_sound
              excluded fuel cursor rule3 rule3Computed,
            source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
              target view fuel cursor rule45 rule45Computed⟩

/-- Recursively build Rules 1a--6 while retaining the frame-wide Rule-3 cancellation policy.
At every nonterminal node the children are sorted by the complete strengthened key before their
promotion layers are merged. -/
noncomputable def buildAromaticCanonicalRule3Through6PromotedKey?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalRule3Through6PromotedKey
  | 0, cursor => do
      let prior ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
        excluded target view 0 cursor
      let children ← source.aromaticCanonicalRerootChildren? cursor
      if children = [] then
        some
          { prior := prior
            promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
      else none
  | fuel + 1, cursor => do
      let prior ← source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
        excluded target view (fuel + 1) cursor
      let children ← source.aromaticCanonicalRerootChildren? cursor
      let marker := aromaticCanonicalRule6PromotionMarker reference cursor
      if children = [] then
        some { prior := prior, promotion := [[([], marker)]] }
      else
        let childKeys ← children.mapM
          (source.buildAromaticCanonicalRule3Through6PromotedKey?
            excluded target view reference fuel)
        let compare := source.compareAromaticCanonicalRule3Through6PromotedKeys
        let sorted := sortAromaticCanonicalRule3Through6PromotedKeys compare childKeys
        some
          { prior := prior
            promotion := [[([], marker)]] ++
              mergeAromaticCanonicalRule3Through6PromotionChildren compare sorted }

mutual

inductive DeclarativeAromaticCanonicalRule3Through6PromotedKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalRule3Through6PromotedKey → Prop
  | zeroLeaf {cursor prior children}
      (priorDerivation :
        source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view 0 cursor prior)
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = []) :
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference 0 cursor
          { prior := prior
            promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
  | successorLeaf {fuel cursor prior children}
      (priorDerivation :
        source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view (fuel + 1) cursor prior)
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = []) :
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference (fuel + 1) cursor
          { prior := prior
            promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
  | successorBranch {fuel cursor prior children childKeys sorted}
      (priorDerivation :
        source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view (fuel + 1) cursor prior)
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (nonterminal : children ≠ [])
      (childDerivations :
        source.DeclarativeAromaticCanonicalRule3Through6PromotedKeyList
          excluded target view reference fuel children childKeys)
      (permutation : sorted.Perm childKeys)
      (descending : AromaticCanonicalRule3Through6PromotedKeysDescending
        source.compareAromaticCanonicalRule3Through6PromotedKeys sorted) :
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference (fuel + 1) cursor
          { prior := prior
            promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] ++
              mergeAromaticCanonicalRule3Through6PromotionChildren
                source.compareAromaticCanonicalRule3Through6PromotedKeys sorted }

inductive DeclarativeAromaticCanonicalRule3Through6PromotedKeyList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
      List source.AromaticCanonicalRule3Through6PromotedKey → Prop
  | nil (fuel : Nat) :
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKeyList
        excluded target view reference fuel [] []
  | cons {fuel cursor cursors key keys}
      (head : source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference fuel cursor key)
      (tail : source.DeclarativeAromaticCanonicalRule3Through6PromotedKeyList
        excluded target view reference fuel cursors keys) :
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKeyList
        excluded target view reference fuel (cursor :: cursors) (key :: keys)

end

private theorem mapM_buildAromaticCanonicalRule3Through6PromotedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom)
    (sound : ∀ cursor key,
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel cursor = some key →
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference fuel cursor key) :
    ∀ cursors keys,
      cursors.mapM (source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel) = some keys →
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKeyList
        excluded target view reference fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact .nil fuel
  | cursor :: cursors, keys, computed => by
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
              exact .cons (sound cursor head headComputed)
                (mapM_buildAromaticCanonicalRule3Through6PromotedKey?_sound
                  source excluded target view reference sound cursors tail tailComputed)

theorem buildAromaticCanonicalRule3Through6PromotedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel cursor = some key →
      source.DeclarativeAromaticCanonicalRule3Through6PromotedKey
        excluded target view reference fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalRule3Through6PromotedKey? at computed
      cases priorComputed :
          source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view 0 cursor with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
          let children := source.aromaticCanonicalRerootChildren cursor
          by_cases terminal : children = []
          · simp [children, terminal] at computed
            subst key
            exact .zeroLeaf
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound
                excluded target view 0 cursor prior priorComputed)
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
          · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
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
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound
                excluded target view (fuel + 1) cursor prior priorComputed)
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
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
                letI : Std.TransCmp compare :=
                  source.compareAromaticCanonicalRule3Through6PromotedKeys_transCmp
                exact .successorBranch
                  (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound
                    excluded target view (fuel + 1) cursor prior priorComputed)
                  (source.aromaticCanonicalRerootChildren_sound cursor) terminal
                  (mapM_buildAromaticCanonicalRule3Through6PromotedKey?_sound
                    source excluded target view reference
                    (source.buildAromaticCanonicalRule3Through6PromotedKey?_sound
                      excluded target view reference fuel)
                    children childKeys childKeysComputed)
                  (sortAromaticCanonicalRule3Through6PromotedKeys_perm compare childKeys)
                  (sortAromaticCanonicalRule3Through6PromotedKeys_descending
                    compare childKeys)

/-- The prior stored by a successful promoted build is exactly the independently built
fixed-policy Rules-1a--5 key at that cursor.  Recursive reference promotion cannot rewrite it. -/
theorem buildAromaticCanonicalRule3Through6PromotedKey?_prior
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalRule3Through6PromotedKey?
        excluded target view reference fuel cursor = some key →
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
        excluded target view fuel cursor = some key.prior
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalRule3Through6PromotedKey? at computed
      cases priorComputed :
          source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view 0 cursor with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
          let children := source.aromaticCanonicalRerootChildren cursor
          by_cases terminal : children = []
          · simp [children, terminal] at computed
            subst key
            rfl
          · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
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
            rfl
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
                rfl

/-- All successful reference-specific builds share the identical Rules-1a--5 prior. -/
theorem buildAromaticCanonicalRule3Through6PromotedKey?_prior_reference_invariant
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (leftReference rightReference : source.AromaticCanonicalAtom)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (left right : source.AromaticCanonicalRule3Through6PromotedKey)
    (leftComputed : source.buildAromaticCanonicalRule3Through6PromotedKey?
      excluded target view leftReference fuel cursor = some left)
    (rightComputed : source.buildAromaticCanonicalRule3Through6PromotedKey?
      excluded target view rightReference fuel cursor = some right) :
    left.prior = right.prior := by
  have leftPrior := source.buildAromaticCanonicalRule3Through6PromotedKey?_prior
    excluded target view leftReference fuel cursor left leftComputed
  have rightPrior := source.buildAromaticCanonicalRule3Through6PromotedKey?_prior
    excluded target view rightReference fuel cursor right rightComputed
  exact Option.some.inj (leftPrior.symm.trans rightPrior)

/-- The strengthened comparison cannot consult Rule 6 when Rules 1a--5 are decisive. -/
theorem compareAromaticCanonicalRule3Through6PromotedKeys_of_prior_ne_eq
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRule3Through6PromotedKey)
    (decisive : source.compareAromaticCanonicalOccurrenceRule3Through5Keys
      left.prior right.prior ≠ Ordering.eq) :
    source.compareAromaticCanonicalRule3Through6PromotedKeys left right =
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys
        left.prior right.prior := by
  unfold compareAromaticCanonicalRule3Through6PromotedKeys
  generalize priorComputed :
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys
        left.prior right.prior = prior
  cases prior <;> simp_all [compareLex, Ordering.byKey]

/-- After a complete Rules-1a--5 tie, the result is exactly the Rule-6 promotion comparison. -/
theorem compareAromaticCanonicalRule3Through6PromotedKeys_of_prior_eq
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalRule3Through6PromotedKey)
    (tied : source.compareAromaticCanonicalOccurrenceRule3Through5Keys
      left.prior right.prior = Ordering.eq) :
    source.compareAromaticCanonicalRule3Through6PromotedKeys left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.promotion right.promotion := by
  simp [compareAromaticCanonicalRule3Through6PromotedKeys,
    compareLex, Ordering.byKey, tied]

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
