import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Source-canonical promoted Rule-6 keys

This module places Rule 6 after the currently certified source-canonical Rules 1a--2 and 4--5 key.
A reference atom is promoted at every occurrence where it is duplicated, and child branches are
dynamically reranked by the resulting key.  The recursive construction below performs that
reranking directly on the source-canonical occurrence zipper.  Rule 3 is deliberately not claimed
here; the chemically complete pre-Rule-6 key additionally requires the Rule-3 layer proved in the
separate integration module.
-/

/-- Source-canonical Rules-1a--2, 4--6 key for one reference atom. -/
structure AromaticCanonicalRule6PromotedKey
    (source : AuthoritativeChemicalInput) where
  prior : source.AromaticCanonicalRerootCompoundRule45Key
  promotion : List (List (OfficialSparseEntry Nat))

/-- Rules 1a--2 and 4--5 decide first; reference promotion is consulted only after their tie. -/
def compareAromaticCanonicalRule6PromotedKeys
    (source : AuthoritativeChemicalInput) :
    source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering :=
  compareLex
    (Ordering.byKey (fun key => key.prior)
      source.compareAromaticCanonicalRerootCompoundRule45Keys)
    (Ordering.byKey (fun key => key.promotion)
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))

theorem compareAromaticCanonicalRule6PromotedKeys_transCmp
    (source : AuthoritativeChemicalInput) :
    Std.TransCmp source.compareAromaticCanonicalRule6PromotedKeys := by
  letI : Std.TransCmp source.compareAromaticCanonicalRerootCompoundRule45Keys :=
    source.compareAromaticCanonicalRerootCompoundRule45Keys_transCmp
  letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  unfold compareAromaticCanonicalRule6PromotedKeys
    OfficialRuleMajorKey.compareSparseLayers
    OfficialRuleMajorKey.compareSparseLayer
    OfficialRuleMajorKey.compareSparseEntry
  infer_instance

/-- Structural descending insertion for promoted keys. -/
def insertAromaticCanonicalRule6PromotedKey
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering)
    (key : source.AromaticCanonicalRule6PromotedKey) :
    List source.AromaticCanonicalRule6PromotedKey →
      List source.AromaticCanonicalRule6PromotedKey
  | [] => [key]
  | head :: tail =>
      match compare key head with
      | .lt => head :: insertAromaticCanonicalRule6PromotedKey compare key tail
      | .eq | .gt => key :: head :: tail

def sortAromaticCanonicalRule6PromotedKeys
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering) :
    List source.AromaticCanonicalRule6PromotedKey →
      List source.AromaticCanonicalRule6PromotedKey
  | [] => []
  | key :: keys =>
      insertAromaticCanonicalRule6PromotedKey compare key
        (sortAromaticCanonicalRule6PromotedKeys compare keys)

theorem insertAromaticCanonicalRule6PromotedKey_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering)
    (key : source.AromaticCanonicalRule6PromotedKey) :
    ∀ keys,
      (insertAromaticCanonicalRule6PromotedKey compare key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertAromaticCanonicalRule6PromotedKey
      cases comparison : compare key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head
            (insertAromaticCanonicalRule6PromotedKey_perm compare key tail)).trans
              (List.Perm.swap key head tail)

theorem sortAromaticCanonicalRule6PromotedKeys_perm
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering) :
    ∀ keys, (sortAromaticCanonicalRule6PromotedKeys compare keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (insertAromaticCanonicalRule6PromotedKey_perm compare key
        (sortAromaticCanonicalRule6PromotedKeys compare keys)).trans
          (List.Perm.cons key
            (sortAromaticCanonicalRule6PromotedKeys_perm compare keys))

def AromaticCanonicalRule6PromotedKeysDescending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering)
    (keys : List source.AromaticCanonicalRule6PromotedKey) : Prop :=
  keys.Pairwise fun left right => compare left right ≠ Ordering.lt

theorem insertAromaticCanonicalRule6PromotedKey_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering)
    [Std.TransCmp compare]
    (key : source.AromaticCanonicalRule6PromotedKey) :
    ∀ keys,
      AromaticCanonicalRule6PromotedKeysDescending compare keys →
      AromaticCanonicalRule6PromotedKeysDescending compare
        (insertAromaticCanonicalRule6PromotedKey compare key keys)
  | [], _ => by
      simp [insertAromaticCanonicalRule6PromotedKey,
        AromaticCanonicalRule6PromotedKeysDescending]
  | head :: tail, sorted => by
      have headOverTail : ∀ observed ∈ tail,
          compare head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : AromaticCanonicalRule6PromotedKeysDescending compare tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertAromaticCanonicalRule6PromotedKey
      cases comparison : compare key head with
      | gt =>
          rw [AromaticCanonicalRule6PromotedKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [AromaticCanonicalRule6PromotedKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with rfl | tailPresent
            · simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted := insertAromaticCanonicalRule6PromotedKey_descending
            compare key tail tailSorted
          rw [AromaticCanonicalRule6PromotedKeysDescending, List.pairwise_cons]
          constructor
          · intro observed present
            have permutation := insertAromaticCanonicalRule6PromotedKey_perm compare key tail
            have sourcePresent : observed ∈ key :: tail := (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse : compare head key = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

theorem sortAromaticCanonicalRule6PromotedKeys_descending
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering)
    [Std.TransCmp compare] :
    ∀ keys,
      AromaticCanonicalRule6PromotedKeysDescending compare
        (sortAromaticCanonicalRule6PromotedKeys compare keys)
  | [] => by
      simp [sortAromaticCanonicalRule6PromotedKeys,
        AromaticCanonicalRule6PromotedKeysDescending]
  | key :: keys =>
      insertAromaticCanonicalRule6PromotedKey_descending compare key
        (sortAromaticCanonicalRule6PromotedKeys compare keys)
        (sortAromaticCanonicalRule6PromotedKeys_descending compare keys)

def aromaticCanonicalRule6PromotionMarker
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (reference : source.AromaticCanonicalAtom)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) : Nat :=
  if cursor.occurrence.1.node.current? = some reference then 1 else 0

def aromaticCanonicalRule6PromotionChildLayerCount
    {source : AuthoritativeChemicalInput}
    (children : List source.AromaticCanonicalRule6PromotedKey) : Nat :=
  children.foldl (fun longest child => max longest child.promotion.length) 0

def aromaticCanonicalRule6RankedChildTail
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering)
    (previous : source.AromaticCanonicalRule6PromotedKey) (rank : Nat) :
    List source.AromaticCanonicalRule6PromotedKey →
      List (source.AromaticCanonicalRule6PromotedKey × Nat)
  | [] => []
  | child :: children =>
      let childRank := if compare child previous = Ordering.eq then rank else rank + 1
      (child, childRank) ::
        aromaticCanonicalRule6RankedChildTail compare child childRank children

def aromaticCanonicalRule6RankedChildren
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering) :
    List source.AromaticCanonicalRule6PromotedKey →
      List (source.AromaticCanonicalRule6PromotedKey × Nat)
  | [] => []
  | child :: children =>
      (child, 0) :: aromaticCanonicalRule6RankedChildTail compare child 0 children

def mergeAromaticCanonicalRule6PromotionChildren
    {source : AuthoritativeChemicalInput}
    (compare : source.AromaticCanonicalRule6PromotedKey →
      source.AromaticCanonicalRule6PromotedKey → Ordering)
    (children : List source.AromaticCanonicalRule6PromotedKey) :
    List (List (OfficialSparseEntry Nat)) :=
  let count := aromaticCanonicalRule6PromotionChildLayerCount children
  let ranked := aromaticCanonicalRule6RankedChildren compare children
  (List.range count).map fun depth =>
    ranked.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 (child.1.promotion.getD depth [])

/-- Build the recursively promoted key.  At each node the certified pre-Rule-6 key is built first;
children are reranked by the full promoted comparator before their promotion layers are merged. -/
noncomputable def buildAromaticCanonicalRule6PromotedKey?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalRule6PromotedKey
  | 0, cursor => do
      let prior ← source.buildAromaticCanonicalRerootCompoundRule45Key?
        target view 0 cursor
      let children ← source.aromaticCanonicalRerootChildren? cursor
      if children = [] then
        some
          { prior := prior
            promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
      else none
  | fuel + 1, cursor => do
      let prior ← source.buildAromaticCanonicalRerootCompoundRule45Key?
        target view (fuel + 1) cursor
      let children ← source.aromaticCanonicalRerootChildren? cursor
      let marker := aromaticCanonicalRule6PromotionMarker reference cursor
      if children = [] then
        some { prior := prior, promotion := [[([], marker)]] }
      else
        let childKeys ← children.mapM
          (source.buildAromaticCanonicalRule6PromotedKey? target view reference fuel)
        let compare := source.compareAromaticCanonicalRule6PromotedKeys
        let sorted := sortAromaticCanonicalRule6PromotedKeys compare childKeys
        some
          { prior := prior
            promotion := [[([], marker)]] ++
              mergeAromaticCanonicalRule6PromotionChildren compare sorted }

/- Independent recursive semantics. -/
mutual
inductive DeclarativeAromaticCanonicalRule6PromotedKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalRule6PromotedKey → Prop
  | zeroLeaf {cursor prior children}
      (priorDerivation : source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
        target view 0 cursor prior)
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = []) :
      DeclarativeAromaticCanonicalRule6PromotedKey source target view reference 0 cursor
        { prior := prior
          promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
  | successorLeaf {fuel cursor prior children}
      (priorDerivation : source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
        target view (fuel + 1) cursor prior)
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = []) :
      DeclarativeAromaticCanonicalRule6PromotedKey source target view reference
        (fuel + 1) cursor
          { prior := prior
            promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] }
  | successorBranch {fuel cursor prior children childKeys sorted}
      (priorDerivation : source.DeclarativeAromaticCanonicalRerootCompoundRule45Key
        target view (fuel + 1) cursor prior)
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (nonterminal : children ≠ [])
      (childDerivations : DeclarativeAromaticCanonicalRule6PromotedKeyList
        source target view reference fuel children childKeys)
      (permutation : sorted.Perm childKeys)
      (descending : AromaticCanonicalRule6PromotedKeysDescending
        source.compareAromaticCanonicalRule6PromotedKeys sorted) :
      DeclarativeAromaticCanonicalRule6PromotedKey source target view reference
        (fuel + 1) cursor
          { prior := prior
            promotion := [[([], aromaticCanonicalRule6PromotionMarker reference cursor)]] ++
              mergeAromaticCanonicalRule6PromotionChildren
                source.compareAromaticCanonicalRule6PromotedKeys sorted }

inductive DeclarativeAromaticCanonicalRule6PromotedKeyList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
      List source.AromaticCanonicalRule6PromotedKey → Prop
  | nil (fuel) : DeclarativeAromaticCanonicalRule6PromotedKeyList
      source target view reference fuel [] []
  | cons {fuel cursor cursors key keys}
      (head : DeclarativeAromaticCanonicalRule6PromotedKey
        source target view reference fuel cursor key)
      (tail : DeclarativeAromaticCanonicalRule6PromotedKeyList
        source target view reference fuel cursors keys) :
      DeclarativeAromaticCanonicalRule6PromotedKeyList
        source target view reference fuel (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildAromaticCanonicalRule6PromotedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom)
    (sound : ∀ cursor key,
      source.buildAromaticCanonicalRule6PromotedKey?
        target view reference fuel cursor = some key →
      source.DeclarativeAromaticCanonicalRule6PromotedKey
        target view reference fuel cursor key) :
    ∀ cursors keys,
      cursors.mapM (source.buildAromaticCanonicalRule6PromotedKey?
        target view reference fuel) = some keys →
      DeclarativeAromaticCanonicalRule6PromotedKeyList
        source target view reference fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeAromaticCanonicalRule6PromotedKeyList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalRule6PromotedKey?
          target view reference fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalRule6PromotedKey?
                target view reference fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeAromaticCanonicalRule6PromotedKeyList.cons
                (sound cursor head headComputed)
                (mapM_buildAromaticCanonicalRule6PromotedKey?_sound
                  source target view reference sound cursors tail tailComputed)

theorem buildAromaticCanonicalRule6PromotedKey?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalRule6PromotedKey?
        target view reference fuel cursor = some key →
      source.DeclarativeAromaticCanonicalRule6PromotedKey
        target view reference fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalRule6PromotedKey? at computed
      cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule45Key?
          target view 0 cursor with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
          let children := source.aromaticCanonicalRerootChildren cursor
          by_cases terminal : children = []
          · simp [children, terminal] at computed
            subst key
            exact DeclarativeAromaticCanonicalRule6PromotedKey.zeroLeaf
              (source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
                target view 0 cursor prior priorComputed)
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
          · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalRule6PromotedKey? at computed
      cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule45Key?
          target view (fuel + 1) cursor with
      | none => simp [priorComputed] at computed
      | some prior =>
          simp only [priorComputed, aromaticCanonicalRerootChildren?] at computed
          let children := source.aromaticCanonicalRerootChildren cursor
          by_cases terminal : children = []
          · simp [children, terminal] at computed
            subst key
            exact DeclarativeAromaticCanonicalRule6PromotedKey.successorLeaf
              (source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
                target view (fuel + 1) cursor prior priorComputed)
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal
          · cases childKeysComputed : children.mapM
                (source.buildAromaticCanonicalRule6PromotedKey?
                  target view reference fuel) with
            | none => simp [children, terminal, childKeysComputed] at computed
            | some childKeys =>
                let compare := source.compareAromaticCanonicalRule6PromotedKeys
                let sorted := sortAromaticCanonicalRule6PromotedKeys compare childKeys
                simp [children, terminal, childKeysComputed] at computed
                subst key
                letI : Std.TransCmp compare :=
                  source.compareAromaticCanonicalRule6PromotedKeys_transCmp
                exact DeclarativeAromaticCanonicalRule6PromotedKey.successorBranch
                  (source.buildAromaticCanonicalRerootCompoundRule45Key?_sound
                    target view (fuel + 1) cursor prior priorComputed)
                  (source.aromaticCanonicalRerootChildren_sound cursor) terminal
                  (mapM_buildAromaticCanonicalRule6PromotedKey?_sound
                    source target view reference
                    (source.buildAromaticCanonicalRule6PromotedKey?_sound
                      target view reference fuel)
                    children childKeys childKeysComputed)
                  (sortAromaticCanonicalRule6PromotedKeys_perm compare childKeys)
                  (sortAromaticCanonicalRule6PromotedKeys_descending compare childKeys)

/-- Reference promotion and its dynamic reranking are defined on the semantic source alone. -/
theorem buildAromaticCanonicalRule6PromotedKey_source_fixed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (reference : source.AromaticCanonicalAtom)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.buildAromaticCanonicalRule6PromotedKey? target view reference fuel cursor =
      source.buildAromaticCanonicalRule6PromotedKey? target view reference fuel cursor :=
  rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
