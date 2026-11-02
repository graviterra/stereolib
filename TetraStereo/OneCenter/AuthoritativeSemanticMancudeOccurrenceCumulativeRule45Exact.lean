import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule45Key

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Exact source-canonical cumulative Rules-4a--5 keys

The broad declarative relation in `AuthoritativeSemanticMancudeOccurrenceRule45Key` admits
every descending permutation of comparator-equivalent children.  That is the right extensional
chemical soundness statement, but it is deliberately too broad to characterize the deterministic
stable sort used by the executable compiler.  This module supplies the missing canonical
relation.  Structural insertion and sorting judgments record the exact comparison branch at each
step, and the recursive key judgment is equivalent to executable success in both directions.
-/

/-- Canonical structural insertion under the source cumulative-key comparator. -/
inductive DeclarativeInsertAromaticCanonicalCumulativeRule45Key
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalCumulativeRule45Key) :
    List source.AromaticCanonicalCumulativeRule45Key →
      List source.AromaticCanonicalCumulativeRule45Key → Prop
  | nil : DeclarativeInsertAromaticCanonicalCumulativeRule45Key source key [] [key]
  | beforeEq {head tail}
      (compared : source.compareAromaticCanonicalCumulativeRule45Keys key head = .eq) :
      DeclarativeInsertAromaticCanonicalCumulativeRule45Key source key
        (head :: tail) (key :: head :: tail)
  | beforeGt {head tail}
      (compared : source.compareAromaticCanonicalCumulativeRule45Keys key head = .gt) :
      DeclarativeInsertAromaticCanonicalCumulativeRule45Key source key
        (head :: tail) (key :: head :: tail)
  | afterLt {head tail inserted}
      (compared : source.compareAromaticCanonicalCumulativeRule45Keys key head = .lt)
      (tailDerived : DeclarativeInsertAromaticCanonicalCumulativeRule45Key
        source key tail inserted) :
      DeclarativeInsertAromaticCanonicalCumulativeRule45Key source key
        (head :: tail) (head :: inserted)

/-- Source insertion is exactly the independent canonical insertion derivation. -/
theorem insertAromaticCanonicalCumulativeRule45Key_eq_iff_canonical
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalCumulativeRule45Key) :
    ∀ keys result,
      insertAromaticCanonicalCumulativeRule45Key
          source.compareAromaticCanonicalCumulativeRule45Keys key keys = result ↔
        source.DeclarativeInsertAromaticCanonicalCumulativeRule45Key key keys result
  | [], result => by
      constructor
      · intro computed
        simp [insertAromaticCanonicalCumulativeRule45Key] at computed
        subst result
        exact DeclarativeInsertAromaticCanonicalCumulativeRule45Key.nil
      · intro derived
        cases derived
        rfl
  | head :: tail, result => by
      cases comparison : source.compareAromaticCanonicalCumulativeRule45Keys key head with
      | eq =>
          constructor
          · intro computed
            simp [insertAromaticCanonicalCumulativeRule45Key, comparison] at computed
            subst result
            exact DeclarativeInsertAromaticCanonicalCumulativeRule45Key.beforeEq comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [insertAromaticCanonicalCumulativeRule45Key, compared]
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared _ => simp [comparison] at compared
      | gt =>
          constructor
          · intro computed
            simp [insertAromaticCanonicalCumulativeRule45Key, comparison] at computed
            subst result
            exact DeclarativeInsertAromaticCanonicalCumulativeRule45Key.beforeGt comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [insertAromaticCanonicalCumulativeRule45Key, compared]
            | afterLt compared _ => simp [comparison] at compared
      | lt =>
          constructor
          · intro computed
            simp only [insertAromaticCanonicalCumulativeRule45Key, comparison] at computed
            cases result with
            | nil => simp at computed
            | cons resultHead resultTail =>
                simp at computed
                rcases computed with ⟨rfl, computed⟩
                exact DeclarativeInsertAromaticCanonicalCumulativeRule45Key.afterLt comparison
                  ((source.insertAromaticCanonicalCumulativeRule45Key_eq_iff_canonical
                    key tail resultTail).mp computed)
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared tailDerived =>
                simp only [insertAromaticCanonicalCumulativeRule45Key, compared,
                  List.cons.injEq, true_and]
                exact (source.insertAromaticCanonicalCumulativeRule45Key_eq_iff_canonical
                  key tail _).mpr tailDerived

/-- Canonical structural stable-sort derivation. -/
inductive DeclarativeSortAromaticCanonicalCumulativeRule45Keys
    (source : AuthoritativeChemicalInput) :
    List source.AromaticCanonicalCumulativeRule45Key →
      List source.AromaticCanonicalCumulativeRule45Key → Prop
  | nil : DeclarativeSortAromaticCanonicalCumulativeRule45Keys source [] []
  | cons {key keys sortedTail result}
      (tail : DeclarativeSortAromaticCanonicalCumulativeRule45Keys source keys sortedTail)
      (inserted : source.DeclarativeInsertAromaticCanonicalCumulativeRule45Key
        key sortedTail result) :
      DeclarativeSortAromaticCanonicalCumulativeRule45Keys source (key :: keys) result

/-- Source stable sort is exactly the independent canonical sort derivation. -/
theorem sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical
    (source : AuthoritativeChemicalInput) :
    ∀ keys result,
      sortAromaticCanonicalCumulativeRule45Keys
          source.compareAromaticCanonicalCumulativeRule45Keys keys = result ↔
        source.DeclarativeSortAromaticCanonicalCumulativeRule45Keys keys result
  | [], result => by
      constructor
      · intro computed
        simp [sortAromaticCanonicalCumulativeRule45Keys] at computed
        subst result
        exact DeclarativeSortAromaticCanonicalCumulativeRule45Keys.nil
      · intro derived
        cases derived
        rfl
  | key :: keys, result => by
      constructor
      · intro computed
        unfold sortAromaticCanonicalCumulativeRule45Keys at computed
        let sortedTail := sortAromaticCanonicalCumulativeRule45Keys
          source.compareAromaticCanonicalCumulativeRule45Keys keys
        exact DeclarativeSortAromaticCanonicalCumulativeRule45Keys.cons
          ((source.sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical
            keys sortedTail).mp rfl)
          ((source.insertAromaticCanonicalCumulativeRule45Key_eq_iff_canonical
            key sortedTail result).mp computed)
      · intro derived
        cases derived with
        | cons tail inserted =>
            unfold sortAromaticCanonicalCumulativeRule45Keys
            rw [(source.sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical
              _ _).mpr tail]
            exact (source.insertAromaticCanonicalCumulativeRule45Key_eq_iff_canonical
              key _ result).mpr inserted

mutual
  /-- Canonical recursive derivation of one source cumulative Rules-4a--5 key. -/
  inductive CanonicalAromaticCanonicalCumulativeRule45Key
      (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (target : source.AromaticCanonicalOccurrence carrierFuel)
      (view : source.AromaticCanonicalDependencyView target) :
      Nat → source.AromaticCanonicalRerootCursor carrierFuel →
        source.AromaticCanonicalCumulativeRule45Key → Prop
    | terminal {fuel cursor children label}
        (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
        (empty : children = [])
        (observed : source.DeclarativeAromaticCanonicalDependencyLabel
          target view cursor label) :
        CanonicalAromaticCanonicalCumulativeRule45Key source stage target view fuel cursor
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
    | branch {fuel cursor children label childKeys sorted}
        (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
        (nonempty : children ≠ [])
        (observed : source.DeclarativeAromaticCanonicalDependencyLabel
          target view cursor label)
        (childDerivations : CanonicalAromaticCanonicalCumulativeRule45KeyList
          source stage target view fuel children childKeys)
        (ranking : source.DeclarativeSortAromaticCanonicalCumulativeRule45Keys
          childKeys sorted) :
        CanonicalAromaticCanonicalCumulativeRule45Key source stage target view
          (fuel + 1) cursor
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                mergeAromaticCanonicalDescriptorChildren sorted
            labels := [[([], label)]] ++
              mergeAromaticCanonicalLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              mergeAromaticCanonicalRankedLabelChildren
                source.compareAromaticCanonicalCumulativeRule45Keys sorted }

  /-- Canonical pointwise derivations for an exact source child list. -/
  inductive CanonicalAromaticCanonicalCumulativeRule45KeyList
      (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (target : source.AromaticCanonicalOccurrence carrierFuel)
      (view : source.AromaticCanonicalDependencyView target) :
      Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
        List source.AromaticCanonicalCumulativeRule45Key → Prop
    | nil (fuel : Nat) :
        CanonicalAromaticCanonicalCumulativeRule45KeyList
          source stage target view fuel [] []
    | cons {fuel cursor cursors key keys}
        (head : CanonicalAromaticCanonicalCumulativeRule45Key
          source stage target view fuel cursor key)
        (tail : CanonicalAromaticCanonicalCumulativeRule45KeyList
          source stage target view fuel cursors keys) :
        CanonicalAromaticCanonicalCumulativeRule45KeyList
          source stage target view fuel (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (exact : ∀ cursor key,
      source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor =
          some key ↔
        source.CanonicalAromaticCanonicalCumulativeRule45Key
          stage target view fuel cursor key) :
    ∀ cursors keys,
      cursors.mapM (source.buildAromaticCanonicalCumulativeRule45Key?
        stage target view fuel) = some keys ↔
      source.CanonicalAromaticCanonicalCumulativeRule45KeyList
        stage target view fuel cursors keys
  | [], keys => by
      constructor
      · intro computed
        simp at computed
        subst keys
        exact CanonicalAromaticCanonicalCumulativeRule45KeyList.nil fuel
      · intro derived
        cases derived
        rfl
  | cursor :: cursors, keys => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : source.buildAromaticCanonicalCumulativeRule45Key?
            stage target view fuel cursor with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : cursors.mapM
                (source.buildAromaticCanonicalCumulativeRule45Key?
                  stage target view fuel) with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst keys
                exact CanonicalAromaticCanonicalCumulativeRule45KeyList.cons
                  ((exact cursor head).mp headComputed)
                  ((source.mapM_buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                    stage target view exact cursors tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            rw [List.mapM_cons, (exact _ _).mpr head]
            rw [(source.mapM_buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
              stage target view exact _ _).mpr tail]
            rfl

/-- Executable source cumulative-key success is equivalent to the canonical independent
recursive derivation. -/
theorem buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ fuel cursor key,
      source.buildAromaticCanonicalCumulativeRule45Key?
          stage target view fuel cursor = some key ↔
        source.CanonicalAromaticCanonicalCumulativeRule45Key
          stage target view fuel cursor key
  | 0, cursor, key => by
      constructor
      · intro computed
        unfold buildAromaticCanonicalCumulativeRule45Key? at computed
        cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            by_cases terminal : children = []
            · simp [childrenComputed, terminal] at computed
              subst key
              exact CanonicalAromaticCanonicalCumulativeRule45Key.terminal
                ((source.aromaticCanonicalRerootChildren?_eq_some_iff
                  cursor children).mp childrenComputed)
                terminal
                ((source.aromaticCanonicalDependencyLabel_eq_iff
                  target view cursor _).mp rfl)
            · simp [childrenComputed, terminal] at computed
      · intro derived
        cases derived with
        | terminal frame empty observed =>
            have childrenComputed :=
              (source.aromaticCanonicalRerootChildren?_eq_some_iff cursor _).mpr frame
            have labelComputed :=
              (source.aromaticCanonicalDependencyLabel_eq_iff
                target view cursor _).mpr observed
            unfold buildAromaticCanonicalCumulativeRule45Key?
            simp [childrenComputed, empty, labelComputed]
  | fuel + 1, cursor, key => by
      constructor
      · intro computed
        unfold buildAromaticCanonicalCumulativeRule45Key? at computed
        cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            by_cases terminal : children = []
            · simp [childrenComputed, terminal] at computed
              subst key
              exact CanonicalAromaticCanonicalCumulativeRule45Key.terminal
                ((source.aromaticCanonicalRerootChildren?_eq_some_iff
                  cursor children).mp childrenComputed)
                terminal
                ((source.aromaticCanonicalDependencyLabel_eq_iff
                  target view cursor _).mp rfl)
            · cases childKeysComputed : children.mapM
                  (source.buildAromaticCanonicalCumulativeRule45Key?
                    stage target view fuel) with
              | none => simp [childrenComputed, terminal, childKeysComputed] at computed
              | some childKeys =>
                  simp [childrenComputed, terminal, childKeysComputed] at computed
                  subst key
                  exact CanonicalAromaticCanonicalCumulativeRule45Key.branch
                    ((source.aromaticCanonicalRerootChildren?_eq_some_iff
                      cursor children).mp childrenComputed)
                    terminal
                    ((source.aromaticCanonicalDependencyLabel_eq_iff
                      target view cursor _).mp rfl)
                    ((source.mapM_buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                      stage target view
                      (fun child childKey =>
                        source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                          stage target view fuel child childKey)
                      children childKeys).mp childKeysComputed)
                    ((source.sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical
                      childKeys _).mp rfl)
      · intro derived
        cases derived with
        | terminal frame empty observed =>
            have childrenComputed :=
              (source.aromaticCanonicalRerootChildren?_eq_some_iff cursor _).mpr frame
            have labelComputed :=
              (source.aromaticCanonicalDependencyLabel_eq_iff
                target view cursor _).mpr observed
            unfold buildAromaticCanonicalCumulativeRule45Key?
            simp [childrenComputed, empty, labelComputed]
        | @branch _ _ children label childKeys sorted frame nonempty observed
            childDerivations ranking =>
            have childrenComputed :=
              (source.aromaticCanonicalRerootChildren?_eq_some_iff
                cursor children).mpr frame
            have labelComputed :=
              (source.aromaticCanonicalDependencyLabel_eq_iff
                target view cursor label).mpr observed
            have childKeysComputed :=
              (source.mapM_buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                stage target view
                (fun child childKey =>
                  source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
                    stage target view fuel child childKey)
                children childKeys).mpr childDerivations
            have sortedComputed :=
              (source.sortAromaticCanonicalCumulativeRule45Keys_eq_iff_canonical
                childKeys sorted).mpr ranking
            unfold buildAromaticCanonicalCumulativeRule45Key?
            simp [childrenComputed, nonempty, labelComputed,
              childKeysComputed, sortedComputed]

/-- The canonical relation refines the broad, permutation-insensitive chemical semantics. -/
theorem CanonicalAromaticCanonicalCumulativeRule45Key.sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalCumulativeRule45Key)
    (canonical : source.CanonicalAromaticCanonicalCumulativeRule45Key
      stage target view fuel cursor key) :
    source.DeclarativeAromaticCanonicalCumulativeRule45Key
      stage target view fuel cursor key :=
  source.buildAromaticCanonicalCumulativeRule45Key?_sound stage target view fuel cursor key
    ((source.buildAromaticCanonicalCumulativeRule45Key?_eq_some_iff_canonical
      stage target view fuel cursor key).mpr canonical)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
