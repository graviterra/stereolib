import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Canonical exact relation for cumulative reroot keys

The broad soundness relation in `LocalizedRerootCumulativeRule45Key` permits every descending
permutation of comparator-equivalent children.  That is useful for extensional chemical
soundness, but it cannot characterize one deterministic executable key.  This module adds a
second, canonical relation.  Its insertion and sorting judgments are structural and independent;
they record the exact stable comparison branch at every step.  The resulting recursive key
judgment is proved equivalent to executable success in both directions.
-/

namespace CertifiedLocalizedCIPInput

/-- Canonical structural insertion under the cumulative key comparator. -/
inductive DeclarativeInsertLocalizedRerootCumulativeRule45Key
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    List input.LocalizedRerootCumulativeRule45Key →
      List input.LocalizedRerootCumulativeRule45Key → Prop
  | nil : DeclarativeInsertLocalizedRerootCumulativeRule45Key input key [] [key]
  | beforeEq {head tail}
      (compared : input.compareLocalizedRerootCumulativeRule45Keys key head = .eq) :
      DeclarativeInsertLocalizedRerootCumulativeRule45Key input key
        (head :: tail) (key :: head :: tail)
  | beforeGt {head tail}
      (compared : input.compareLocalizedRerootCumulativeRule45Keys key head = .gt) :
      DeclarativeInsertLocalizedRerootCumulativeRule45Key input key
        (head :: tail) (key :: head :: tail)
  | afterLt {head tail inserted}
      (compared : input.compareLocalizedRerootCumulativeRule45Keys key head = .lt)
      (tailDerived : DeclarativeInsertLocalizedRerootCumulativeRule45Key
        input key tail inserted) :
      DeclarativeInsertLocalizedRerootCumulativeRule45Key input key
        (head :: tail) (head :: inserted)

/-- Executable insertion is exactly the independent canonical insertion derivation. -/
theorem insertLocalizedRerootCumulativeRule45Key_eq_iff
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    ∀ keys result,
      input.insertLocalizedRerootCumulativeRule45Key key keys = result ↔
        input.DeclarativeInsertLocalizedRerootCumulativeRule45Key key keys result
  | [], result => by
      constructor
      · intro computed
        simp [insertLocalizedRerootCumulativeRule45Key] at computed
        subst result
        exact DeclarativeInsertLocalizedRerootCumulativeRule45Key.nil
      · intro derived
        cases derived
        rfl
  | head :: tail, result => by
      cases comparison : input.compareLocalizedRerootCumulativeRule45Keys key head with
      | eq =>
          constructor
          · intro computed
            simp [insertLocalizedRerootCumulativeRule45Key, comparison] at computed
            subst result
            exact DeclarativeInsertLocalizedRerootCumulativeRule45Key.beforeEq comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [insertLocalizedRerootCumulativeRule45Key, compared]
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared _ => simp [comparison] at compared
      | gt =>
          constructor
          · intro computed
            simp [insertLocalizedRerootCumulativeRule45Key, comparison] at computed
            subst result
            exact DeclarativeInsertLocalizedRerootCumulativeRule45Key.beforeGt comparison
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [insertLocalizedRerootCumulativeRule45Key, compared]
            | afterLt compared _ => simp [comparison] at compared
      | lt =>
          constructor
          · intro computed
            simp only [insertLocalizedRerootCumulativeRule45Key, comparison] at computed
            cases result with
            | nil => simp at computed
            | cons resultHead resultTail =>
                simp at computed
                rcases computed with ⟨rfl, computed⟩
                exact DeclarativeInsertLocalizedRerootCumulativeRule45Key.afterLt comparison
                  ((input.insertLocalizedRerootCumulativeRule45Key_eq_iff
                    key tail resultTail).mp computed)
          · intro derived
            cases derived with
            | beforeEq compared => simp [comparison] at compared
            | beforeGt compared => simp [comparison] at compared
            | afterLt compared tailDerived =>
                simp only [insertLocalizedRerootCumulativeRule45Key, compared,
                  List.cons.injEq, true_and]
                exact (input.insertLocalizedRerootCumulativeRule45Key_eq_iff
                  key tail _).mpr tailDerived

/-- Canonical stable-sort derivation. -/
inductive DeclarativeSortLocalizedRerootCumulativeRule45Keys
    (input : CertifiedLocalizedCIPInput) :
    List input.LocalizedRerootCumulativeRule45Key →
      List input.LocalizedRerootCumulativeRule45Key → Prop
  | nil : DeclarativeSortLocalizedRerootCumulativeRule45Keys input [] []
  | cons {key keys sortedTail result}
      (tail : DeclarativeSortLocalizedRerootCumulativeRule45Keys input keys sortedTail)
      (inserted : input.DeclarativeInsertLocalizedRerootCumulativeRule45Key
        key sortedTail result) :
      DeclarativeSortLocalizedRerootCumulativeRule45Keys input (key :: keys) result

/-- Executable stable sort is exactly the independent canonical sort derivation. -/
theorem sortLocalizedRerootCumulativeRule45Keys_eq_iff
    (input : CertifiedLocalizedCIPInput) :
    ∀ keys result,
      input.sortLocalizedRerootCumulativeRule45Keys keys = result ↔
        input.DeclarativeSortLocalizedRerootCumulativeRule45Keys keys result
  | [], result => by
      constructor
      · intro computed
        simp [sortLocalizedRerootCumulativeRule45Keys] at computed
        subst result
        exact DeclarativeSortLocalizedRerootCumulativeRule45Keys.nil
      · intro derived
        cases derived
        rfl
  | key :: keys, result => by
      constructor
      · intro computed
        unfold sortLocalizedRerootCumulativeRule45Keys at computed
        let sortedTail := input.sortLocalizedRerootCumulativeRule45Keys keys
        exact DeclarativeSortLocalizedRerootCumulativeRule45Keys.cons
          ((input.sortLocalizedRerootCumulativeRule45Keys_eq_iff
            keys sortedTail).mp rfl)
          ((input.insertLocalizedRerootCumulativeRule45Key_eq_iff
            key sortedTail result).mp computed)
      · intro derived
        cases derived with
        | cons tail inserted =>
            unfold sortLocalizedRerootCumulativeRule45Keys
            rw [(input.sortLocalizedRerootCumulativeRule45Keys_eq_iff _ _).mpr tail]
            exact (input.insertLocalizedRerootCumulativeRule45Key_eq_iff
              key _ result).mpr inserted

mutual
  /-- Canonical recursive derivation of one cumulative reroot key. -/
  inductive CanonicalLocalizedRerootCumulativeRule45Key
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → input.LocalizedRerootCursor carrierFuel →
        input.LocalizedRerootCumulativeRule45Key → Prop
    | terminal {fuel cursor children label}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (empty : children = [])
        (observed : input.DeclarativeLocalizedDependencyLabel
          target view cursor label) :
        CanonicalLocalizedRerootCumulativeRule45Key input stage target view fuel cursor
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
    | branch {fuel cursor children label childKeys sorted}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (nonempty : children ≠ [])
        (observed : input.DeclarativeLocalizedDependencyLabel
          target view cursor label)
        (childDerivations : CanonicalLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel children childKeys)
        (ranking : input.DeclarativeSortLocalizedRerootCumulativeRule45Keys
          childKeys sorted) :
        CanonicalLocalizedRerootCumulativeRule45Key input stage target view
          (fuel + 1) cursor
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }

  /-- Canonical pointwise derivations of an exact child list. -/
  inductive CanonicalLocalizedRerootCumulativeRule45KeyList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
      (stage : LocalizedCumulativeRule45Stage)
      (target : input.LocalizedCIPOccurrence carrierFuel)
      (view : input.LocalizedDependencyView target) :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        List input.LocalizedRerootCumulativeRule45Key → Prop
    | nil (fuel : Nat) :
        CanonicalLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel [] []
    | cons {fuel cursor cursors key keys}
        (head : CanonicalLocalizedRerootCumulativeRule45Key
          input stage target view fuel cursor key)
        (tail : CanonicalLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel cursors keys) :
        CanonicalLocalizedRerootCumulativeRule45KeyList
          input stage target view fuel (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (exact : ∀ cursor key,
      input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor =
          some key ↔
        input.CanonicalLocalizedRerootCumulativeRule45Key
          stage target view fuel cursor key) :
    ∀ cursors keys,
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel) = some keys ↔
      input.CanonicalLocalizedRerootCumulativeRule45KeyList
        stage target view fuel cursors keys
  | [], keys => by
      constructor
      · intro computed
        simp at computed
        subst keys
        exact CanonicalLocalizedRerootCumulativeRule45KeyList.nil fuel
      · intro derived
        cases derived
        rfl
  | cursor :: cursors, keys => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : input.buildLocalizedRerootCumulativeRule45Key?
            stage target view fuel cursor with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : cursors.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst keys
                exact CanonicalLocalizedRerootCumulativeRule45KeyList.cons
                  ((exact cursor head).mp headComputed)
                  ((input.mapM_buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                    stage target view exact cursors tail).mp
                    tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            rw [List.mapM_cons, (exact _ _).mpr head]
            rw [(input.mapM_buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
              stage target view exact _ _).mpr tail]
            rfl

/-- Executable cumulative-key success is equivalent to the canonical independent recursive
derivation. -/
theorem buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
          stage target view fuel cursor = some key ↔
        input.CanonicalLocalizedRerootCumulativeRule45Key
          stage target view fuel cursor key
  | 0, cursor, key => by
      constructor
      · intro computed
        unfold buildLocalizedRerootCumulativeRule45Key? at computed
        cases childrenComputed : input.localizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            by_cases terminal : children = []
            · simp [childrenComputed, terminal] at computed
              subst key
              exact CanonicalLocalizedRerootCumulativeRule45Key.terminal
                ((input.localizedRerootChildren?_eq_some_iff
                  cursor children).mp childrenComputed)
                terminal
                ((input.localizedDependencyLabel_eq_iff
                  target view cursor _).mp rfl)
            · simp [childrenComputed, terminal] at computed
      · intro derived
        cases derived with
        | terminal frame empty observed =>
            have childrenComputed :=
              (input.localizedRerootChildren?_eq_some_iff cursor _).mpr frame
            have labelComputed :=
              (input.localizedDependencyLabel_eq_iff target view cursor _).mpr observed
            unfold buildLocalizedRerootCumulativeRule45Key?
            simp [childrenComputed, empty, labelComputed]
  | fuel + 1, cursor, key => by
      constructor
      · intro computed
        unfold buildLocalizedRerootCumulativeRule45Key? at computed
        cases childrenComputed : input.localizedRerootChildren? cursor with
        | none => simp [childrenComputed] at computed
        | some children =>
            by_cases terminal : children = []
            · simp [childrenComputed, terminal] at computed
              subst key
              exact CanonicalLocalizedRerootCumulativeRule45Key.terminal
                ((input.localizedRerootChildren?_eq_some_iff
                  cursor children).mp childrenComputed)
                terminal
                ((input.localizedDependencyLabel_eq_iff
                  target view cursor _).mp rfl)
            · cases childKeysComputed : children.mapM
                  (input.buildLocalizedRerootCumulativeRule45Key?
                    stage target view fuel) with
              | none => simp [childrenComputed, terminal, childKeysComputed] at computed
              | some childKeys =>
                  simp [childrenComputed, terminal, childKeysComputed] at computed
                  subst key
                  exact CanonicalLocalizedRerootCumulativeRule45Key.branch
                    ((input.localizedRerootChildren?_eq_some_iff
                      cursor children).mp childrenComputed)
                    terminal
                    ((input.localizedDependencyLabel_eq_iff
                      target view cursor _).mp rfl)
                    ((input.mapM_buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                      stage target view
                      (fun child childKey =>
                        input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                          stage target view fuel child childKey)
                      children childKeys).mp childKeysComputed)
                    ((input.sortLocalizedRerootCumulativeRule45Keys_eq_iff
                      childKeys _).mp rfl)
      · intro derived
        cases derived with
        | terminal frame empty observed =>
            have childrenComputed :=
              (input.localizedRerootChildren?_eq_some_iff cursor _).mpr frame
            have labelComputed :=
              (input.localizedDependencyLabel_eq_iff target view cursor _).mpr observed
            unfold buildLocalizedRerootCumulativeRule45Key?
            simp [childrenComputed, empty, labelComputed]
        | @branch _ _ children label childKeys sorted frame nonempty observed
            childDerivations ranking =>
            have childrenComputed :=
              (input.localizedRerootChildren?_eq_some_iff cursor children).mpr frame
            have labelComputed :=
              (input.localizedDependencyLabel_eq_iff target view cursor label).mpr observed
            have childKeysComputed :=
              (input.mapM_buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                stage target view
                (fun child childKey =>
                  input.buildLocalizedRerootCumulativeRule45Key?_eq_some_iff_canonical
                    stage target view fuel child childKey)
                children childKeys).mpr childDerivations
            have sortedComputed :=
              (input.sortLocalizedRerootCumulativeRule45Keys_eq_iff
                childKeys sorted).mpr ranking
            unfold buildLocalizedRerootCumulativeRule45Key?
            simp [childrenComputed, nonempty, labelComputed,
              childKeysComputed, sortedComputed]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
