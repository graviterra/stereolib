import TetraStereo.OneCenter.LocalizedOccurrenceRule4cCarrier

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Rule-major constitutional keys over occurrence reroot cursors

The ordinary localized key compiler expands only away from its original ligand root.  Auxiliary
descriptor assignment instead compares all four ligands at an internal occurrence, which requires
the occurrence zipper: one branch may point toward the original final root and the other branches
point outward.  This module compiles complete Rules-1a--2 keys directly over those reroot cursors.

Fuel exhaustion is fail-closed: a nonterminal cursor at zero fuel returns `none`; no incomplete key
is admitted.  Successful compilation has an independent recursive derivation recording the exact
reroot child frame, one derivation per child, a multiplicity-preserving child-key permutation, and
descending rule-major sibling order.
-/

namespace CertifiedLocalizedCIPInput

/-- Fail-closed complete rule-major compilation over the occurrence zipper. -/
noncomputable def buildLocalizedRerootRuleMajorKey?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option (OfficialRuleMajorKey input.Atom)
  | 0, cursor => do
      let children ← input.localizedRerootChildren? cursor
      if children = [] then
        some (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true)
      else none
  | fuel + 1, cursor => do
      let children ← input.localizedRerootChildren? cursor
      if children = [] then
        some (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true)
      else
        let childKeys ← children.mapM
          (input.buildLocalizedRerootRuleMajorKey? fuel)
        let sorted ← OfficialRuleMajorKey.sort? childKeys
        some (OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey
            cursor.occurrence.1.node false) sorted)

private theorem mapM_buildLocalizedRerootRuleMajorKey?_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat} :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List (OfficialRuleMajorKey input.Atom)),
      cursors.mapM (input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel) = some keys →
      ∀ key, key ∈ keys →
        ∃ cursor, cursor ∈ cursors ∧
          input.buildLocalizedRerootRuleMajorKey? fuel cursor = some key
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootRuleMajorKey? fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootRuleMajorKey? fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨cursor, by simp, headComputed⟩
              · rcases input.mapM_buildLocalizedRerootRuleMajorKey?_member
                    cursors tail tailComputed key tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem cursor sourcePresent, sourceComputed⟩

/-- Every successfully compiled reroot key is complete. -/
theorem buildLocalizedRerootRuleMajorKey?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      key.complete = true
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootRuleMajorKey? fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
                | none =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                | some sorted =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                    subst key
                    unfold OfficialRuleMajorKey.assemble
                    rw [List.all_eq_true]
                    intro child childPresent
                    have sourcePresent : child ∈ childKeys :=
                      (OfficialRuleMajorKey.sort?_perm childKeys sorted
                        sortedComputed).mem_iff.mp childPresent
                    rcases input.mapM_buildLocalizedRerootRuleMajorKey?_member
                        children childKeys childKeysComputed child sourcePresent with
                      ⟨childCursor, _cursorPresent, childComputed⟩
                    exact input.buildLocalizedRerootRuleMajorKey?_complete
                      fuel childCursor child childComputed

/-- Every successful reroot key's cached Rules-1a--2 projections are exact fresh observations of
the same addressed provenance nodes. -/
theorem buildLocalizedRerootRuleMajorKey?_sourceAligned
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      OfficialRuleMajorKey.SourceAligned input.moleculeGraph key
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
              cursor.occurrence.1.node true
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
              cursor.occurrence.1.node true
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootRuleMajorKey? fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
                | none =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                | some sorted =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                    subst key
                    apply OfficialRuleMajorKey.SourceAligned.assemble
                    · exact input.moleculeGraph.officialRuleMajorRootKey_sourceAligned
                        cursor.occurrence.1.node false
                    · intro child childPresent
                      have sourcePresent : child ∈ childKeys :=
                        (OfficialRuleMajorKey.sort?_perm childKeys sorted
                          sortedComputed).mem_iff.mp childPresent
                      rcases input.mapM_buildLocalizedRerootRuleMajorKey?_member
                          children childKeys childKeysComputed child sourcePresent with
                        ⟨childCursor, _cursorPresent, childComputed⟩
                      exact input.buildLocalizedRerootRuleMajorKey?_sourceAligned
                        fuel childCursor child childComputed

/-! ## Independent recursive derivation -/

mutual
  /-- Proof-relevant successful compilation of one reroot cursor. -/
  inductive DeclarativeLocalizedRerootRuleMajorKey
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
      Nat → input.LocalizedRerootCursor carrierFuel →
        OfficialRuleMajorKey input.Atom → Prop
    | terminal {fuel cursor children}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (empty : children = []) :
        DeclarativeLocalizedRerootRuleMajorKey input fuel cursor
          (input.moleculeGraph.officialRuleMajorRootKey
            cursor.occurrence.1.node true)
    | branch {fuel cursor children childKeys sorted}
        (frame : input.DeclarativeLocalizedRerootChildren cursor children)
        (nonempty : children ≠ [])
        (childDerivations : DeclarativeLocalizedRerootRuleMajorKeyList input
          fuel children childKeys)
        (ranking : sorted.Perm childKeys)
        (descending : OfficialRuleMajorKey.Descending sorted) :
        DeclarativeLocalizedRerootRuleMajorKey input (fuel + 1) cursor
          (OfficialRuleMajorKey.assemble
            (input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node false) sorted)

  /-- Pointwise recursive derivation for every exact reroot child. -/
  inductive DeclarativeLocalizedRerootRuleMajorKeyList
      (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
      Nat → List (input.LocalizedRerootCursor carrierFuel) →
        List (OfficialRuleMajorKey input.Atom) → Prop
    | nil (fuel : Nat) :
        DeclarativeLocalizedRerootRuleMajorKeyList input fuel [] []
    | cons {fuel cursor cursors key keys}
        (head : DeclarativeLocalizedRerootRuleMajorKey input fuel cursor key)
        (tail : DeclarativeLocalizedRerootRuleMajorKeyList input fuel cursors keys) :
        DeclarativeLocalizedRerootRuleMajorKeyList input fuel
          (cursor :: cursors) (key :: keys)
end

private theorem mapM_buildLocalizedRerootRuleMajorKey?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (sound : ∀ cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List (OfficialRuleMajorKey input.Atom)),
      cursors.mapM (input.buildLocalizedRerootRuleMajorKey? fuel) = some keys →
      input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeLocalizedRerootRuleMajorKeyList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootRuleMajorKey? fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootRuleMajorKey? fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeLocalizedRerootRuleMajorKeyList.cons
                (sound cursor head headComputed)
                (input.mapM_buildLocalizedRerootRuleMajorKey?_sound
                  sound cursors tail tailComputed)

/-- Successful executable reroot compilation satisfies the independent exact-frame recursive
relation and records a lawful descending sibling ranking at every node. -/
theorem buildLocalizedRerootRuleMajorKey?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel cursor key,
      input.buildLocalizedRerootRuleMajorKey?
        (carrierFuel := carrierFuel) fuel cursor = some key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact DeclarativeLocalizedRerootRuleMajorKey.terminal
              (input.localizedRerootChildren?_sound cursor children childrenComputed)
              terminal
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootRuleMajorKey? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            exact DeclarativeLocalizedRerootRuleMajorKey.terminal
              (input.localizedRerootChildren?_sound cursor children childrenComputed)
              terminal
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootRuleMajorKey? fuel) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
                | none =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                | some sorted =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      sortedComputed] at computed
                    subst key
                    exact DeclarativeLocalizedRerootRuleMajorKey.branch
                      (input.localizedRerootChildren?_sound
                        cursor children childrenComputed)
                      terminal
                      (input.mapM_buildLocalizedRerootRuleMajorKey?_sound
                        (fun child childKey childComputed =>
                          input.buildLocalizedRerootRuleMajorKey?_sound
                            fuel child childKey childComputed)
                        children childKeys childKeysComputed)
                      (OfficialRuleMajorKey.sort?_perm
                        childKeys sorted sortedComputed)
                      (OfficialRuleMajorKey.sort?_descending
                        childKeys sorted sortedComputed)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
