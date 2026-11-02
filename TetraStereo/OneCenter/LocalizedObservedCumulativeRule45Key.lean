import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.OfficialRuleMajorObservation

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Observed cumulative Rule-45 keys with a fail-closed Rule-1b observer

`LocalizedParametricCumulativeLabels` separates the auxiliary-label source from the cumulative
Rules-4a--5 key construction, but its constitutional component is still hard-wired to the stored
`OfficialCIPNode.rule1bRootDistance` observation.  `OfficialRuleMajorObservation` supplies the
companion `officialRuleMajorRootKeyWith` for an arbitrary *total* `observe : OfficialCIPNode V → ℕ`
callback.

This module closes the remaining seam for the cumulative builder: it adds a fail-closed observer
`observe : OfficialCIPNode input.Atom → Option Nat` alongside the arbitrary label callback
`read : cursor → Option LocalizedAuxiliaryLabel`.  The root helper
`MoleculeGraph.observedRuleMajorRootKey?` first *succeeds* on the observer (`observe node = some
scalar`) and only then composes with the existing total callback
`officialRuleMajorRootKeyWith` at the returned scalar; a `none` observation fails the whole build,
and no `getD`-style default is ever substituted.  The provenance `sourceNodes` are left untouched.

## Main results

* `buildLocalizedObservedCumulativeRule45Key?_eq_legacy` — specializing `observe` to
  `some ∘ rule1bRootDistance` and `read` to `localizedDependencyLabel target view` reproduces the
  legacy `buildLocalizedRerootCumulativeRule45Key?` *exactly*, for every fuel and cursor.
* `buildLocalizedObservedCumulativeRule45Key?_sourceNodes_eq_legacy` — the provenance trees are
  preserved exactly by that specialization.
* `buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1b_head` — the root Rule-1b head
  of any successful observed build is exactly the scalar returned by `observe` at the root node.
* `buildLocalizedObservedCumulativeRule45Key?_constitutional_complete` — every successful observed
  build has a complete constitutional projection, whatever the observer and label callback are.
* `buildLocalizedObservedCumulativeRule45Key?_exists_of_available` — finite-budget availability:
  if the actual structural reroot expansion is complete within the fuel bound
  (`LocalizedRerootExpansionCompleteWithin`) and `observe` is pointwise available on every node
  reached by that expansion (`LocalizedRerootReachedNodes`), then a key exists.

## Scope

The child enumeration `localizedRerootChildren?`, the cumulative sibling sort
`sortLocalizedRerootCumulativeRule45Keys`, and the descriptor/label/ranked-label merges are reused
verbatim from the existing cumulative construction; no second solver is introduced.  No parent
strictness is ported, and no hypothesis about a pre-existing key or a desired comparator outcome is
assumed.  This module proves structural mathematics about the observed compiler; it does not claim
that a particular `Option Nat` observer is the normative chemical Rule-1b reading — implemented
transport of an intended observer to an actual frame is stated, not a claim of normative origin.
-/

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Fail-closed observed root key.  The Rule-1b scalar is read through the `Option Nat` observer;
only after that read succeeds is the existing total-`Nat` callback
`officialRuleMajorRootKeyWith` applied at the returned scalar.  A `none` observation fails closed,
and the provenance `sourceNodes` field is left exactly `[[([], node)]]`. -/
def observedRuleMajorRootKey? (observe : OfficialCIPNode V → Option Nat)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    Option (OfficialRuleMajorKey V) :=
  match observe node with
  | none => none
  | some scalar => some (m.officialRuleMajorRootKeyWith (fun _ => scalar) node complete)

/-- The observed root helper reproduces the legacy root key exactly when the observer is the total
`rule1bRootDistance` observation. -/
theorem observedRuleMajorRootKey?_eq_rule1bRootDistance (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) :
    observedRuleMajorRootKey? (fun node => some node.rule1bRootDistance) m node complete =
      some (m.officialRuleMajorRootKey node complete) := by
  rfl

/-- A successful observed root key retains its provenance node in `sourceNodes`. -/
theorem observedRuleMajorRootKey?_sourceNodes (observe : OfficialCIPNode V → Option Nat)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool)
    (key : OfficialRuleMajorKey V)
    (computed : observedRuleMajorRootKey? observe m node complete = some key) :
    key.sourceNodes = [[([], node)]] := by
  cases obs : observe node with
  | none => simp [observedRuleMajorRootKey?, obs] at computed
  | some scalar =>
      simp [observedRuleMajorRootKey?, obs] at computed
      subst key
      rfl

/-- The root Rule-1b head of a successful observed root key is exactly the scalar returned by the
observer at the root node. -/
theorem observedRuleMajorRootKey?_rule1b_head (observe : OfficialCIPNode V → Option Nat)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool)
    (key : OfficialRuleMajorKey V)
    (computed : observedRuleMajorRootKey? observe m node complete = some key) :
    ∃ scalar, observe node = some scalar ∧ key.rule1b.head? = some [([], scalar)] := by
  cases obs : observe node with
  | none => simp [observedRuleMajorRootKey?, obs] at computed
  | some scalar =>
      simp [observedRuleMajorRootKey?, obs] at computed
      subst key
      exact ⟨scalar, rfl, by simp⟩

/-- A successful observed root key retains its requested completeness flag. -/
theorem observedRuleMajorRootKey?_complete (observe : OfficialCIPNode V → Option Nat)
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool)
    (key : OfficialRuleMajorKey V)
    (computed : observedRuleMajorRootKey? observe m node complete = some key) :
    key.complete = complete := by
  cases obs : observe node with
  | none => simp [observedRuleMajorRootKey?, obs] at computed
  | some scalar =>
      simp [observedRuleMajorRootKey?, obs] at computed
      subst key
      rfl

end MoleculeGraph

namespace CertifiedLocalizedCIPInput

/-! ## The observed cumulative builder -/

/-- Fail-closed cumulative Rules-4a--5 builder over exact reroot cursors, with an independently
chosen Rule-1b observer and an independently chosen auxiliary-label callback.  Everything except
the two observation sources is the production construction: the exact child enumeration, the
cumulative sibling sort, the descriptor/label/ranked-label merges, and the rule-major assembly are
all reused verbatim.  A `none` Rule-1b observation fails the whole build. -/
noncomputable def buildLocalizedObservedCumulativeRule45Key?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option input.LocalizedRerootCumulativeRule45Key
  | 0, cursor => do
      let children ← input.localizedRerootChildren? cursor
      if children = [] then
        let label := read cursor
        let constitutional ← input.moleculeGraph.observedRuleMajorRootKey?
          observe cursor.occurrence.1.node true
        some
          { constitutional := constitutional
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, cursor => do
      let children ← input.localizedRerootChildren? cursor
      let label := read cursor
      if children = [] then
        let constitutional ← input.moleculeGraph.observedRuleMajorRootKey?
          observe cursor.occurrence.1.node true
        some
          { constitutional := constitutional
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        let childKeys ← children.mapM
          (input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel)
        let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
        let constitutional ← input.moleculeGraph.observedRuleMajorRootKey?
          observe cursor.occurrence.1.node false
        some
          { constitutional := OfficialRuleMajorKey.assemble constitutional
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }

/-! ## Generic `mapM` facts -/

/-- Pointwise agreement of two `Option`-valued functions lifts through `List.mapM`. -/
private theorem observed_list_mapM_congr {α β : Type*} {first second : α → Option β}
    (agrees : ∀ value, first value = second value) :
    ∀ values : List α, values.mapM first = values.mapM second
  | [] => rfl
  | value :: values => by
      simp [List.mapM_cons, agrees value, observed_list_mapM_congr agrees values]

/-- Every successful `List.mapM` result element comes from some source element. -/
private theorem observed_list_mapM_member {α β : Type*} (reader : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM reader = some results →
      ∀ result, result ∈ results →
        ∃ value, value ∈ values ∧ reader value = some result
  | [], results, computed, result, present => by
      simp at computed
      subst results
      simp at present
  | value :: values, results, computed, result, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : reader value with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : values.mapM reader with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst results
              rcases List.mem_cons.mp present with same | tailPresent
              · subst result
                exact ⟨value, by simp, headComputed⟩
              · rcases observed_list_mapM_member reader values tail tailComputed
                    result tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem value sourcePresent, sourceComputed⟩

/-- Pointwise existence lifts to a successful `List.mapM`. -/
private theorem observed_mapM_exists {α β : Type*} (build : α → Option β) :
    ∀ values : List α,
      (∀ value, value ∈ values → ∃ result, build value = some result) →
      ∃ results, values.mapM build = some results
  | [], _ => ⟨[], rfl⟩
  | value :: values, allExist => by
      obtain ⟨result, computed⟩ := allExist value (by simp)
      have tailExist : ∀ v, v ∈ values → ∃ r, build v = some r := by
        intro v present
        exact allExist v (List.mem_cons_of_mem value present)
      obtain ⟨results, resultsComputed⟩ := observed_mapM_exists build values tailExist
      refine ⟨result :: results, ?_⟩
      simp [computed, resultsComputed]

/-! ## Structural budget and reached nodes -/

/-- The canonical total zipper expansion chosen from `exists_localizedRerootChildren`. -/
noncomputable def localizedRerootChildrenOf
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (input.LocalizedRerootCursor carrierFuel) :=
  Classical.choose (input.exists_localizedRerootChildren cursor)

/-- `localizedRerootChildrenOf` is exactly a successful `localizedRerootChildren?` expansion. -/
theorem localizedRerootChildrenOf_spec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedRerootChildren? cursor = some (input.localizedRerootChildrenOf cursor) :=
  Classical.choose_spec (input.exists_localizedRerootChildren cursor)

/-- Recursive completeness of the canonical reroot child enumeration within a fuel bound. -/
noncomputable def LocalizedRerootExpansionCompleteWithin
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    Nat → input.LocalizedRerootCursor carrierFuel → Prop
  | 0, cursor => input.localizedRerootChildrenOf cursor = []
  | fuel + 1, cursor =>
      ∀ child, child ∈ input.localizedRerootChildrenOf cursor →
        input.LocalizedRerootExpansionCompleteWithin fuel child

/-- The provenance nodes reached by a budgeted expansion from one cursor. -/
noncomputable def LocalizedRerootReachedNodes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    Nat → input.LocalizedRerootCursor carrierFuel → List (OfficialCIPNode input.Atom)
  | 0, cursor => [cursor.occurrence.1.node]
  | fuel + 1, cursor =>
      cursor.occurrence.1.node ::
        (input.localizedRerootChildrenOf cursor).flatMap
          (fun child => input.LocalizedRerootReachedNodes fuel child)

/-! ## Recovery of the legacy cumulative builder -/

/-- Specializing the observer to `some ∘ rule1bRootDistance` and the label callback to the existing
restricted dependency reader reproduces the existing cumulative builder exactly, for every fuel and
cursor. -/
theorem buildLocalizedObservedCumulativeRule45Key?_eq_legacy
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedObservedCumulativeRule45Key? stage
        (fun node => some node.rule1bRootDistance)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
      input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor
  | 0, cursor => by
      unfold buildLocalizedObservedCumulativeRule45Key?
        buildLocalizedRerootCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · simp [terminal,
              input.moleculeGraph.observedRuleMajorRootKey?_eq_rule1bRootDistance
                cursor.occurrence.1.node true]
          · simp [terminal]
  | fuel + 1, cursor => by
      unfold buildLocalizedObservedCumulativeRule45Key?
        buildLocalizedRerootCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · simp [terminal,
              input.moleculeGraph.observedRuleMajorRootKey?_eq_rule1bRootDistance
                cursor.occurrence.1.node true]
          · have congruence :
                children.mapM (input.buildLocalizedObservedCumulativeRule45Key?
                    stage (fun node => some node.rule1bRootDistance)
                    (fun cursor => input.localizedDependencyLabel target view cursor) fuel) =
                  children.mapM (input.buildLocalizedRerootCumulativeRule45Key?
                    stage target view fuel) :=
              observed_list_mapM_congr
                (fun child =>
                  buildLocalizedObservedCumulativeRule45Key?_eq_legacy
                    input stage target view fuel child)
                children
            simp [terminal, congruence,
              input.moleculeGraph.observedRuleMajorRootKey?_eq_rule1bRootDistance
                cursor.occurrence.1.node false]

/-- Provenance trees are preserved exactly by the legacy specialization: the observed build and the
legacy build carry the same addressed `sourceNodes`. -/
theorem buildLocalizedObservedCumulativeRule45Key?_sourceNodes_eq_legacy
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      (input.buildLocalizedObservedCumulativeRule45Key? stage
        (fun node => some node.rule1bRootDistance)
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor).map
        (fun key => key.constitutional.sourceNodes) =
      (input.buildLocalizedRerootCumulativeRule45Key? stage target view fuel cursor).map
        (fun key => key.constitutional.sourceNodes) := by
  intro fuel cursor
  rw [input.buildLocalizedObservedCumulativeRule45Key?_eq_legacy stage target view fuel cursor]

/-! ## Root head of a successful observed build -/

/-- The root Rule-1b head of any successful observed build is exactly the scalar returned by the
observer at the root node, independently of the label callback and of all deeper observations. -/
theorem buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor = some key →
      ∃ scalar, observe cursor.occurrence.1.node = some scalar ∧
        key.constitutional.rule1b.head? = some [([], scalar)]
  | 0, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none => simp [rootComputed] at computed
            | some constitutional =>
                simp [rootComputed] at computed
                subst key
                rcases input.moleculeGraph.observedRuleMajorRootKey?_rule1b_head
                    observe cursor.occurrence.1.node true constitutional rootComputed with
                  ⟨scalar, observedScalar, rule1bHead⟩
                exact ⟨scalar, observedScalar, by simpa using rule1bHead⟩
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none => simp [rootComputed] at computed
            | some constitutional =>
                simp [rootComputed] at computed
                subst key
                rcases input.moleculeGraph.observedRuleMajorRootKey?_rule1b_head
                    observe cursor.occurrence.1.node true constitutional rootComputed with
                  ⟨scalar, observedScalar, rule1bHead⟩
                exact ⟨scalar, observedScalar, by simpa using rule1bHead⟩
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                    observe cursor.occurrence.1.node false with
                | none =>
                    simp [childrenComputed, terminal, rootComputed] at computed
                | some constitutional =>
                    simp [childrenComputed, terminal, childKeysComputed, rootComputed] at computed
                    subst key
                    rcases input.moleculeGraph.observedRuleMajorRootKey?_rule1b_head
                        observe cursor.occurrence.1.node false constitutional rootComputed with
                      ⟨scalar, observedScalar, rule1bHead⟩
                    refine ⟨scalar, observedScalar, ?_⟩
                    unfold OfficialRuleMajorKey.assemble
                    rcases List.head?_eq_some_iff.mp rule1bHead with
                      ⟨rule1bRest, rule1bEq⟩
                    rw [rule1bEq]
                    simp

/-! ## Constitutional completeness -/

/-- The constitutional projection of a successful observed build is complete, whatever the observer
and label callback are. -/
theorem buildLocalizedObservedCumulativeRule45Key?_constitutional_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor = some key →
      key.constitutional.complete = true
  | 0, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none => simp [rootComputed] at computed
            | some constitutional =>
                simp [rootComputed] at computed
                subst key
                simpa using
                  (input.moleculeGraph.observedRuleMajorRootKey?_complete
                    observe cursor.occurrence.1.node true constitutional rootComputed)
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none => simp [rootComputed] at computed
            | some constitutional =>
                simp [rootComputed] at computed
                subst key
                simpa using
                  (input.moleculeGraph.observedRuleMajorRootKey?_complete
                    observe cursor.occurrence.1.node true constitutional rootComputed)
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                    observe cursor.occurrence.1.node false with
                | none =>
                    simp [childrenComputed, terminal, rootComputed] at computed
                | some constitutional =>
                    simp [childrenComputed, terminal, childKeysComputed, rootComputed] at computed
                    subst key
                    unfold OfficialRuleMajorKey.assemble
                    rw [List.all_eq_true]
                    intro child childPresent
                    rw [List.mem_map] at childPresent
                    rcases childPresent with ⟨childKey, childSortedPresent, rfl⟩
                    have childSourcePresent : childKey ∈ childKeys :=
                      (input.sortLocalizedRerootCumulativeRule45Keys_perm
                        childKeys).mem_iff.mp childSortedPresent
                    rcases observed_list_mapM_member
                        (input.buildLocalizedObservedCumulativeRule45Key?
                          stage observe read fuel)
                        children childKeys childKeysComputed childKey childSourcePresent with
                      ⟨childCursor, _cursorPresent, childComputed⟩
                    exact input.buildLocalizedObservedCumulativeRule45Key?_constitutional_complete
                      stage observe read fuel childCursor childKey childComputed

/-! ## Finite-budget availability -/

/-- If the actual structural reroot expansion is complete within the stated fuel and the observer
is available at every reached provenance node, the observed builder returns a key.  This is the
finite-budget availability theorem: no key existence or comparator outcome is assumed. -/
theorem buildLocalizedObservedCumulativeRule45Key?_exists_of_available
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootExpansionCompleteWithin fuel cursor →
      (∀ node, node ∈ input.LocalizedRerootReachedNodes fuel cursor →
        (observe node).isSome = true) →
      ∃ key,
        input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor = some key
  | 0, cursor, complete, available => by
      change input.localizedRerootChildrenOf cursor = [] at complete
      have childrenComputed : input.localizedRerootChildren? cursor =
          some (input.localizedRerootChildrenOf cursor) :=
        input.localizedRerootChildrenOf_spec cursor
      have nodeAvailable : (observe cursor.occurrence.1.node).isSome = true :=
        available cursor.occurrence.1.node (by simp [LocalizedRerootReachedNodes])
      cases obs : observe cursor.occurrence.1.node with
      | none => simp [obs] at nodeAvailable
      | some scalar =>
          refine ⟨
            { constitutional := input.moleculeGraph.officialRuleMajorRootKeyWith
                (fun _ => scalar) cursor.occurrence.1.node true
              descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]]
              labels := [[([], read cursor)]]
              rankedLabels := [[([], read cursor)]] }, ?_⟩
          simp [buildLocalizedObservedCumulativeRule45Key?, MoleculeGraph.observedRuleMajorRootKey?,
            childrenComputed, complete, obs]
  | fuel + 1, cursor, complete, available => by
      change (∀ child, child ∈ input.localizedRerootChildrenOf cursor →
        input.LocalizedRerootExpansionCompleteWithin fuel child) at complete
      have childrenComputed : input.localizedRerootChildren? cursor =
          some (input.localizedRerootChildrenOf cursor) :=
        input.localizedRerootChildrenOf_spec cursor
      have nodeAvailable : (observe cursor.occurrence.1.node).isSome = true :=
        available cursor.occurrence.1.node (by simp [LocalizedRerootReachedNodes])
      cases obs : observe cursor.occurrence.1.node with
      | none => simp [obs] at nodeAvailable
      | some scalar =>
          by_cases terminal : input.localizedRerootChildrenOf cursor = []
          · refine ⟨
              { constitutional := input.moleculeGraph.officialRuleMajorRootKeyWith
                  (fun _ => scalar) cursor.occurrence.1.node true
                descriptor := [[([], localizedCumulativeRule45Priority stage (read cursor))]]
                labels := [[([], read cursor)]]
                rankedLabels := [[([], read cursor)]] }, ?_⟩
            simp [buildLocalizedObservedCumulativeRule45Key?, MoleculeGraph.observedRuleMajorRootKey?,
              childrenComputed, terminal, obs]
          · have childrenComplete : ∀ child,
                child ∈ input.localizedRerootChildrenOf cursor →
                input.LocalizedRerootExpansionCompleteWithin fuel child :=
              complete
            have childrenAvailable : ∀ child,
                child ∈ input.localizedRerootChildrenOf cursor →
                ∀ node, node ∈ input.LocalizedRerootReachedNodes fuel child →
                  (observe node).isSome = true := by
              intro child childPresent node nodePresent
              exact available node (by
                simp [LocalizedRerootReachedNodes, List.mem_flatMap]
                right
                exact ⟨child, childPresent, nodePresent⟩)
            have childrenBuild : ∀ child,
                child ∈ input.localizedRerootChildrenOf cursor →
                ∃ key, input.buildLocalizedObservedCumulativeRule45Key?
                  stage observe read fuel child = some key := by
              intro child childPresent
              exact buildLocalizedObservedCumulativeRule45Key?_exists_of_available
                input stage observe read fuel child
                (childrenComplete child childPresent)
                (childrenAvailable child childPresent)
            obtain ⟨childKeys, childKeysComputed⟩ :=
              observed_mapM_exists (input.buildLocalizedObservedCumulativeRule45Key?
                stage observe read fuel) (input.localizedRerootChildrenOf cursor) childrenBuild
            refine ⟨
              { constitutional := OfficialRuleMajorKey.assemble
                  (input.moleculeGraph.officialRuleMajorRootKeyWith
                    (fun _ => scalar) cursor.occurrence.1.node false)
                  ((input.sortLocalizedRerootCumulativeRule45Keys childKeys).map
                    fun child => child.constitutional)
                descriptor :=
                  [[([], localizedCumulativeRule45Priority stage (read cursor))]] ++
                    input.mergeLocalizedRerootDescriptorChildren
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                labels := [[([], read cursor)]] ++
                  input.mergeLocalizedRerootLabelChildren
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                rankedLabels := [[([], read cursor)]] ++
                  input.mergeLocalizedRerootRankedLabelChildren
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys) }, ?_⟩
            simp [buildLocalizedObservedCumulativeRule45Key?, MoleculeGraph.observedRuleMajorRootKey?,
              childrenComputed, terminal, obs, childKeysComputed]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the observed root helper, the observed cumulative builder, and their
public recovery/coherence theorems.  `assert_kernel_only` permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and native/compiler
trust. -/

assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.observedRuleMajorRootKey?
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.observedRuleMajorRootKey?_eq_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.observedRuleMajorRootKey?_sourceNodes
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.observedRuleMajorRootKey?_rule1b_head
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.observedRuleMajorRootKey?_complete
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildrenOf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootChildrenOf_spec
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootExpansionCompleteWithin
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootReachedNodes
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_eq_legacy
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_sourceNodes_eq_legacy
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1b_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_constitutional_complete
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_exists_of_available
