import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Parametric label reading for source-canonical cumulative Rules-4a--5 keys

`AuthoritativeSemanticMancudeOccurrenceRule45Key` compiles cumulative Rules-4a--5 keys on the
source-canonical occurrence zipper, but every node label is read through one restricted
dependency view (`aromaticCanonicalDependencyLabel target view`).  As in the localized
occurrence compiler, that makes it impossible to compare the *same* key construction driven by a
different label source.

This module separates label reading from key construction.
`buildAromaticCanonicalCumulativeRule45KeyWithRead?` takes an arbitrary total callback

`read : cursor → Option LocalizedAuxiliaryLabel`

and otherwise performs exactly the production construction: it reuses the actual public
`aromaticCanonicalRerootChildren?` frame reader, the actual cumulative sibling sort
`sortAromaticCanonicalCumulativeRule45Keys`, the actual descriptor/label/ranked-label merges, the
actual exact `MoleculeGraph.exactOfficialRuleMajorRootKey` root projections, the actual
`ExactOfficialRuleMajorKey.assemble` branching, and the same public
`AromaticCanonicalCumulativeRule45Key` key type (including its exact `sourceNodes` and
`semanticExactOfficialRule1aObservation` observer).  Only the label observation is supplied by
`read`.

## Main results

* `buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel` —
  specializing the callback to the existing `aromaticCanonicalDependencyLabel target view`
  reproduces the existing `buildAromaticCanonicalCumulativeRule45Key?` *exactly*, for every fuel
  and every cursor, with no hypotheses (proved by induction on the fuel and the actual
  `List.mapM` recursion, with no assumed equality).
* `buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr` — pointwise-equal readers build
  pointwise-equal whole `Option` keys at every fuel and cursor.
* `buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr_of_reachable` — readers that agree on
  every cursor reachable by the actual recursive reroot edge from a start cursor build the *same
  full* `Option` key at every reachable cursor and fuel.
* `buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_of_readerAgree` — the same agreement
  composed with the unconditional specialization identifies a parametric build with the shipped
  one, and `..._wholeState_eq_of_readerAgree` instantiates it to a whole-state reader.
* `..._key_eq_of_readerAgree` and `..._rankedLabels_eq_of_readerAgree` — successful builds yield
  the *same* key (hence the same ranked labels, so the Rule-4b reference population is unchanged),
  including the fail-closed `none` outcome being equal on both sides.
* `buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutional_complete` and
  `..._successful_shape` — every successful parametric compilation has a complete constitutional
  projection, a `sourceNodes` head equal to the cursor node, and first descriptor/label/ranked
  layers equal to the cursor reading.
* `buildAromaticCanonicalCumulativeRule45KeyWithRead?_sound` — every successful parametric build
  satisfies an independent declarative recursive semantics parameterized by the reader.

## Scope

The callback is a total function into `Option LocalizedAuxiliaryLabel`.  The value `none` is the
structural "no label observation at this cursor" value that the cumulative priority vectors
already consume; it is *not* identified with, and carries no claim about, any unavailable physical
input or any particular chemical configuration.  This module proves structural mathematics only.
It does not add a solver, an evaluator or a production path, and every result preserves the exact
`Option`/refusal behaviour of the existing builder.
-/

/-! ## The parametric builder -/

/-- Label-callback form of the source-canonical cumulative Rules-4a--5 builder.  `read` is total;
`none` is the structural absence of a label observation, exactly as consumed by the cumulative
priority vectors.  Everything except the label source is the production construction. -/
noncomputable def buildAromaticCanonicalCumulativeRule45KeyWithRead?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      Option source.AromaticCanonicalCumulativeRule45Key
  | 0, cursor => do
      let children ← source.aromaticCanonicalRerootChildren? cursor
      if children = [] then
        let label := read cursor
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, cursor => do
      let children ← source.aromaticCanonicalRerootChildren? cursor
      let label := read cursor
      if children = [] then
        some
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        let childKeys ← children.mapM
          (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
            stage read fuel)
        let compare := source.compareAromaticCanonicalCumulativeRule45Keys
        let sorted := sortAromaticCanonicalCumulativeRule45Keys compare childKeys
        some
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor :=
              [[([], localizedCumulativeRule45Priority stage label)]] ++
                mergeAromaticCanonicalDescriptorChildren sorted
            labels := [[([], label)]] ++ mergeAromaticCanonicalLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              mergeAromaticCanonicalRankedLabelChildren compare sorted }

/-! ## Generic `mapM` facts -/

/-- Pointwise agreement of two `Option`-valued functions lifts through `List.mapM`. -/
private theorem list_mapM_congr {α β : Type*} {first second : α → Option β}
    (agrees : ∀ value, first value = second value) :
    ∀ values : List α, values.mapM first = values.mapM second
  | [] => rfl
  | value :: values => by
      simp [List.mapM_cons, agrees value, list_mapM_congr agrees values]

/-- Pointwise agreement on the members of a list lifts through `List.mapM`.  Membership is enough
because `mapM` only applies the reader to list members. -/
private theorem list_mapM_congr_on {α β : Type*} (first second : α → Option β) :
    ∀ values : List α,
      (∀ value, value ∈ values → first value = second value) →
      values.mapM first = values.mapM second
  | [], _ => rfl
  | value :: values, agrees => by
      simp [List.mapM_cons, agrees value (by simp),
        list_mapM_congr_on first second values
          (fun member memberPresent => agrees member (by simp [memberPresent]))]

/-- Every successful `List.mapM` result element comes from some source element. -/
private theorem list_mapM_member {α β : Type*} (reader : α → Option β) :
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
              · rcases list_mapM_member reader values tail tailComputed result tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem value sourcePresent, sourceComputed⟩

/-! ## Recovery of the production builder -/

/-- Specializing the callback to the existing restricted dependency reader reproduces the
existing cumulative builder exactly, for every fuel and cursor.  This is unconditional: no
hypothesis about any compiled key is used. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor) fuel cursor =
      source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor
  | 0, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
        buildAromaticCanonicalCumulativeRule45Key?
      cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · simp [terminal]
          · simp [terminal]
  | fuel + 1, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
        buildAromaticCanonicalCumulativeRule45Key?
      cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · simp [terminal]
          · have congruence :
                children.mapM (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                    stage (fun cursor =>
                      source.aromaticCanonicalDependencyLabel target view cursor) fuel) =
                  children.mapM (source.buildAromaticCanonicalCumulativeRule45Key?
                    stage target view fuel) :=
              list_mapM_congr
                (fun child =>
                  buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
                    source stage target view fuel child)
                children
            simp [terminal, congruence]

/-! ## Congruence under reader agreement -/

/-- Pointwise-equal readers build pointwise-equal whole `Option` keys at every fuel and cursor.
No key equality is assumed: the proof is the actual structural recursion on fuel and the actual
`List.mapM` over executable children. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (agree : ∀ cursor : source.AromaticCanonicalRerootCursor carrierFuel,
      first cursor = second cursor) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage first fuel cursor =
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage second fuel cursor
  | 0, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor
            simp [terminal, cursorAgree]
          · simp [terminal]
  | fuel + 1, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor
            simp [terminal, cursorAgree]
          · have mapCongr : children.mapM
                  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                    stage first fuel) =
                children.mapM
                  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                    stage second fuel) :=
              list_mapM_congr
                (fun child =>
                  buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr
                    source stage first second agree fuel child)
                children
            have cursorAgree := agree cursor
            simp [terminal, cursorAgree, mapCongr]

/-- The actual recursive reroot edge: `child` is an executable child of `cursor` on the public
source-canonical zipper. -/
def aromaticCanonicalRerootEdge (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor child : source.AromaticCanonicalRerootCursor fuel) : Prop :=
  child ∈ source.aromaticCanonicalRerootChildren cursor

/-- The public optional children reader is definitionally the executable expansion. -/
theorem aromaticCanonicalRerootChildren?_eq_some
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    source.aromaticCanonicalRerootChildren? cursor =
      some (source.aromaticCanonicalRerootChildren cursor) :=
  rfl

/-- Readers that agree on every cursor reachable from a start cursor by the actual recursive
reroot edge build the same whole `Option` key at every reachable cursor and fuel.  The proof
recurses on the actual structural fuel and on the actual `List.mapM` over executable children; it
never assumes equality of the built keys. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr_of_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : ∀ cursor : source.AromaticCanonicalRerootCursor carrierFuel,
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
        first cursor = second cursor) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage first fuel cursor =
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage second fuel cursor
  | 0, cursor, reach => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree]
          · simp [terminal]
  | fuel + 1, cursor, reach => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      cases childrenComputed : source.aromaticCanonicalRerootChildren? cursor with
      | none => simp
      | some children =>
          by_cases terminal : children = []
          · have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree]
          · have childrenEq : children = source.aromaticCanonicalRerootChildren cursor := by
              rw [aromaticCanonicalRerootChildren?_eq_some] at childrenComputed
              exact (Option.some.inj childrenComputed).symm
            have mapCongr : children.mapM
                  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                    stage first fuel) =
                children.mapM
                  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                    stage second fuel) := by
              refine list_mapM_congr_on
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage first fuel)
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage second fuel)
                children ?_
              intro child childPresent
              have childEdge : aromaticCanonicalRerootEdge source cursor child := by
                unfold aromaticCanonicalRerootEdge
                rwa [← childrenEq]
              have childReach :
                  Relation.ReflTransGen (aromaticCanonicalRerootEdge source) cursor child :=
                Relation.ReflTransGen.single childEdge
              exact buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr_of_reachable
                source stage first second start agree fuel child (reach.trans childReach)
            have cursorAgree := agree cursor reach
            simp [terminal, cursorAgree, mapCongr]

/-! ## Agreement with the shipped restricted builder -/

/-- If an arbitrary reader agrees with the restricted dependency reader on every cursor reachable
from a start cursor, the parametric build equals the shipped `buildAromaticCanonicalCumulativeRule45Key?`
at every reachable cursor and every fuel — as a whole `Option`, so the fail-closed `none`
outcome is equal too.  No hypothesis about any compiled key is used. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_of_readerAgree
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : ∀ cursor : source.AromaticCanonicalRerootCursor carrierFuel,
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
        read cursor = source.aromaticCanonicalDependencyLabel target view cursor) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read fuel cursor =
      source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor := by
  intro fuel cursor reach
  calc
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read fuel cursor =
        source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
          (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
          fuel cursor :=
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr_of_reachable
        stage read
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        start agree fuel cursor reach
    _ = source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor :=
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
        stage target view fuel cursor

/-- Whole-state instantiation: a whole-state reader that agrees with the restricted dependency
reader at every reachable cursor drives exactly the shipped builder. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_readerAgree
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : ∀ cursor : source.AromaticCanonicalRerootCursor carrierFuel,
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
        state cursor.occurrence =
          source.aromaticCanonicalDependencyLabel target view cursor) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
        (fun cursor => state cursor.occurrence) fuel cursor =
      source.buildAromaticCanonicalCumulativeRule45Key? stage target view fuel cursor :=
  source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_of_readerAgree
    stage target view (fun cursor => state cursor.occurrence) start agree

/-- Successful parametric and shipped compilations under reader agreement yield the *same* key,
not merely comparable projections. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_key_eq_of_readerAgree
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : ∀ cursor : source.AromaticCanonicalRerootCursor carrierFuel,
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
        read cursor = source.aromaticCanonicalDependencyLabel target view cursor)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reach : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor)
    (parametricKey shippedKey : source.AromaticCanonicalCumulativeRule45Key)
    (parametricComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage read fuel cursor = some parametricKey)
    (shippedComputed : source.buildAromaticCanonicalCumulativeRule45Key?
      stage target view fuel cursor = some shippedKey) :
    parametricKey = shippedKey := by
  have total := source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_of_readerAgree
    stage target view read start agree fuel cursor reach
  rw [parametricComputed, shippedComputed] at total
  exact Option.some.inj total

/-- Under reader agreement the successful parametric ranked labels are exactly the shipped ranked
labels, so the Rule-4b reference population is exactly the shipped one. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_rankedLabels_eq_of_readerAgree
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (start : source.AromaticCanonicalRerootCursor carrierFuel)
    (agree : ∀ cursor : source.AromaticCanonicalRerootCursor carrierFuel,
      Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor →
        state cursor.occurrence =
          source.aromaticCanonicalDependencyLabel target view cursor)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reach : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) start cursor)
    (parametricKey shippedKey : source.AromaticCanonicalCumulativeRule45Key)
    (parametricComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage (fun cursor => state cursor.occurrence) fuel cursor = some parametricKey)
    (shippedComputed : source.buildAromaticCanonicalCumulativeRule45Key?
      stage target view fuel cursor = some shippedKey) :
    parametricKey.rankedLabels = shippedKey.rankedLabels := by
  have total := source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_readerAgree
    stage target view state start agree fuel cursor reach
  rw [parametricComputed, shippedComputed] at total
  have keyEq : parametricKey = shippedKey := Option.some.inj total
  subst shippedKey
  rfl

/-! ## Completeness and successful shape -/

/-- Every successful parametric child list consists of keys whose constitutional projections are
complete. -/
private theorem mapM_buildWithRead?_constitutional_complete
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (complete : ∀ (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalCumulativeRule45Key),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel cursor = some key →
      key.constitutional.complete = true) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalCumulativeRule45Key),
      cursors.mapM (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel) = some keys →
      ∀ key, key ∈ keys → key.constitutional.complete = true
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          stage read fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                stage read fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with same | tailPresent
              · subst key
                exact complete cursor head headComputed
              · exact mapM_buildWithRead?_constitutional_complete
                  source stage read complete cursors tail tailComputed key tailPresent

/-- The constitutional projection of a successful parametric compilation is complete, whatever
the label callback is. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutional_complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalCumulativeRule45Key),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read fuel cursor =
        some key →
      key.constitutional.complete = true
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        rfl
      · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        rfl
      · cases childKeysComputed : children.mapM
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              stage read fuel) with
        | none => simp [children, terminal, childKeysComputed] at computed
        | some childKeys =>
            simp [children, terminal, childKeysComputed] at computed
            subst key
            unfold ExactOfficialRuleMajorKey.assemble
            rw [List.all_eq_true]
            intro childComplete childPresent
            rw [List.mem_map] at childPresent
            rcases childPresent with ⟨childKey, childSortedPresent, rfl⟩
            have childSourcePresent : childKey ∈ childKeys :=
              (source.sortAromaticCanonicalCumulativeRule45Keys_perm
                source.compareAromaticCanonicalCumulativeRule45Keys
                childKeys).mem_iff.mp childSortedPresent
            rcases list_mapM_member
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  stage read fuel) children childKeys childKeysComputed
                childKey childSourcePresent with
              ⟨childCursor, _childPresent, childComputed⟩
            exact buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutional_complete
              source stage read fuel childCursor childKey childComputed

/-- Every successful parametric compilation has the exact public source shape: a `sourceNodes`
head equal to the cursor node, and first descriptor/label/ranked layers equal to the cursor
reading.  These are the projections the observable layer inspects; no label equality is assumed
beyond the reader's own value. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalCumulativeRule45Key),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read fuel cursor =
        some key →
      key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] ∧
      key.descriptor.head? =
        some [([], localizedCumulativeRule45Priority stage (read cursor))] ∧
      key.labels.head? = some [([], read cursor)] ∧
      key.rankedLabels.head? = some [([], read cursor)]
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        simp [MoleculeGraph.exactOfficialRuleMajorRootKey]
      · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        simp [MoleculeGraph.exactOfficialRuleMajorRootKey]
      · cases childKeysComputed : children.mapM
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              stage read fuel) with
        | none => simp [children, terminal, childKeysComputed] at computed
        | some childKeys =>
            simp [children, terminal, childKeysComputed] at computed
            subst key
            simp [ExactOfficialRuleMajorKey.assemble,
              MoleculeGraph.exactOfficialRuleMajorRootKey]

/-! ## Independent declarative semantics -/

/- Independent recursive semantics of parametric canonical cumulative Rules-4a--5 keys and
aligned child lists.  The topology is the declarative zipper frame, the sibling order is the
ordinary permutation/descending pair under the exact public comparator, and the observed label at
each cursor is exactly the reader's value. -/
mutual

inductive DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    Nat → source.AromaticCanonicalRerootCursor carrierFuel →
      source.AromaticCanonicalCumulativeRule45Key → Prop
  | zeroLeaf {cursor children label}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : read cursor = label) :
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead source stage read 0 cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
          labels := [[([], label)]]
          rankedLabels := [[([], label)]] }
  | successorLeaf {fuel cursor children label}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (terminal : children = [])
      (observed : read cursor = label) :
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead source stage read
        (fuel + 1) cursor
        { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
            cursor.occurrence.1.node true
          descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
          labels := [[([], label)]]
          rankedLabels := [[([], label)]] }
  | successorBranch {fuel cursor children label childKeys sorted}
      (frame : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
      (nonterminal : children ≠ [])
      (observed : read cursor = label)
      (childDerivations : DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList
        source stage read fuel children childKeys)
      (permutation : sorted.Perm childKeys)
      (descending : AromaticCanonicalCumulativeRule45KeysDescending
        source.compareAromaticCanonicalCumulativeRule45Keys sorted) :
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead source stage read
        (fuel + 1) cursor
        { constitutional := ExactOfficialRuleMajorKey.assemble
            (MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node false)
            (sorted.map fun child => child.constitutional)
          descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
            mergeAromaticCanonicalDescriptorChildren sorted
          labels := [[([], label)]] ++ mergeAromaticCanonicalLabelChildren sorted
          rankedLabels := [[([], label)]] ++
            mergeAromaticCanonicalRankedLabelChildren
              source.compareAromaticCanonicalCumulativeRule45Keys sorted }

inductive DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    Nat → List (source.AromaticCanonicalRerootCursor carrierFuel) →
      List source.AromaticCanonicalCumulativeRule45Key → Prop
  | nil (fuel) :
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList
        source stage read fuel [] []
  | cons {fuel cursor cursors key keys}
      (head : DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead
        source stage read fuel cursor key)
      (tail : DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList
        source stage read fuel cursors keys) :
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList
        source stage read fuel (cursor :: cursors) (key :: keys)

end

/-- Aligned child lists of successful parametric builds satisfy the independent declarative
recursion. -/
private theorem mapM_buildWithRead?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (sound : ∀ (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalCumulativeRule45Key),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel cursor = some key →
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead
        source stage read fuel cursor key) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalCumulativeRule45Key),
      cursors.mapM (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel) = some keys →
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList
        source stage read fuel cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList.nil fuel
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          stage read fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                stage read fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList.cons
                (sound cursor head headComputed)
                (mapM_buildWithRead?_sound
                  source stage read sound cursors tail tailComputed)

/-- Every successful parametric cumulative key satisfies the independent recursive topology,
label, permutation and descending-order semantics. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
      (key : source.AromaticCanonicalCumulativeRule45Key),
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage read fuel cursor =
        some key →
      DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead
        source stage read fuel cursor key
  | 0, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        exact DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead.zeroLeaf
          (source.aromaticCanonicalRerootChildren_sound cursor) terminal rfl
      · simp [children, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead? at computed
      simp only [aromaticCanonicalRerootChildren?] at computed
      let children := source.aromaticCanonicalRerootChildren cursor
      let label := read cursor
      by_cases terminal : children = []
      · simp [children, terminal] at computed
        subst key
        exact DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead.successorLeaf
          (source.aromaticCanonicalRerootChildren_sound cursor) terminal rfl
      · cases childKeysComputed : children.mapM
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              stage read fuel) with
        | none => simp [children, terminal, childKeysComputed] at computed
        | some childKeys =>
            let compare := source.compareAromaticCanonicalCumulativeRule45Keys
            let sorted := sortAromaticCanonicalCumulativeRule45Keys compare childKeys
            simp [children, terminal, childKeysComputed] at computed
            subst key
            letI : Std.TransCmp compare :=
              source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
            exact DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead.successorBranch
              (source.aromaticCanonicalRerootChildren_sound cursor) terminal rfl
              (mapM_buildWithRead?_sound
                source stage read
                (buildAromaticCanonicalCumulativeRule45KeyWithRead?_sound
                  source stage read fuel)
                children childKeys childKeysComputed)
              (sortAromaticCanonicalCumulativeRule45Keys_perm compare childKeys)
              (sortAromaticCanonicalCumulativeRule45Keys_descending compare childKeys)

end AuthoritativeChemicalInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRerootEdge
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRerootChildren?_eq_some
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr_of_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_of_readerAgree
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_readerAgree
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_key_eq_of_readerAgree
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_rankedLabels_eq_of_readerAgree
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutional_complete
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.DeclarativeAromaticCanonicalCumulativeRule45KeyWithRead
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.DeclarativeAromaticCanonicalCumulativeRule45KeyWithReadList
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_sound
