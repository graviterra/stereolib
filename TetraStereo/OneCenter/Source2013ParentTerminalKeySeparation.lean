/-
  Source2013ParentTerminalKeySeparation

  Constitutional comparison of an actually-built terminal key against an actually-built
  nonterminal key under the 2013 duplicate-only observer
  (`Rule1bSourceProfileCompiler.sourceObservation2013`).

  ## The point

  `Source2013AuxiliaryDependencyRoute` shows that a backward multiple-bond copy of the parent
  atom and the real parent node *tie* under `sourceObservation2013`.  The stored 2018 observation
  separates them; the 2013 observation does not.  That tie concerns Rule 1b only.

  This module proves the comparison-theoretic insulation that survives the tie, using the
  fail-closed observed cumulative builder `buildLocalizedObservedCumulativeRule45Key?` with
  observer `fun node => some (sourceObservation2013 node)` and an arbitrary auxiliary-label
  reader.  It does not construct the chemical parent/duplicate cursor pair; that actual case is
  the sibling `f90_source2013_parent_extra_child` construction.  Everything below is stated for
  actual cursors and actual builder successes, so the sibling data can feed directly into it.

  The decisive fact is purely structural.  A successful terminal build has exactly one Rule-1a
  sphere.  A successful nonterminal build has its root sphere followed by the merge of the
  nonempty sorted child spheres.  `OfficialRuleMajorKey.compareSparseLayers` is ordinary
  `List.compareLex` over spheres: no zero padding is inserted.  After the two root spheres
  compare equal, the nonempty merged tail is compared with `[]`, which is strictly `gt`.  The
  direction therefore does not depend on the observer, on the label reader, on the sibling order
  produced by the label-dependent sort, or on atomic positivity.  Rule 1a then decides the whole
  constitutional key via `compare_eq_rule1a_of_decisive`, and the cumulative comparator is the
  constitutional one via `compareCumulative_eq_constitutional_of_constitutional_ne_eq`; Rule 1b,
  where the 2013 tie lives, is never consulted.

  ## Main results

  * `buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1a_head` — every successful
    observed build starts its Rule-1a projection with the cursor node's atomic number.  This is
    independent of the observer, the label reader and the child ordering.
  * `buildLocalizedObservedCumulativeRule45Key?_terminal_constitutional_rule1a` — a successful
    build at a cursor with no actual children has the singleton Rule-1a projection
    `[[([], z)]]`.
  * `buildLocalizedObservedCumulativeRule45Key?_nonempty_decomposition` — a successful build at a
    cursor with actual children decomposes its Rule-1a projection as the root sphere followed by
    the merge of the sorted child constitutional Rule-1a spheres.  No key, sorting outcome or
    comparison is assumed; the sorted list is nonempty and every member is an actual child build.
  * `buildLocalizedObservedCumulativeRule45Key?_terminal_nonempty_rule1a_gt` — a terminal right
    key and a nonterminal left key with equal root atomic numbers compare strictly at Rule 1a.
    The terminal side has exactly one sphere, the nonterminal side has a nonempty merged tail,
    and ordinary `List.compareLex` returns `gt`.  This is a consequence of the actual builds
    alone, whatever order the labels induce among the children.
  * `source2013_terminalRight_nonemptyLeft_separation` — at fuel `2 * (carrierFuel + 1)`, with
    observer `some ∘ sourceObservation2013` and an arbitrary reader, both keys exist and the
    Rule-1a comparison is `gt`; consequently the constitutional comparator is `gt` *without
    consulting Rule 1b or Rule 2*, and the cumulative comparator is the constitutional one.
  * `source2013_terminalRight_nonemptyLeft_separation_despite_rootTie` — the same conclusion under
    the explicit hypothesis that the two root Rule-1b observations tie, together with the fact
    that both Rule-1b first spheres carry exactly those tied 2013 observations.

  ## Honesty

  * The `realAtom` branch of `sourceObservation2013` is the comparison-totality convention
    documented in `SourceProfileRule1bCompiler`; it is not a normative 2013 clause about real
    nodes.  Nothing here claims that the 2013 duplicate-only rule justifies real-node ranking, nor
    that the numerical observation is a normative chemical semantics.
  * Full 2013 mixed real/duplicate applicability remains separate.  The results below are
    structural facts about the existing observed compiler and its comparator; the chemical
    parent/terminal case, including the extra positive-copy sibling supplied by
    `parent.remaining = target.remaining + 1`, is supplied, not proved, by the sibling
    construction.
  * No second solver, no assumed key inequality and no assumed strict comparison is introduced.
    The strict `Ordering.gt` is computed from the actual `List.compareLex` equations.
-/

import TetraStereo.OneCenter.LocalizedObservedCumulativeAvailability
import TetraStereo.OneCenter.Source2013AuxiliaryDependencyRoute
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

open Rule1bSourceProfileCompiler

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Rule-1a shape of the observed root key -/

namespace MoleculeGraph

/-- The observed root key produced by a successful observation has the singleton Rule-1a
projection of the observed node. -/
theorem observedRuleMajorRootKey?_rule1a_eq_singleton
    (observe : OfficialCIPNode V → Option Nat) (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) (key : OfficialRuleMajorKey V)
    (computed : m.observedRuleMajorRootKey? observe node complete = some key) :
    key.rule1a = [[([], (ofLex (m.officialNodeAtomLabel node)).1)]] := by
  cases obs : observe node with
  | none => simp [observedRuleMajorRootKey?, obs] at computed
  | some scalar =>
      simp [observedRuleMajorRootKey?, obs] at computed
      subst key
      simp [officialRuleMajorRootKeyWith]

/-- The observed root key produced by a successful observation has the observed node's atomic
number as its first Rule-1a sphere and first parent address. -/
theorem observedRuleMajorRootKey?_rule1a_head
    (observe : OfficialCIPNode V → Option Nat) (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) (key : OfficialRuleMajorKey V)
    (computed : m.observedRuleMajorRootKey? observe node complete = some key) :
    key.rule1a.head? = some [([], (ofLex (m.officialNodeAtomLabel node)).1)] := by
  rw [observedRuleMajorRootKey?_rule1a_eq_singleton observe m node complete key computed]
  rfl

end MoleculeGraph

namespace Source2013ParentTerminalKeySeparation

/-- Assembling a singleton observed root key with child keys prepends exactly the root Rule-1a
sphere and then the merged child Rule-1a spheres. -/
private theorem assemble_rootKey_rule1a
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool)
    (scalar : Nat) (children : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble
        (m.officialRuleMajorRootKeyWith (fun _ => scalar) node complete) children).rule1a =
      [([], (ofLex (m.officialNodeAtomLabel node)).1)] ::
        OfficialRuleMajorKey.mergeChildren children OfficialRuleMajorKey.rule1a := by
  simp [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKeyWith]

/-- Input-to-output membership through a successful `List.mapM`. -/
private theorem mapM_exists_of_mem {α β : Type*} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ∀ x, x ∈ xs → ∃ y, y ∈ ys ∧ f x = some y
  | [], ys, computed, x, present => by
      simp at computed
      subst ys
      simp at present
  | a :: as, ys, computed, x, present => by
      simp only [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : as.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst ys
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨head, by simp, headComputed⟩
              · obtain ⟨y, yMem, yComputed⟩ :=
                  mapM_exists_of_mem f tailComputed x tailPresent
                exact ⟨y, List.mem_cons_of_mem head yMem, yComputed⟩

/-- Output-to-input membership through a successful `List.mapM`. -/
private theorem mapM_mem_of_exists {α β : Type*} (f : α → Option β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      ∀ y, y ∈ ys → ∃ x, x ∈ xs ∧ f x = some y
  | [], ys, computed, y, present => by
      simp at computed
      subst ys
      simp at present
  | a :: as, ys, computed, y, present => by
      simp only [List.mapM_cons] at computed
      cases headComputed : f a with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : as.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst ys
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨a, by simp, headComputed⟩
              · obtain ⟨x, xMem, xComputed⟩ :=
                  mapM_mem_of_exists f tailComputed y tailPresent
                exact ⟨x, List.mem_cons_of_mem a xMem, xComputed⟩

/-- A `foldl` of `max` never drops below its initial value. -/
private theorem le_foldl_max {α : Type*} (f : α → Nat) :
    ∀ (xs : List α) (init : Nat),
      init ≤ xs.foldl (fun longest x => max longest (f x)) init
  | [], init => Nat.le_refl init
  | x :: xs, init => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left _ _)
        (le_foldl_max f xs (max init (f x)))

/-- A `foldl` of `max` is at least the value of every member, regardless of the initial value. -/
private theorem f_le_foldl_max {α : Type*} (f : α → Nat) :
    ∀ (xs : List α) {x : α}, x ∈ xs →
      ∀ init, f x ≤ xs.foldl (fun longest y => max longest (f y)) init
  | [], x, present, _ => by simp at present
  | a :: as, x, present, init => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp present with same | tailPresent
      · subst x
        exact Nat.le_trans (Nat.le_max_right _ _)
          (le_foldl_max f as (max init (f a)))
      · exact f_le_foldl_max f as tailPresent (max init (f a))

/-- The maximum child sphere count is positive as soon as a child with a nonempty Rule-1a
projection is present. -/
private theorem childLayerCount_pos_of_mem {V : Type*}
    (children : List (OfficialRuleMajorKey V)) (key : OfficialRuleMajorKey V)
    (present : key ∈ children) (ruleNonempty : key.rule1a ≠ []) :
    0 < OfficialRuleMajorKey.childLayerCount children OfficialRuleMajorKey.rule1a := by
  unfold OfficialRuleMajorKey.childLayerCount
  have lengthPos : 0 < key.rule1a.length := List.length_pos_iff.mpr ruleNonempty
  have bound : key.rule1a.length ≤
      children.foldl (fun longest child => max longest child.rule1a.length) 0 :=
    f_le_foldl_max (fun child : OfficialRuleMajorKey V => child.rule1a.length)
      children present 0
  omega

/-- A merge of sorted child Rule-1a spheres is nonempty whenever the first child has a nonempty
Rule-1a projection. -/
private theorem mergeChildren_rule1a_ne_nil_of_cons {V : Type*}
    (first : OfficialRuleMajorKey V) (rest : List (OfficialRuleMajorKey V))
    (ruleNonempty : first.rule1a ≠ []) :
    OfficialRuleMajorKey.mergeChildren (first :: rest) OfficialRuleMajorKey.rule1a ≠ [] := by
  unfold OfficialRuleMajorKey.mergeChildren
  dsimp only
  have countPos : 0 < OfficialRuleMajorKey.childLayerCount (first :: rest)
      OfficialRuleMajorKey.rule1a :=
    childLayerCount_pos_of_mem (first :: rest) first (by simp) ruleNonempty
  have rangeNe : List.range (OfficialRuleMajorKey.childLayerCount (first :: rest)
      OfficialRuleMajorKey.rule1a) ≠ [] := by
    rw [List.range_ne_nil]
    exact Nat.ne_of_gt countPos
  intro empty
  exact rangeNe (List.map_eq_nil_iff.mp empty)

/-- `compareNat` is reflexive, with the same proof term shape as the generic `ReflCmp` API. -/
private theorem compareNat_self (n : Nat) :
    OfficialRuleMajorKey.compareNat n n = Ordering.eq := by
  show compare n n = Ordering.eq
  exact Std.compare_self

/-- Rule-1a sparse-entry comparison of an addressed observation with itself is `eq`. -/
private theorem compareSparseEntry_nat_self (entry : OfficialSparseEntry Nat) :
    OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat entry entry =
      Ordering.eq := by
  letI : Std.ReflCmp OfficialRuleMajorKey.compareNat := ⟨fun {n} => compareNat_self n⟩
  obtain ⟨address, observation⟩ := entry
  have addressEq' : List.compareLex OfficialRuleMajorKey.compareNat address address =
      Ordering.eq := Std.ReflCmp.compare_self
  have addressEq :
      flip (List.compareLex OfficialRuleMajorKey.compareNat) address address =
        Ordering.eq := addressEq'
  have observationEq : OfficialRuleMajorKey.compareNat observation observation =
      Ordering.eq := Std.ReflCmp.compare_self
  simp [OfficialRuleMajorKey.compareSparseEntry, compareLex, Ordering.byKey,
    addressEq, observationEq]

/-- Rule-1a sparse-layer comparison of a layer with itself is `eq`. -/
private theorem compareSparseLayer_nat_self (layer : List (OfficialSparseEntry Nat)) :
    OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat layer layer =
      Ordering.eq := by
  induction layer with
  | nil => rfl
  | cons entry entries ih =>
      simp only [OfficialRuleMajorKey.compareSparseLayer, List.compareLex_cons_cons,
        compareSparseEntry_nat_self entry, Ordering.eq_then] at ih ⊢
      exact ih

/-- **Terminal versus a nonempty merged tail.**  If the left Rule-1a projection has a nonempty
sphere list after a common root sphere and the right projection ends at that root sphere, the
addressed layer comparison is strictly `gt`.  `compareSparseLayers` is ordinary `List.compareLex`:
after the common first sphere compares equal, the nonempty left list is compared with `[]`.  No
zero-padded sphere is involved, and nothing below the first sphere is inspected. -/
private theorem compareSparseLayers_rule1a_tail_gt
    (z : Nat) (tail : List (List (OfficialSparseEntry Nat)))
    (nonempty : tail ≠ []) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      ([([], z)] :: tail) [[([], z)]] = Ordering.gt := by
  rcases List.exists_cons_of_ne_nil nonempty with ⟨firstExtra, restExtra, rfl⟩
  unfold OfficialRuleMajorKey.compareSparseLayers
  rw [List.compareLex_cons_cons, compareSparseLayer_nat_self,
    List.compareLex_cons_nil]
  simp

end Source2013ParentTerminalKeySeparation

/-! ## Rule-1a shape of the observed cumulative builder

The builder is the production construction with two independent observation sources.  The shape
lemmas below are pure consequences of its actual equations; no comparison outcome is assumed. -/

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-- Every successful observed cumulative build retains the cursor node's atomic number as the
first Rule-1a sphere, whatever the observer, the label reader, the child ordering and the fuel. -/
theorem buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1a_head
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor = some key →
      key.constitutional.rule1a.head? =
        some [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
          cursor.occurrence.1.node)).1)]
  | 0, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · cases obs : observe cursor.occurrence.1.node with
            | none =>
                simp [childrenComputed, terminal, MoleculeGraph.observedRuleMajorRootKey?,
                  obs] at computed
            | some scalar =>
                simp [childrenComputed, terminal, MoleculeGraph.observedRuleMajorRootKey?,
                  obs] at computed
                subst key
                simp [MoleculeGraph.officialRuleMajorRootKeyWith]
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · cases obs : observe cursor.occurrence.1.node with
            | none =>
                simp [childrenComputed, terminal, MoleculeGraph.observedRuleMajorRootKey?,
                  obs] at computed
            | some scalar =>
                simp [childrenComputed, terminal, MoleculeGraph.observedRuleMajorRootKey?,
                  obs] at computed
                subst key
                simp [MoleculeGraph.officialRuleMajorRootKeyWith]
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                cases obs : observe cursor.occurrence.1.node with
                | none =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      MoleculeGraph.observedRuleMajorRootKey?, obs] at computed
                | some scalar =>
                    simp [childrenComputed, terminal, childKeysComputed,
                      MoleculeGraph.observedRuleMajorRootKey?, obs] at computed
                    subst key
                    rw [Source2013ParentTerminalKeySeparation.assemble_rootKey_rule1a]
                    rfl

/-- A successful observed build at a cursor with no actual children has the singleton Rule-1a
projection of that cursor's node.  This holds at every fuel, in both the zero and the successor
case of the builder. -/
theorem buildLocalizedObservedCumulativeRule45Key?_terminal_constitutional_rule1a
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.localizedRerootChildren? cursor = some [] →
      input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor = some key →
      key.constitutional.rule1a =
        [[([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
          cursor.occurrence.1.node)).1)]]
  | 0, cursor, key, childrenComputed, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      rw [childrenComputed] at computed
      simp at computed
      cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
          observe cursor.occurrence.1.node true with
      | none => simp [rootComputed] at computed
      | some constitutional =>
          simp [rootComputed] at computed
          subst key
          exact input.moleculeGraph.observedRuleMajorRootKey?_rule1a_eq_singleton
            observe cursor.occurrence.1.node true constitutional rootComputed
  | fuel + 1, cursor, key, childrenComputed, computed => by
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      rw [childrenComputed] at computed
      simp at computed
      cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
          observe cursor.occurrence.1.node true with
      | none => simp [rootComputed] at computed
      | some constitutional =>
          simp [rootComputed] at computed
          subst key
          exact input.moleculeGraph.observedRuleMajorRootKey?_rule1a_eq_singleton
            observe cursor.occurrence.1.node true constitutional rootComputed

/-- **Nonterminal decomposition of an actual observed build.**  If the cursor has a nonempty
actual child list and the observed builder succeeds at a positive fuel, then the child keys and
their actual label-dependent sort exist, the sort is nonempty, and the key's Rule-1a projection
is the root sphere followed by the merge of the sorted child constitutional spheres.  Every
child key in the sort is a successful build of an actual child. -/
theorem buildLocalizedObservedCumulativeRule45Key?_nonempty_decomposition
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    {fuel : Nat} (fuelPos : 0 < fuel)
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (childrenComputed : input.localizedRerootChildren? cursor = some children)
    (nonempty : children ≠ [])
    {key : input.LocalizedRerootCumulativeRule45Key}
    (computed :
      input.buildLocalizedObservedCumulativeRule45Key? stage observe read fuel cursor = some key) :
    ∃ (childKeys sorted : List input.LocalizedRerootCumulativeRule45Key),
      children.mapM
          (input.buildLocalizedObservedCumulativeRule45Key? stage observe read (fuel - 1)) =
        some childKeys ∧
      input.sortLocalizedRerootCumulativeRule45Keys childKeys = sorted ∧
      sorted ≠ [] ∧
      key.constitutional.rule1a =
        [([], (ofLex (input.moleculeGraph.officialNodeAtomLabel
            cursor.occurrence.1.node)).1)] ::
          OfficialRuleMajorKey.mergeChildren
            (sorted.map fun child => child.constitutional)
            OfficialRuleMajorKey.rule1a := by
  cases fuel with
  | zero => omega
  | succ previous =>
      unfold buildLocalizedObservedCumulativeRule45Key? at computed
      simp [childrenComputed, nonempty] at computed
      cases childKeysComputed : children.mapM
          (input.buildLocalizedObservedCumulativeRule45Key? stage observe read previous) with
      | none => simp [childKeysComputed] at computed
      | some childKeys =>
          simp [childKeysComputed] at computed
          cases obs : observe cursor.occurrence.1.node with
          | none =>
              simp [MoleculeGraph.observedRuleMajorRootKey?, obs] at computed
          | some scalar =>
              simp [MoleculeGraph.observedRuleMajorRootKey?, obs] at computed
              subst key
              refine ⟨childKeys, input.sortLocalizedRerootCumulativeRule45Keys childKeys,
                ?_, rfl, ?_, ?_⟩
              · simpa using childKeysComputed
              · obtain ⟨witness, witnessMem⟩ :=
                  List.exists_mem_of_ne_nil children nonempty
                obtain ⟨mapped, mappedMem, _mappedComputed⟩ :=
                  Source2013ParentTerminalKeySeparation.mapM_exists_of_mem
                    (input.buildLocalizedObservedCumulativeRule45Key? stage observe read previous)
                    childKeysComputed witness witnessMem
                have sortedMem : mapped ∈
                    input.sortLocalizedRerootCumulativeRule45Keys childKeys :=
                  (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys).mem_iff.mpr
                    mappedMem
                intro empty
                rw [empty] at sortedMem
                simp at sortedMem
              · rw [Source2013ParentTerminalKeySeparation.assemble_rootKey_rule1a]

end CertifiedLocalizedCIPInput

/-! ## The general actual-built key comparison -/

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-- **General actual-built key lemma: terminal right versus nonempty left.**  A successful
terminal build on the right and a successful nonterminal build on the left, with equal root
atomic numbers, compare strictly `gt` at Rule 1a.  The left child list's actual first sorted child
supplies a nonempty merged sphere; the terminal side has exactly one sphere.  The proof uses the
builder's actual sort, whatever order the labels induce, and does not inspect the child
observations. -/
theorem buildLocalizedObservedCumulativeRule45Key?_terminal_nonempty_rule1a_gt
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    {leftFuel : Nat} (leftFuelPos : 0 < leftFuel)
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    {leftChildren : List (input.LocalizedRerootCursor carrierFuel)}
    (leftChildrenComputed : input.localizedRerootChildren? leftCursor = some leftChildren)
    (leftNonempty : leftChildren ≠ [])
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (leftComputed : input.buildLocalizedObservedCumulativeRule45Key?
      stage observe read leftFuel leftCursor = some leftKey)
    {rightFuel : Nat}
    (rightChildrenComputed : input.localizedRerootChildren? rightCursor = some [])
    (rightComputed : input.buildLocalizedObservedCumulativeRule45Key?
      stage observe read rightFuel rightCursor = some rightKey)
    (rootLabelsEqual :
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        leftCursor.occurrence.1.node)).1 =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        rightCursor.occurrence.1.node)).1) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      leftKey.constitutional.rule1a rightKey.constitutional.rule1a = Ordering.gt := by
  obtain ⟨childKeys, sorted, mapMComputed, sortComputed, sortedNonempty, leftShape⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_nonempty_decomposition
      stage observe read leftFuelPos leftChildrenComputed leftNonempty leftComputed
  have rightShape :=
    input.buildLocalizedObservedCumulativeRule45Key?_terminal_constitutional_rule1a
      stage observe read rightFuel rightCursor rightKey rightChildrenComputed rightComputed
  obtain ⟨first, rest, sortedEq⟩ := List.exists_cons_of_ne_nil sortedNonempty
  have firstMemSorted : first ∈ sorted := by rw [sortedEq]; simp
  have firstMemChildKeys : first ∈ childKeys := by
    have sortedPerm := input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys
    rw [sortComputed] at sortedPerm
    exact sortedPerm.mem_iff.mp firstMemSorted
  obtain ⟨childCursor, _childMem, childBuilt⟩ :=
    Source2013ParentTerminalKeySeparation.mapM_mem_of_exists
      (input.buildLocalizedObservedCumulativeRule45Key? stage observe read (leftFuel - 1))
      mapMComputed first firstMemChildKeys
  have childHead :=
    input.buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1a_head
      stage observe read (leftFuel - 1) childCursor first childBuilt
  have firstRuleNonempty : first.constitutional.rule1a ≠ [] := by
    intro empty
    simp [empty] at childHead
  have mergedNonempty : OfficialRuleMajorKey.mergeChildren
      (sorted.map fun child => child.constitutional) OfficialRuleMajorKey.rule1a ≠ [] := by
    rw [sortedEq]
    simp only [List.map_cons]
    exact Source2013ParentTerminalKeySeparation.mergeChildren_rule1a_ne_nil_of_cons
      first.constitutional (rest.map fun child => child.constitutional) firstRuleNonempty
  rw [leftShape, rightShape]
  rw [rootLabelsEqual]
  exact Source2013ParentTerminalKeySeparation.compareSparseLayers_rule1a_tail_gt
    _ _ mergedNonempty

/-! ## The 2013 endpoint at the structural fuel bound -/

/-- **2013 observed keys, terminal right versus nonempty left.**  At fuel
`2 * (carrierFuel + 1)`, with observer `fun node => some (sourceObservation2013 node)` and an
arbitrary label reader, both cumulative keys exist for path-valid cursors.  The full Rule-1a
projections are strictly ordered `gt` after equal root spheres, so the constitutional comparator is `gt` *before Rule 1b is
consulted*, and the cumulative comparator is exactly that constitutional comparison (the
descriptor projection is never reached).  No key existence, no inequality and no comparison
direction is assumed. -/
theorem source2013_terminalRight_nonemptyLeft_separation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid leftCursor)
    (rightValid : input.LocalizedRerootCursorValid rightCursor)
    (leftChildren : List (input.LocalizedRerootCursor carrierFuel))
    (leftChildrenComputed : input.localizedRerootChildren? leftCursor = some leftChildren)
    (leftNonempty : leftChildren ≠ [])
    (rightTerminal : input.localizedRerootChildren? rightCursor = some [])
    (rootLabelsEqual :
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        leftCursor.occurrence.1.node)).1 =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        rightCursor.occurrence.1.node)).1) :
    ∃ leftKey rightKey,
      input.buildLocalizedObservedCumulativeRule45Key? stage
          (fun node => some (sourceObservation2013 node)) read
          (2 * (carrierFuel + 1)) leftCursor = some leftKey ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage
          (fun node => some (sourceObservation2013 node)) read
          (2 * (carrierFuel + 1)) rightCursor = some rightKey ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftKey.constitutional.rule1a rightKey.constitutional.rule1a = Ordering.gt ∧
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          leftKey.constitutional.rule1a rightKey.constitutional.rule1a ∧
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
        Ordering.gt ∧
      input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
        OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional := by
  have fuelPos : 0 < 2 * (carrierFuel + 1) := by omega
  obtain ⟨leftKey, leftBuilt⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
      stage (fun node => some (sourceObservation2013 node)) read leftCursor leftValid
      (fun _ => rfl)
  obtain ⟨rightKey, rightBuilt⟩ :=
    input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
      stage (fun node => some (sourceObservation2013 node)) read rightCursor rightValid
      (fun _ => rfl)
  have rule1aGt :=
    input.buildLocalizedObservedCumulativeRule45Key?_terminal_nonempty_rule1a_gt
      stage (fun node => some (sourceObservation2013 node)) read fuelPos
      leftChildrenComputed leftNonempty leftBuilt rightTerminal rightBuilt rootLabelsEqual
  have decisive :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftKey.constitutional.rule1a rightKey.constitutional.rule1a ≠ Ordering.eq := by
    rw [rule1aGt]
    decide
  have constitutionalEq :
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          leftKey.constitutional.rule1a rightKey.constitutional.rule1a :=
    OfficialRuleMajorKey.compare_eq_rule1a_of_decisive decisive
  have constitutionalGt :
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
        Ordering.gt := by
    rw [constitutionalEq, rule1aGt]
  have cumulativeEq :
      input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
        OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional :=
    input.compareCumulative_eq_constitutional_of_constitutional_ne_eq leftKey rightKey
      (by rw [constitutionalGt]; decide)
  exact ⟨leftKey, rightKey, leftBuilt, rightBuilt, rule1aGt, constitutionalEq,
    constitutionalGt, cumulativeEq⟩

/-- **The 2013 root Rule-1b first spheres of actually-built observed keys.**  With observer
`fun node => some (sourceObservation2013 node)`, a successful observed build carries exactly the
cursor node's 2013 observation as its first Rule-1b sphere. -/
theorem buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildLocalizedObservedCumulativeRule45Key? stage
          (fun node => some (sourceObservation2013 node)) read fuel cursor = some key →
      key.constitutional.rule1b.head? =
        some [([], sourceObservation2013 cursor.occurrence.1.node)]
  | fuel, cursor, key, computed => by
      obtain ⟨scalar, observed, head⟩ :=
        input.buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1b_head
          stage (fun node => some (sourceObservation2013 node)) read fuel cursor key computed
      have scalarEq : sourceObservation2013 cursor.occurrence.1.node = scalar := by
        simpa using observed
      subst scalar
      exact head

/-- **Insulation under the 2013 root Rule-1b tie.**  With the same actual terminal-right /
nonempty-left data at fuel `2 * (carrierFuel + 1)`, suppose the two root observations tie under
`sourceObservation2013`.  Then both built keys' first Rule-1b spheres are that common tied value,
yet the Rule-1a comparison is `gt`, the constitutional comparator is `gt` without consulting
Rule 1b, and the cumulative comparator is the constitutional one.  The tie is recorded, not
assumed away and not used to decide anything. -/
theorem source2013_terminalRight_nonemptyLeft_separation_despite_rootTie
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftValid : input.LocalizedRerootCursorValid leftCursor)
    (rightValid : input.LocalizedRerootCursorValid rightCursor)
    (leftChildren : List (input.LocalizedRerootCursor carrierFuel))
    (leftChildrenComputed : input.localizedRerootChildren? leftCursor = some leftChildren)
    (leftNonempty : leftChildren ≠ [])
    (rightTerminal : input.localizedRerootChildren? rightCursor = some [])
    (rootLabelsEqual :
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        leftCursor.occurrence.1.node)).1 =
      (ofLex (input.moleculeGraph.officialNodeAtomLabel
        rightCursor.occurrence.1.node)).1)
    (rootTie : sourceObservation2013 leftCursor.occurrence.1.node =
      sourceObservation2013 rightCursor.occurrence.1.node) :
    ∃ leftKey rightKey,
      input.buildLocalizedObservedCumulativeRule45Key? stage
          (fun node => some (sourceObservation2013 node)) read
          (2 * (carrierFuel + 1)) leftCursor = some leftKey ∧
      input.buildLocalizedObservedCumulativeRule45Key? stage
          (fun node => some (sourceObservation2013 node)) read
          (2 * (carrierFuel + 1)) rightCursor = some rightKey ∧
      leftKey.constitutional.rule1b.head? =
        some [([], sourceObservation2013 leftCursor.occurrence.1.node)] ∧
      rightKey.constitutional.rule1b.head? =
        some [([], sourceObservation2013 rightCursor.occurrence.1.node)] ∧
      leftKey.constitutional.rule1b.head? = rightKey.constitutional.rule1b.head? ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftKey.constitutional.rule1a rightKey.constitutional.rule1a = Ordering.gt ∧
      OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional =
        Ordering.gt ∧
      input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey =
        OfficialRuleMajorKey.compare leftKey.constitutional rightKey.constitutional := by
  obtain ⟨leftKey, rightKey, leftBuilt, rightBuilt, rule1aGt, _constitutionalEq,
    constitutionalGt, cumulativeEq⟩ :=
    input.source2013_terminalRight_nonemptyLeft_separation
      stage read leftCursor rightCursor leftValid rightValid leftChildren
      leftChildrenComputed leftNonempty rightTerminal rootLabelsEqual
  have leftRule1b :=
    input.buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
      stage read (2 * (carrierFuel + 1)) leftCursor leftKey leftBuilt
  have rightRule1b :=
    input.buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
      stage read (2 * (carrierFuel + 1)) rightCursor rightKey rightBuilt
  have rule1bHeadsEqual :
      leftKey.constitutional.rule1b.head? = rightKey.constitutional.rule1b.head? := by
    rw [leftRule1b, rightRule1b, rootTie]
  exact ⟨leftKey, rightKey, leftBuilt, rightBuilt, leftRule1b, rightRule1b,
    rule1bHeadsEqual, rule1aGt, constitutionalGt, cumulativeEq⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

Every new scientific export is guarded.  `assert_kernel_only` permits exactly `propext`,
`Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and native/compiler
trust.  The observed-builder arguments use `Classical.choice` through the existing fail-closed
child enumeration. -/

assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.observedRuleMajorRootKey?_rule1a_eq_singleton
assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.observedRuleMajorRootKey?_rule1a_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_constitutional_rule1a_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_terminal_constitutional_rule1a
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_nonempty_decomposition
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_terminal_nonempty_rule1a_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.source2013_terminalRight_nonemptyLeft_separation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.source2013_terminalRight_nonemptyLeft_separation_despite_rootTie
