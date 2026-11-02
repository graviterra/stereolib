import TetraStereo.OneCenter.LocalizedObservedCumulativeAvailability
import TetraStereo.OneCenter.Source2013ParentTerminalKeySeparation
import TetraStereo.OneCenter.Source2013ParentDuplicateStructuralSeparation
import TetraStereo.OneCenter.Source2013ActualParentComparison
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

namespace TetraStereo.OneCenter

open Rule1bSourceProfileCompiler

namespace CertifiedLocalizedCIPInput

/-!
# Actual-frame parent-versus-outward comparison for the totalized 2013 observer

This module closes the ACTUAL four-ligand-frame comparison between the parent cursor and *every*
other cursor of the frame, for the **explicitly totalized original-root bb2013 observer**
`fun node => some (sourceObservation2013 node)`, under arbitrary auxiliary-label readers.

The two structural regimes are exhaustive:

* **Backward duplicate of the parent atom** (`next = parentAtom`).  The outward child is a positive
  multiple-bond copy of the parent atom.  Under `sourceObservation2013` its root observation ties the
  real parent's, so Rule 1b does not separate the two cursors.  What separates them is Rule 1a: the
  actual parent rerooted away from the target still has a positive-copy child (nonempty merged
  Rule-1a), while the duplicate is terminal (singleton Rule-1a).  The separation is therefore
  decided *before* the tied Rule-1b sphere, and the descriptor projection is never consulted.
* **Every other child** (`next ≠ parentAtom`), which covers real atoms, ring duplicates, forward
  multiple-bond duplicates and backward duplicates of higher ancestors.  The totalized 2013
  observation of the extended node differs strictly from the real parent's, so the two built keys
  have distinct singleton Rule-1b first spheres; the constitutional comparator is strict and the
  full cumulative comparator is the constitutional one.

In both regimes each of the two *arbitrary* readers is compiled separately at the common numeric
fuel `2 * (carrierFuel + 1)`, and the resulting comparisons are proved **non-tied** and **equal
across the two readers**.  Non-tie alone is not the statement: the descriptor component of the
cumulative key depends on the reader, so the proof also shows that the reader-dependent descriptor
is never reached and that the constitutional comparison is reader-independent.

Reader independence of the constitutional observable of the observed builder is proved once, for an
arbitrary observer and arbitrary readers
(`buildLocalizedObservedCumulativeRule45Key?_constitutionalObservable_eq`).  It is a genuine
recursion on the actual fuel and on the actual `List.mapM`; the sibling sort may differ between
readers, and the proof passes through sorted-permutation uniqueness of constitutional observables and
the addressed assembly factorization.

## Scope and honesty

* The observer is the **totalized** original-root bb2013 observation
  `fun node => some (sourceObservation2013 node)`.  Its `realAtom` branch is the documented
  comparison-totality convention of `SourceProfileRule1bCompiler`; it is **not** a normative 2013
  duplicate-only source clause.  Nothing here claims independent 2013 chemical fidelity, and
  nothing here asserts that the totalized real-node sphere is the historical 2013 semantics.
* The frame data (`localizedOccurrenceFourLigandFrame? target = some frame`) is the actual executable
  frame.  Parent history, activity, positive-copy and bond facts are derived from that frame, the
  finite carrier membership of its cursors, and the real provenance of the target.  No caller
  supplies a parent/outward proof certificate, a successful-key premise, a desired tie, or a desired
  comparison outcome.
* Key existence is derived from `buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice`
  at the common bound `2 * (carrierFuel + 1)`, not assumed.
* The exact existing algorithms are reused: the production child enumeration, the cumulative sibling
  sort, the descriptor/label/ranked-label merges and the rule-major assembly.  No replacement
  enumerator or second solver is introduced.
-/

/-! ## Generic `List.mapM` projection congruence -/

/-- Pointwise agreement of the projected options lifts through `List.mapM`.  This is the
`List.mapM` induction used by the constitutional-observable reader independence; it is purely
generic and duplicates only the small private helper shape already used by the exact public
observable proof, because that helper is private to its module. -/
private theorem observedConstitutional_list_mapM_map_projection {α β γ : Type*}
    (first second : α → Option β) (project : β → γ)
    (agrees : ∀ value, (first value).map project = (second value).map project) :
    ∀ values : List α,
      (values.mapM first).map (List.map project) =
        (values.mapM second).map (List.map project)
  | [] => rfl
  | value :: values => by
      rw [List.mapM_cons, List.mapM_cons]
      have inner : ∀ chosen : β,
          Option.map (List.map project)
              ((values.mapM first).bind (fun rest => some (chosen :: rest))) =
            Option.map (List.map project)
              ((values.mapM second).bind (fun rest => some (chosen :: rest))) := by
        intro chosen
        rw [Option.map_bind, Option.map_bind]
        show (values.mapM first).bind
              (fun rest => some (project chosen :: List.map project rest)) =
            (values.mapM second).bind
              (fun rest => some (project chosen :: List.map project rest))
        have firstNormalized :
            (values.mapM first).bind
                (fun rest => some (project chosen :: List.map project rest)) =
              (values.mapM first).map
                (fun rest => project chosen :: List.map project rest) := by
          cases List.mapM first values <;> rfl
        have secondNormalized :
            (values.mapM second).bind
                (fun rest => some (project chosen :: List.map project rest)) =
              (values.mapM second).map
                (fun rest => project chosen :: List.map project rest) := by
          cases List.mapM second values <;> rfl
        rw [firstNormalized, secondNormalized]
        have combined := congrArg
          (Option.map (fun rest : List γ => project chosen :: rest))
          (observedConstitutional_list_mapM_map_projection first second project agrees values)
        rw [Option.map_map, Option.map_map] at combined
        exact combined
      cases firstComputed : first value with
      | none =>
          have secondComputed : second value = none := by
            have pointwise := agrees value
            rw [firstComputed] at pointwise
            cases secondValue : second value with
            | none => rfl
            | some _ => simp [secondValue] at pointwise
          rw [secondComputed]
          rfl
      | some head =>
          have secondValue :
              ∃ other, second value = some other ∧ project head = project other := by
            have pointwise := agrees value
            rw [firstComputed] at pointwise
            cases secondComputed : second value with
            | none => simp [secondComputed] at pointwise
            | some other =>
                simp [secondComputed] at pointwise
                exact ⟨other, rfl, pointwise⟩
          obtain ⟨other, secondComputed, projectionEq⟩ := secondValue
          rw [secondComputed]
          show Option.map (List.map project)
                ((values.mapM first).bind (fun rest => some (head :: rest))) =
              Option.map (List.map project)
                ((values.mapM second).bind (fun rest => some (other :: rest)))
          rw [inner head]
          rw [Option.map_bind, Option.map_bind]
          show (values.mapM second).bind
                (fun rest => some (project head :: List.map project rest)) =
              (values.mapM second).bind
                (fun rest => some (project other :: List.map project rest))
          rw [projectionEq]

/-- The `Bind`-class syntactic form of `Option.bind_some`, matching `do`-notation elaboration. -/
private theorem bind_some_option {α β : Type u} (value : α) (next : α → Option β) :
    Bind.bind (some value) next = next value := rfl

/-- The `Bind`-class syntactic form of `Option.bind_none`. -/
private theorem bind_none_option {α β : Type u} (next : α → Option β) :
    Bind.bind (none : Option α) next = none := rfl

/-! ## Reader independence of the observed constitutional observable -/

/-- **Reader independence of the observed constitutional observable (engine for the totalized
2013 observer).**

For an arbitrary observer, an arbitrary cumulative stage, and **arbitrary** auxiliary-label readers,
two observed cumulative builds at the same fuel and cursor have the same constitutional observable.
This covers the fail-closed `none` outcomes as well, because the statement maps the whole `Option`
key through the constitutional projection.

The proof is a recursion on the actual fuel and on the actual `List.mapM` over the executable
children.  The sibling sort is reader-dependent (its full cumulative comparator consults the
descriptor), so the proof does not assume that the sorted orders agree: it transports equality of
the projectioned child lists to equality of their constitutional-key sequences by
`constitutional_observables_eq_of_perm`, using the descending property of the production sort and the
constitutional coherence of the cumulative comparator, and then applies the addressed assembly
factorization `assembled_constitutional_observable_eq`.  No key equality and no comparison outcome
is assumed. -/
private theorem buildLocalizedObservedCumulativeRule45Key?_constitutionalObservable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (observe : OfficialCIPNode input.Atom → Option Nat)
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      (input.buildLocalizedObservedCumulativeRule45Key? stage observe first fuel cursor).map
          (fun key => constitutionalObservable key.constitutional) =
        (input.buildLocalizedObservedCumulativeRule45Key? stage observe second fuel cursor).map
          (fun key => constitutionalObservable key.constitutional)
  | 0, cursor => by
      unfold buildLocalizedObservedCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp only [childrenComputed, bind_none_option]
      | some children =>
          by_cases terminal : children = []
          · cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none =>
                simp only [bind_some_option, childrenComputed, if_pos terminal, rootComputed,
                  bind_none_option]
            | some constitutional =>
                simp only [bind_some_option, childrenComputed, if_pos terminal, rootComputed,
                  Option.map_some, Option.some.injEq, constitutionalObservable]
          · simp only [bind_some_option, childrenComputed, if_neg terminal]
  | fuel + 1, cursor => by
      unfold buildLocalizedObservedCumulativeRule45Key?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp only [childrenComputed, bind_none_option]
      | some children =>
          by_cases terminal : children = []
          · cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                observe cursor.occurrence.1.node true with
            | none =>
                simp only [bind_some_option, childrenComputed, if_pos terminal, rootComputed,
                  bind_none_option]
            | some constitutional =>
                simp only [bind_some_option, childrenComputed, if_pos terminal, rootComputed,
                  Option.map_some, Option.some.injEq, constitutionalObservable]
          · have mapProjectionEq :
                ((children.mapM (input.buildLocalizedObservedCumulativeRule45Key?
                    stage observe first fuel)).map
                    (List.map (fun key => constitutionalObservable key.constitutional))) =
                  ((children.mapM (input.buildLocalizedObservedCumulativeRule45Key?
                    stage observe second fuel)).map
                    (List.map (fun key => constitutionalObservable key.constitutional))) :=
              observedConstitutional_list_mapM_map_projection
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe first fuel)
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe second fuel)
                (fun key => constitutionalObservable key.constitutional)
                (fun child =>
                  buildLocalizedObservedCumulativeRule45Key?_constitutionalObservable_eq
                    input stage observe first second fuel child)
                children
            cases firstComputed : children.mapM
                (input.buildLocalizedObservedCumulativeRule45Key? stage observe first fuel) with
            | none =>
                have secondComputed : children.mapM
                    (input.buildLocalizedObservedCumulativeRule45Key?
                      stage observe second fuel) = none := by
                  cases secondValue : children.mapM
                      (input.buildLocalizedObservedCumulativeRule45Key?
                        stage observe second fuel) with
                  | none => rfl
                  | some _ => simp [firstComputed, secondValue] at mapProjectionEq
                simp only [bind_some_option, childrenComputed, if_neg terminal,
                  firstComputed, secondComputed, bind_none_option]
            | some firstKeys =>
                cases secondComputed : children.mapM
                    (input.buildLocalizedObservedCumulativeRule45Key?
                      stage observe second fuel) with
                | none => simp [firstComputed, secondComputed] at mapProjectionEq
                | some secondKeys =>
                    have observablesEq : firstKeys.map
                          (fun key => constitutionalObservable key.constitutional) =
                        secondKeys.map
                          (fun key => constitutionalObservable key.constitutional) := by
                      simpa [firstComputed, secondComputed] using mapProjectionEq
                    have sortedConstitutionalEq :
                        ((input.sortLocalizedRerootCumulativeRule45Keys firstKeys).map
                            (fun key => key.constitutional)).map constitutionalObservable =
                          ((input.sortLocalizedRerootCumulativeRule45Keys secondKeys).map
                            (fun key => key.constitutional)).map constitutionalObservable := by
                      have firstPerm :=
                        (input.sortLocalizedRerootCumulativeRule45Keys_perm firstKeys).map
                          (fun key => constitutionalObservable key.constitutional)
                      have secondPerm :=
                        (input.sortLocalizedRerootCumulativeRule45Keys_perm secondKeys).map
                          (fun key => constitutionalObservable key.constitutional)
                      refine constitutional_observables_eq_of_perm
                        ((input.sortLocalizedRerootCumulativeRule45Keys firstKeys).map
                          (fun key => key.constitutional))
                        ((input.sortLocalizedRerootCumulativeRule45Keys secondKeys).map
                          (fun key => key.constitutional)) ?_ ?_ ?_
                      · simpa only [List.map_map, Function.comp_def] using
                          firstPerm.trans
                            ((List.Perm.of_eq observablesEq).trans secondPerm.symm)
                      · exact input.cumulative_descending_constitutional
                          (input.sortLocalizedRerootCumulativeRule45Keys firstKeys)
                          (input.sortLocalizedRerootCumulativeRule45Keys_descending firstKeys)
                      · exact input.cumulative_descending_constitutional
                          (input.sortLocalizedRerootCumulativeRule45Keys secondKeys)
                          (input.sortLocalizedRerootCumulativeRule45Keys_descending secondKeys)
                    cases rootComputed : input.moleculeGraph.observedRuleMajorRootKey?
                        observe cursor.occurrence.1.node false with
                    | none =>
                        simp only [bind_some_option, childrenComputed, if_neg terminal,
                          firstComputed, secondComputed, rootComputed, bind_none_option]
                    | some constitutional =>
                        have assembledEq := assembled_constitutional_observable_eq
                          constitutional
                          ((input.sortLocalizedRerootCumulativeRule45Keys firstKeys).map
                            (fun key => key.constitutional))
                          ((input.sortLocalizedRerootCumulativeRule45Keys secondKeys).map
                            (fun key => key.constitutional))
                          sortedConstitutionalEq
                        simp only [bind_some_option, childrenComputed, if_neg terminal,
                          firstComputed, secondComputed, rootComputed, Option.map_some,
                          Option.some.injEq]
                        change constitutionalObservable
                            (OfficialRuleMajorKey.assemble constitutional
                              ((input.sortLocalizedRerootCumulativeRule45Keys firstKeys).map
                                (fun key => key.constitutional))) =
                          constitutionalObservable
                            (OfficialRuleMajorKey.assemble constitutional
                              ((input.sortLocalizedRerootCumulativeRule45Keys secondKeys).map
                                (fun key => key.constitutional)))
                        exact assembledEq

/-! ## Successful-shape and comparison bridges -/

/-- **Successful-shape constitutional observable equality for the totalized 2013 observer.**

If both arbitrary readers succeed at the same fuel and cursor under the totalized original-root
bb2013 observer, the resulting keys have equal constitutional observables.  This is the
success-form companion of the reader-independence theorem and never assumes key existence: the
success equations are hypotheses. -/
theorem totalizedObserver2013_constitutionalObservable_eq_of_builds
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    {firstKey secondKey : input.LocalizedRerootCumulativeRule45Key}
    (firstBuilt : input.buildLocalizedObservedCumulativeRule45Key? stage
      (fun node => some (sourceObservation2013 node)) first fuel cursor = some firstKey)
    (secondBuilt : input.buildLocalizedObservedCumulativeRule45Key? stage
      (fun node => some (sourceObservation2013 node)) second fuel cursor = some secondKey) :
    constitutionalObservable firstKey.constitutional =
      constitutionalObservable secondKey.constitutional := by
  have combined :=
    buildLocalizedObservedCumulativeRule45Key?_constitutionalObservable_eq
      input stage (fun node => some (sourceObservation2013 node)) first second fuel cursor
  rw [firstBuilt, secondBuilt] at combined
  simpa using combined

/-- **Reader-independent constitutional comparison of two totalized-2013 keys.**

Equality of the parent constitutional observables and of the outward constitutional observables
across two arbitrary readers implies equality of the two constitutional comparisons.  The proof is
the exact public comparator factorization `compare = compareConstitutionalObservable ∘
constitutionalObservable`; no comparison direction is assumed. -/
theorem totalizedObserver2013_constitutionalCompare_eq_of_observables
    (input : CertifiedLocalizedCIPInput)
    (parentFirst otherFirst parentSecond otherSecond :
      input.LocalizedRerootCumulativeRule45Key)
    (parentObservation : constitutionalObservable parentFirst.constitutional =
      constitutionalObservable parentSecond.constitutional)
    (otherObservation : constitutionalObservable otherFirst.constitutional =
      constitutionalObservable otherSecond.constitutional) :
    OfficialRuleMajorKey.compare parentFirst.constitutional otherFirst.constitutional =
      OfficialRuleMajorKey.compare parentSecond.constitutional otherSecond.constitutional := by
  rw [ruleMajor_compare_eq_observable, ruleMajor_compare_eq_observable,
    parentObservation, otherObservation]

/-! ## Structural derivation from the actual frame cursor

The final theorem must not accept a parent/outward proof certificate.  These helpers invert the
actual executable frame membership: a frame cursor at an appended sibling address is the
`OfficialCIPNode.extend` of the target node by one executable copy, and membership in the copy list
supplies the graph adjacency and the bond-order bound. -/

/-- Membership in the executable child-copy list yields graph adjacency and a bond-order bound.
Both are read off the executable enumerator; no adjacency or bond bound is assumed. -/
private theorem executableOfficialChildCopy_adjacent_and_bond
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (current next : input.Atom) (copyIndex : Nat)
    (currentObserved : node.current? = some current)
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node) :
    input.moleculeGraph.Adj current next ∧
      copyIndex < input.moleculeGraph.bond current next := by
  cases currentComputed : node.current? with
  | none =>
      unfold executableOfficialChildCopies at present
      simp [currentComputed] at present
  | some actual =>
      have actualEq : actual = current := by
        rw [currentComputed] at currentObserved
        exact Option.some.inj currentObserved
      subst actual
      cases parentComputed : node.parent? with
      | none =>
          unfold executableOfficialChildCopies at present
          simp only [currentComputed, parentComputed] at present
          exact (input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mp
            present
      | some parent =>
          unfold executableOfficialChildCopies at present
          simp only [currentComputed, parentComputed] at present
          have filtered := (List.mem_filter.mp present).1
          exact (input.mem_executableOfficialNeighborCopies_iff current next copyIndex).mp
            filtered

/-- The executable parent-zero-copy filter never lists the parent atom at copy index zero.
Hence a listed child whose atom is the stored parent atom is a positive multiple-bond copy. -/
private theorem executableOfficialChildCopy_copyIndex_ne_zero_of_parent
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (parentAtom next : input.Atom) (copyIndex : Nat)
    (parentObserved : node.parent? = some parentAtom)
    (nextEq : next = parentAtom)
    (present : (next, copyIndex) ∈ input.executableOfficialChildCopies node) :
    copyIndex ≠ 0 := by
  intro zero
  cases currentComputed : node.current? with
  | none =>
      unfold executableOfficialChildCopies at present
      simp [currentComputed] at present
  | some _ =>
      unfold executableOfficialChildCopies at present
      simp only [currentComputed, parentObserved] at present
      have filtered := List.mem_filter.mp present
      have contradiction : (false : Bool) = true := by
        simpa [nextEq, zero] using filtered.2
      exact Bool.false_ne_true contradiction

/-- **Actual frame outward cursor extension.**  A cursor of an actually computed four-ligand frame
whose address extends the target address by one sibling slot is the target node extended by an
actual executable child copy.  The sibling slot and the target's non-duplicate provenance are read
from the frame; no child certificate is assumed. -/
private theorem observedActualFrameOutwardChild_extension
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors)
    (slot : Nat)
    (addressEq : cursor.occurrence.1.address = target.1.address ++ [slot]) :
    ∃ next copyIndex,
      cursor.occurrence.1.node = target.1.node.extend next copyIndex ∧
        (next, copyIndex) ∈ input.executableOfficialChildCopies target.1.node := by
  have targetDerived : input.DeclarativeLocalizedOccurrence carrierFuel target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have cursorDerived :
      input.DeclarativeLocalizedOccurrence carrierFuel cursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
      cursor.occurrence.2
  have sameRoot := input.localizedOccurrenceFourLigandFrame_cursor_root
    target frame frameComputed cursor present
  obtain ⟨child, childAtSlot, occurrenceEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child targetDerived cursorDerived
      sameRoot slot addressEq
  have childMem : child ∈ input.executableOfficialCIPChildren target.1.node :=
    List.fst_mem_of_mem_zipIdx childAtSlot
  have targetNotDuplicate :=
    input.isDuplicateLeaf_eq_false_of_provenance_real target.1.node targetReal
  have mapMem : child ∈
      (input.executableOfficialChildCopies target.1.node).map
        (fun copy => target.1.node.extend copy.1 copy.2) := by
    simpa [executableOfficialCIPChildren, targetNotDuplicate] using childMem
  obtain ⟨copy, copyPresent, extendEq⟩ := List.mem_map.mp mapMem
  obtain ⟨next, copyIndex⟩ := copy
  have nodeEq : cursor.occurrence.1.node = child := by
    rw [occurrenceEq]
  refine ⟨next, copyIndex, ?_, copyPresent⟩
  exact nodeEq.trans extendEq.symm

/-! ## The totalized-2013 actual-frame exhaustion -/

/-- **Actual-frame parent-versus-every-other-cursor comparison for the totalized 2013 observer.**

For an actually computed four-ligand frame of a real, non-root carrier occurrence, there is an
actual parent index among the four frame cursors such that, for every other index and for two
**arbitrary** auxiliary-label readers, both readers compile observed cumulative keys at the common
fuel `2 * (carrierFuel + 1)` under the explicitly totalized original-root bb2013 observer
`fun node => some (sourceObservation2013 node)`.  The parent-versus-other cumulative comparison is
non-tied under each reader, and the two readers return the **identical** cumulative comparison.

Both structural regimes of the actual frame are covered:

* the backward positive-copy duplicate of the parent atom, where the totalized 2013 root spheres
  tie and the actual Rule-1a separation of the nonterminal parent from the terminal duplicate
  decides the comparison under the tie;
* every other child (real atoms, forward multiple-bond duplicates, ring duplicates, and backward
  duplicates of higher ancestors), where the totalized 2013 observations differ strictly and the
  singleton Rule-1b first spheres already decide the constitutional comparison.

The parent index, the parent activity and history, the positive-copy index, the bond-order lower
bound, the terminality and the two root observations are all derived from the computed frame, the
target's real provenance, the finite carrier membership of the frame cursors, and the carrier parent
certificate obtained from reachability.  No caller supplies a parent or outward proof certificate,
a successful-build premise, a desired tie, or a desired comparison outcome.  No additional positive
remaining-depth hypothesis is needed: the parent's positive remaining depth is derived from the
certificate inside the actual positive-copy construction, and key existence comes from the existing
common bound.

The theorem is a statement about the named **totalized** observer, not a claim of independent 2013
chemical fidelity: the real-atom branch of `sourceObservation2013` is the documented
comparison-totality convention, not a duplicate-only 2013 source clause. -/
theorem totalizedObserver2013_actualFrame_parentVersusEveryOtherChild_comparison_readerIndependent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (nonroot : target.1.address ≠ [])
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (first second : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∃ parentIndex : Fin 4,
      IsLocalizedActualFrameParentCursor input target (frame.cursorAt parentIndex) ∧
      ∀ otherIndex : Fin 4, otherIndex ≠ parentIndex →
        ∃ parentKeyFirst otherKeyFirst parentKeySecond otherKeySecond,
          input.buildLocalizedObservedCumulativeRule45Key? stage
              (fun node => some (sourceObservation2013 node)) first
              (2 * (carrierFuel + 1)) (frame.cursorAt parentIndex) = some parentKeyFirst ∧
          input.buildLocalizedObservedCumulativeRule45Key? stage
              (fun node => some (sourceObservation2013 node)) first
              (2 * (carrierFuel + 1)) (frame.cursorAt otherIndex) = some otherKeyFirst ∧
          input.buildLocalizedObservedCumulativeRule45Key? stage
              (fun node => some (sourceObservation2013 node)) second
              (2 * (carrierFuel + 1)) (frame.cursorAt parentIndex) = some parentKeySecond ∧
          input.buildLocalizedObservedCumulativeRule45Key? stage
              (fun node => some (sourceObservation2013 node)) second
              (2 * (carrierFuel + 1)) (frame.cursorAt otherIndex) = some otherKeySecond ∧
          input.compareLocalizedRerootCumulativeRule45Keys
              parentKeyFirst otherKeyFirst ≠ Ordering.eq ∧
          input.compareLocalizedRerootCumulativeRule45Keys
              parentKeySecond otherKeySecond ≠ Ordering.eq ∧
          input.compareLocalizedRerootCumulativeRule45Keys parentKeyFirst otherKeyFirst =
            input.compareLocalizedRerootCumulativeRule45Keys parentKeySecond otherKeySecond := by
  have targetActive : target.1.node.ActiveSimple :=
    input.localizedCIPOccurrence_activeSimple_of_provenance_real target targetReal
  obtain ⟨certificateActive⟩ :=
    input.exists_activeLocalizedParentFrameHistory target targetActive nonroot
  let certificate := certificateActive.toLocalizedParentFrameHistory
  let parentCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := certificate.parent, previous? := some target }
  have parentMemExec :=
    input.parentCursor_mem_executableLocalizedRerootChildren target targetActive certificate
  have parentMemFrame : parentCursor ∈ frame.cursors := by
    rw [input.localizedOccurrenceFourLigandFrame_cursors_eq_executable
      target frame frameComputed]
    exact parentMemExec
  obtain ⟨parentPosition, parentGet⟩ := List.mem_iff_get.mp parentMemFrame
  let parentIndex : Fin 4 :=
    ⟨parentPosition.val,
      Nat.lt_of_lt_of_le parentPosition.isLt (Nat.le_of_eq frame.length_eq)⟩
  have parentFinEq :
      (Fin.cast frame.length_eq.symm parentIndex : Fin frame.cursors.length) =
        parentPosition := Fin.ext rfl
  have parentCursorAtEq : frame.cursorAt parentIndex = parentCursor := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    rw [parentFinEq]
    exact parentGet
  have parentPresent : frame.cursorAt parentIndex ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm parentIndex)
  have parentAddress :
      IsLocalizedActualFrameParentCursor input target (frame.cursorAt parentIndex) := by
    show (frame.cursorAt parentIndex).occurrence.1.address = target.1.address.dropLast
    rw [parentCursorAtEq]
    exact certificate.parent_address
  refine ⟨parentIndex, parentAddress, ?_⟩
  intro otherIndex otherNe
  let otherCursor := frame.cursorAt otherIndex
  have parentPresent' : parentCursor ∈ frame.cursors := parentMemFrame
  have otherPresent : otherCursor ∈ frame.cursors :=
    List.get_mem frame.cursors (Fin.cast frame.length_eq.symm otherIndex)
  have parentValid : input.LocalizedRerootCursorValid (frame.cursorAt parentIndex) :=
    input.localizedOccurrenceFourLigandFrame_cursor_valid
      target frame frameComputed (frame.cursorAt parentIndex) parentPresent
  have otherValid : input.LocalizedRerootCursorValid otherCursor :=
    input.localizedOccurrenceFourLigandFrame_cursor_valid
      target frame frameComputed otherCursor otherPresent
  have parentAddressCanonical :
      IsLocalizedActualFrameParentCursor input target parentCursor :=
    certificate.parent_address
  have notParent : ¬ IsLocalizedActualFrameParentCursor input target otherCursor := by
    intro otherParent
    have cursorEq := input.localizedOccurrenceFourLigandFrame_parent_cursor_unique
      target frame frameComputed parentCursor otherCursor parentPresent' otherPresent
      parentAddressCanonical otherParent
    have indexEq : parentIndex = otherIndex := by
      apply input.localizedOccurrenceFourLigandFrame_cursorAt_injective
        target frame frameComputed
      exact parentCursorAtEq.trans cursorEq
    exact otherNe indexEq.symm
  have structural :=
    input.localizedOccurrenceFourLigandFrame_cursor_address_classification
      target frame frameComputed otherCursor otherPresent
  have outwardAddress :
      ∃ slot : Nat, otherCursor.occurrence.1.address = target.1.address ++ [slot] := by
    rcases structural with parentCase | outwardCase
    · exact (notParent parentCase.1).elim
    · exact outwardCase
  obtain ⟨slot, slotAddress⟩ := outwardAddress
  obtain ⟨next, copyIndex, nodeExtend, copyPresent⟩ :=
    observedActualFrameOutwardChild_extension input target targetReal frame frameComputed
      otherCursor otherPresent slot slotAddress
  obtain ⟨current, parentAtom, tail, targetCurrent, parentCurrent,
    targetHistory, parentHistory⟩ := certificate.history_shape input
  have targetParentObserved : target.1.node.parent? = some parentAtom := by
    simp [OfficialCIPNode.parent?, targetHistory]
  have copyFacts := executableOfficialChildCopy_adjacent_and_bond
    input target.1.node current next copyIndex targetCurrent copyPresent
  by_cases nextParent : next = parentAtom
  · -- Backward positive-copy duplicate of the parent atom.
    subst next
    have copyPositive : copyIndex ≠ 0 :=
      executableOfficialChildCopy_copyIndex_ne_zero_of_parent
        input target.1.node parentAtom parentAtom copyIndex targetParentObserved rfl
        copyPresent
    have doubleBond : 1 < input.moleculeGraph.bond current parentAtom := by
      exact Nat.lt_of_le_of_lt
        (Nat.succ_le_of_lt (Nat.pos_of_ne_zero copyPositive)) copyFacts.2
    have otherProvenance : otherCursor.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.multipleBondDuplicate target.1.node.depth := by
      rw [nodeExtend, OfficialCIPNode.extend_provenance,
        OfficialCIPNode.childProvenance_copy_pos target.1.node parentAtom copyPositive]
    have otherTerminal : input.localizedRerootChildren? otherCursor = some [] := by
      rw [input.localizedRerootChildren?_eq_some_executable,
        input.executableLocalizedRerootChildren_eq_nil_of_multipleBondDuplicate
          otherCursor target.1.node.depth otherProvenance]
    have parentNonemptyExec :
        input.executableLocalizedRerootChildren parentCursor ≠ [] :=
      input.actualParent_outwardCursor_children_ne_nil targetActive certificate
        current parentAtom tail targetCurrent targetHistory parentHistory doubleBond
    obtain ⟨parentChildren, parentChildrenComputed, parentChildrenNonempty⟩ :
        ∃ parentChildren : List (input.LocalizedRerootCursor carrierFuel),
          input.localizedRerootChildren? parentCursor = some parentChildren ∧
            parentChildren ≠ [] :=
      ⟨input.executableLocalizedRerootChildren parentCursor,
        input.localizedRerootChildren?_eq_some_executable parentCursor,
        parentNonemptyExec⟩
    have parentChildrenAt :
        input.localizedRerootChildren? (frame.cursorAt parentIndex) =
          some parentChildren := by
      rw [parentCursorAtEq]
      exact parentChildrenComputed
    have parentNodeCurrent :
        (frame.cursorAt parentIndex).occurrence.1.node.current? = some parentAtom := by
      rw [parentCursorAtEq]
      exact parentCurrent
    have otherNodeCurrent :
        (frame.cursorAt otherIndex).occurrence.1.node.current? = some parentAtom := by
      show otherCursor.occurrence.1.node.current? = some parentAtom
      rw [nodeExtend]
      rfl
    have rootLabelsEqual :
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          (frame.cursorAt parentIndex).occurrence.1.node)).1 =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel
          (frame.cursorAt otherIndex).occurrence.1.node)).1 := by
      have parentLabel := MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current
        input.moleculeGraph (frame.cursorAt parentIndex).occurrence.1.node parentAtom
        parentNodeCurrent
      have otherLabel := MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current
        input.moleculeGraph (frame.cursorAt otherIndex).occurrence.1.node parentAtom
        otherNodeCurrent
      exact parentLabel.trans otherLabel.symm
    have backwardTie := sourceObservation2013_backwardParent_tie
      target.1.node certificate.parent.1.node current parentAtom tail copyIndex
      targetHistory (certificate.parent_provenance input)
      (certificate.parent_history_nodup input) parentHistory copyPositive
    have rootTie :
        sourceObservation2013 (frame.cursorAt parentIndex).occurrence.1.node =
          sourceObservation2013 (frame.cursorAt otherIndex).occurrence.1.node := by
      have parentObservation :
          sourceObservation2013 (frame.cursorAt parentIndex).occurrence.1.node =
            sourceObservation2013 certificate.parent.1.node := by
        rw [parentCursorAtEq]
      have otherObservation :
          sourceObservation2013 (frame.cursorAt otherIndex).occurrence.1.node =
            sourceObservation2013 (target.1.node.extend parentAtom copyIndex) := by
        show sourceObservation2013 otherCursor.occurrence.1.node =
          sourceObservation2013 (target.1.node.extend parentAtom copyIndex)
        rw [nodeExtend]
      rw [parentObservation, otherObservation]
      exact backwardTie.symm
    obtain ⟨parentKeyFirst, otherKeyFirst, parentBuiltFirst, otherBuiltFirst,
      _parentHeadFirst, _otherHeadFirst, _headsEqualFirst, _rule1aGtFirst,
      constitutionalGtFirst, cumulativeEqFirst⟩ :=
      input.source2013_terminalRight_nonemptyLeft_separation_despite_rootTie
        stage first (frame.cursorAt parentIndex) (frame.cursorAt otherIndex)
        parentValid otherValid parentChildren parentChildrenAt parentChildrenNonempty
        otherTerminal rootLabelsEqual rootTie
    obtain ⟨parentKeySecond, otherKeySecond, parentBuiltSecond, otherBuiltSecond,
      _parentHeadSecond, _otherHeadSecond, _headsEqualSecond, _rule1aGtSecond,
      constitutionalGtSecond, cumulativeEqSecond⟩ :=
      input.source2013_terminalRight_nonemptyLeft_separation_despite_rootTie
        stage second (frame.cursorAt parentIndex) (frame.cursorAt otherIndex)
        parentValid otherValid parentChildren parentChildrenAt parentChildrenNonempty
        otherTerminal rootLabelsEqual rootTie
    refine ⟨parentKeyFirst, otherKeyFirst, parentKeySecond, otherKeySecond,
      parentBuiltFirst, otherBuiltFirst, parentBuiltSecond, otherBuiltSecond,
      ?_, ?_, ?_⟩
    · rw [cumulativeEqFirst, constitutionalGtFirst]
      intro contradiction
      cases contradiction
    · rw [cumulativeEqSecond, constitutionalGtSecond]
      intro contradiction
      cases contradiction
    · rw [cumulativeEqFirst, cumulativeEqSecond, constitutionalGtFirst, constitutionalGtSecond]
  · -- Every other executable child: strict Rule-1b head separation.
    have observationNe := sourceObservation2013_extend_ne_realParent input
      target.1.node certificate.parent.1.node current parentAtom tail next copyIndex
      targetHistory (certificate.parent_provenance input) parentHistory copyFacts.1
      nextParent
    obtain ⟨parentKeyFirst, parentBuiltFirst⟩ :=
      input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
        stage (fun node => some (sourceObservation2013 node)) first
        (frame.cursorAt parentIndex) parentValid (fun _ => rfl)
    obtain ⟨otherKeyFirst, otherBuiltFirst⟩ :=
      input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
        stage (fun node => some (sourceObservation2013 node)) first
        (frame.cursorAt otherIndex) otherValid (fun _ => rfl)
    obtain ⟨parentKeySecond, parentBuiltSecond⟩ :=
      input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
        stage (fun node => some (sourceObservation2013 node)) second
        (frame.cursorAt parentIndex) parentValid (fun _ => rfl)
    obtain ⟨otherKeySecond, otherBuiltSecond⟩ :=
      input.buildLocalizedObservedCumulativeRule45Key?_exists_of_total_observer_at_twice
        stage (fun node => some (sourceObservation2013 node)) second
        (frame.cursorAt otherIndex) otherValid (fun _ => rfl)
    have parentHeadFirst :=
      input.buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
        stage first (2 * (carrierFuel + 1)) (frame.cursorAt parentIndex)
        parentKeyFirst parentBuiltFirst
    have otherHeadFirst :=
      input.buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
        stage first (2 * (carrierFuel + 1)) (frame.cursorAt otherIndex)
        otherKeyFirst otherBuiltFirst
    have parentHeadSecond :=
      input.buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
        stage second (2 * (carrierFuel + 1)) (frame.cursorAt parentIndex)
        parentKeySecond parentBuiltSecond
    have otherHeadSecond :=
      input.buildLocalizedObservedCumulativeRule45Key?_source2013_rule1b_head
        stage second (2 * (carrierFuel + 1)) (frame.cursorAt otherIndex)
        otherKeySecond otherBuiltSecond
    have parentObservation :
        sourceObservation2013 (frame.cursorAt parentIndex).occurrence.1.node =
          sourceObservation2013 certificate.parent.1.node := by
      rw [parentCursorAtEq]
    have otherObservation :
        sourceObservation2013 (frame.cursorAt otherIndex).occurrence.1.node =
          sourceObservation2013 (target.1.node.extend next copyIndex) := by
      show sourceObservation2013 otherCursor.occurrence.1.node =
        sourceObservation2013 (target.1.node.extend next copyIndex)
      rw [nodeExtend]
    have observationsNe :
        sourceObservation2013 (frame.cursorAt parentIndex).occurrence.1.node ≠
          sourceObservation2013 (frame.cursorAt otherIndex).occurrence.1.node := by
      rw [parentObservation, otherObservation]
      exact fun same => observationNe same.symm
    have firstResult := input.builtCumulativeKeys_constitutionalCompare_ne_eq
      parentKeyFirst otherKeyFirst parentHeadFirst otherHeadFirst observationsNe
    have secondResult := input.builtCumulativeKeys_constitutionalCompare_ne_eq
      parentKeySecond otherKeySecond parentHeadSecond otherHeadSecond observationsNe
    have parentObservableEq :=
      input.totalizedObserver2013_constitutionalObservable_eq_of_builds
        stage first second (2 * (carrierFuel + 1)) (frame.cursorAt parentIndex)
        parentBuiltFirst parentBuiltSecond
    have otherObservableEq :=
      input.totalizedObserver2013_constitutionalObservable_eq_of_builds
        stage first second (2 * (carrierFuel + 1)) (frame.cursorAt otherIndex)
        otherBuiltFirst otherBuiltSecond
    have comparisonEq :=
      input.totalizedObserver2013_constitutionalCompare_eq_of_observables
        parentKeyFirst otherKeyFirst parentKeySecond otherKeySecond
        parentObservableEq otherObservableEq
    refine ⟨parentKeyFirst, otherKeyFirst, parentKeySecond, otherKeySecond,
      parentBuiltFirst, otherBuiltFirst, parentBuiltSecond, otherBuiltSecond,
      ?_, ?_, ?_⟩
    · rw [firstResult.2]
      exact firstResult.1
    · rw [secondResult.2]
      exact secondResult.1
    · rw [firstResult.2, secondResult.2]
      exact comparisonEq

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.totalizedObserver2013_constitutionalObservable_eq_of_builds
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.totalizedObserver2013_constitutionalCompare_eq_of_observables
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.totalizedObserver2013_actualFrame_parentVersusEveryOtherChild_comparison_readerIndependent
