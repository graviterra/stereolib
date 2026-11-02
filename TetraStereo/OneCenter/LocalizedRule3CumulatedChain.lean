import TetraStereo.OneCenter.LocalizedRule3OccurrenceReferenceCursor
import TetraStereo.OneCenter.P93AcyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Occurrence-local cumulated Rule-3 chains

P-93.4.2 distinguishes cumulenes by the number of consecutive double bonds.  A cumulene with an
odd number of double bonds is planar and uses the same terminal `E/Z` geometry as an extended
double bond; an even cumulene is axial and belongs to the `M/P` (or general `Rₐ/Sₐ`) path instead.

This module supplies the topology layer needed by the localized Rule-3 analyzer.  Starting with a
real order-two carrier occurrence whose parent is a terminal atom, it walks the unique real
order-two continuation until the opposite terminal.  The walk is fuel-bounded and fail-closed:
fuel exhaustion or a branched continuation refuses, while a terminal is proved by the exact
zipper neighborhood.  Only odd chains with more than one double bond are returned.
-/

namespace CertifiedLocalizedCIPInput

/-- A physical continuation of a cumulated-double-bond axis in the exact cut neighborhood. -/
def LocalizedRule3AxisContinuation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor child : input.LocalizedRerootCursor carrierFuel) : Prop :=
  cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    match cursor.occurrence.1.node.current?, child.occurrence.1.node.current? with
    | some current, some next => input.moleculeGraph.bond current next = 2
    | _, _ => False

/-- Exact physical axis continuations among an already certified zipper expansion. -/
noncomputable def localizedRule3AxisContinuationCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    List (input.LocalizedRerootCursor carrierFuel) := by
  classical
  exact children.filter fun child => decide (input.LocalizedRule3AxisContinuation cursor child)

@[simp] theorem mem_localizedRule3AxisContinuationCursors_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    child ∈ input.localizedRule3AxisContinuationCursors cursor children ↔
      child ∈ children ∧ input.LocalizedRule3AxisContinuation cursor child := by
  classical
  simp [localizedRule3AxisContinuationCursors]

/-- Compute the complete physical double-bond continuations of one cut cursor. -/
noncomputable def localizedRule3AxisContinuationCursors?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option (List (input.LocalizedRerootCursor carrierFuel)) := do
  let children ← input.localizedRerootChildren? cursor
  some (input.localizedRule3AxisContinuationCursors cursor children)

/-- Independent meaning of a returned continuation list. -/
def DeclarativeLocalizedRule3AxisContinuationCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (continuations : List (input.LocalizedRerootCursor carrierFuel)) : Prop :=
  ∃ children,
    input.localizedRerootChildren? cursor = some children ∧
      input.DeclarativeLocalizedRerootChildren cursor children ∧
      ∀ child, child ∈ continuations ↔
        child ∈ children ∧ input.LocalizedRule3AxisContinuation cursor child

/-- Continuation extraction accounts for exactly the real order-two zipper neighbors. -/
theorem localizedRule3AxisContinuationCursors?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (continuations : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRule3AxisContinuationCursors? cursor = some continuations) :
    input.DeclarativeLocalizedRule3AxisContinuationCursors cursor continuations := by
  unfold localizedRule3AxisContinuationCursors? at computed
  cases childrenComputed : input.localizedRerootChildren? cursor with
  | none => simp [childrenComputed] at computed
  | some children =>
      simp [childrenComputed] at computed
      subst continuations
      exact ⟨children, childrenComputed,
        input.localizedRerootChildren?_sound cursor children childrenComputed,
        fun child => input.mem_localizedRule3AxisContinuationCursors_iff
          cursor child children⟩

/-! ## Exhaustive local axis topology

The real-only continuation list above is useful for recursion, but it is not by itself a complete
physical-topology test.  In an official cyclic digraph, copy index zero of an edge returning to an
atom already in the branch is a `ringDuplicate`.  Such a node is a physical ring-closing edge,
whereas the positive copy indices of the same multiple bond are bookkeeping duplicates.  The
following layer keeps exactly that distinction. -/

/-- A physical order-two continuation is either an unvisited real atom or the zero-copy leaf that
closes a ring.  Multiple-bond copies and placeholders are not additional physical continuations. -/
def LocalizedRule3AxisPhysicalContinuation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor child : input.LocalizedRerootCursor carrierFuel) : Prop :=
  cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    LocalizedRule3PhysicalReferenceProvenance child.occurrence.1.node.provenance ∧
    match cursor.occurrence.1.node.current?, child.occurrence.1.node.current? with
    | some current, some next => input.moleculeGraph.bond current next = 2
    | _, _ => False

/-- Exact physical (real or ring-closing) order-two continuations in a certified zipper frame. -/
noncomputable def localizedRule3AxisPhysicalContinuationCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    List (input.LocalizedRerootCursor carrierFuel) := by
  classical
  exact children.filter fun child =>
    decide (input.LocalizedRule3AxisPhysicalContinuation cursor child)

@[simp] theorem mem_localizedRule3AxisPhysicalContinuationCursors_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor child : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel)) :
    child ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children ↔
      child ∈ children ∧ input.LocalizedRule3AxisPhysicalContinuation cursor child := by
  classical
  simp [localizedRule3AxisPhysicalContinuationCursors]

/-- Compute every physical order-two continuation, including a cyclic zero-copy closure. -/
noncomputable def localizedRule3AxisPhysicalContinuationCursors?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option (List (input.LocalizedRerootCursor carrierFuel)) := do
  let children ← input.localizedRerootChildren? cursor
  some (input.localizedRule3AxisPhysicalContinuationCursors cursor children)

/-- Independent exact meaning of the physical continuation list. -/
def DeclarativeLocalizedRule3AxisPhysicalContinuationCursors
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (continuations : List (input.LocalizedRerootCursor carrierFuel)) : Prop :=
  ∃ children,
    input.localizedRerootChildren? cursor = some children ∧
      input.DeclarativeLocalizedRerootChildren cursor children ∧
      ∀ child, child ∈ continuations ↔
        child ∈ children ∧ input.LocalizedRule3AxisPhysicalContinuation cursor child

/-- Physical continuation extraction is exact, including ring closures and excluding all
multiple-bond bookkeeping copies. -/
theorem localizedRule3AxisPhysicalContinuationCursors?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (continuations : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRule3AxisPhysicalContinuationCursors? cursor =
      some continuations) :
    input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors cursor continuations := by
  unfold localizedRule3AxisPhysicalContinuationCursors? at computed
  cases childrenComputed : input.localizedRerootChildren? cursor with
  | none => simp [childrenComputed] at computed
  | some children =>
      simp [childrenComputed] at computed
      subst continuations
      exact ⟨children, childrenComputed,
        input.localizedRerootChildren?_sound cursor children childrenComputed,
        fun child => input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
          cursor child children⟩

/-- Executable physical continuation extraction never repeats a cursor.  In particular,
two entries witnessing a branch are distinct physical continuations. -/
theorem localizedRule3AxisPhysicalContinuationCursors?_nodup
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (continuations : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRule3AxisPhysicalContinuationCursors? cursor =
      some continuations) : continuations.Nodup := by
  classical
  unfold localizedRule3AxisPhysicalContinuationCursors? at computed
  cases childrenComputed : input.localizedRerootChildren? cursor with
  | none => simp [childrenComputed] at computed
  | some children =>
      simp [childrenComputed] at computed
      subst continuations
      exact (input.localizedRerootChildren_nodup cursor children
        (input.localizedRerootChildren?_sound cursor children childrenComputed)).filter _

/-- Real recursion edges are exactly physical continuations whose child is a real atom. -/
theorem localizedRule3AxisContinuation_iff_physical_and_real
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor child : input.LocalizedRerootCursor carrierFuel) :
    input.LocalizedRule3AxisContinuation cursor child ↔
      input.LocalizedRule3AxisPhysicalContinuation cursor child ∧
        child.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  cases childProvenance : child.occurrence.1.node.provenance <;>
    simp [LocalizedRule3AxisContinuation, LocalizedRule3AxisPhysicalContinuation,
      LocalizedRule3PhysicalReferenceProvenance, childProvenance]

/-- Exhaustive shape of the physical order-two continuations at one cut cursor. -/
inductive LocalizedRule3AxisTopology
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  | terminal
  | linear (next : input.LocalizedRerootCursor carrierFuel)
  | ringClosure (closure : input.LocalizedRerootCursor carrierFuel)
  | branched
      (first second : input.LocalizedRerootCursor carrierFuel)
      (rest : List (input.LocalizedRerootCursor carrierFuel))

/-- Classify the complete physical continuation list.  The singleton provenance test is
fail-closed even though exact filtering proves that only `realAtom` or `ringDuplicate` can occur. -/
noncomputable def localizedRule3AxisTopology?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option (input.LocalizedRule3AxisTopology carrierFuel) := do
  let continuations ← input.localizedRule3AxisPhysicalContinuationCursors? cursor
  match continuations with
  | [] => some .terminal
  | [next] =>
      match next.occurrence.1.node.provenance with
      | .realAtom => some (.linear next)
      | .ringDuplicate _ => some (.ringClosure next)
      | .multipleBondDuplicate _ | .placeholder _ _ => none
  | first :: second :: rest => some (.branched first second rest)

/-- Independent proof-relevant meaning of every executable topology outcome. -/
inductive DeclarativeLocalizedRule3AxisTopology
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.LocalizedRule3AxisTopology carrierFuel → Prop
  | terminal
      (frame : input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors cursor []) :
      input.DeclarativeLocalizedRule3AxisTopology cursor .terminal
  | linear {next}
      (frame : input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors cursor [next])
      (real : next.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
      input.DeclarativeLocalizedRule3AxisTopology cursor (.linear next)
  | ringClosure {closure distance}
      (frame : input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors cursor [closure])
      (ring : closure.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance) :
      input.DeclarativeLocalizedRule3AxisTopology cursor (.ringClosure closure)
  | branched {first second rest}
      (frame : input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors
        cursor (first :: second :: rest))
      (distinct : first ≠ second) :
      input.DeclarativeLocalizedRule3AxisTopology cursor (.branched first second rest)

/-- Every returned topology is backed by the complete exact physical continuation frame. -/
theorem localizedRule3AxisTopology?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (topology : input.LocalizedRule3AxisTopology carrierFuel)
    (computed : input.localizedRule3AxisTopology? cursor = some topology) :
    input.DeclarativeLocalizedRule3AxisTopology cursor topology := by
  unfold localizedRule3AxisTopology? at computed
  cases continuationsComputed :
      input.localizedRule3AxisPhysicalContinuationCursors? cursor with
  | none => simp [continuationsComputed] at computed
  | some continuations =>
      cases continuations with
      | nil =>
          simp [continuationsComputed] at computed
          subst topology
          exact DeclarativeLocalizedRule3AxisTopology.terminal
            (input.localizedRule3AxisPhysicalContinuationCursors?_sound
              cursor [] continuationsComputed)
      | cons first rest =>
          cases rest with
          | nil =>
              cases provenance : first.occurrence.1.node.provenance <;>
                simp [continuationsComputed, provenance] at computed
              · subst topology
                exact DeclarativeLocalizedRule3AxisTopology.linear
                  (input.localizedRule3AxisPhysicalContinuationCursors?_sound
                    cursor [first] continuationsComputed) provenance
              · subst topology
                exact DeclarativeLocalizedRule3AxisTopology.ringClosure
                  (input.localizedRule3AxisPhysicalContinuationCursors?_sound
                    cursor [first] continuationsComputed) provenance
          | cons second more =>
              simp [continuationsComputed] at computed
              subst topology
              refine DeclarativeLocalizedRule3AxisTopology.branched
                (input.localizedRule3AxisPhysicalContinuationCursors?_sound
                  cursor (first :: second :: more) continuationsComputed) ?_
              have nodup := input.localizedRule3AxisPhysicalContinuationCursors?_nodup
                cursor (first :: second :: more) continuationsComputed
              intro equal
              exact (List.nodup_cons.mp nodup).1 (by simp [equal])

/-- The classifier is exhaustive on every certified cursor.  Its internal `Option` is only the
fail-closed implementation boundary; exact physical filtering rules out the invalid singleton
provenances that could return `none`. -/
theorem exists_localizedRule3AxisTopology
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∃ topology, input.localizedRule3AxisTopology? cursor = some topology := by
  classical
  obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
  have continuationsComputed :
      input.localizedRule3AxisPhysicalContinuationCursors? cursor =
        some (input.localizedRule3AxisPhysicalContinuationCursors cursor children) := by
    simp [localizedRule3AxisPhysicalContinuationCursors?, childrenComputed]
  unfold localizedRule3AxisTopology?
  rw [continuationsComputed]
  generalize continuationsIdentity :
      input.localizedRule3AxisPhysicalContinuationCursors cursor children = continuations
  cases continuations with
  | nil => exact ⟨.terminal, rfl⟩
  | cons first rest =>
      cases rest with
      | nil =>
          have firstPresent : first ∈
              input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
            rw [continuationsIdentity]
            simp
          have admissible :=
            (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
              cursor first children).mp firstPresent
          cases provenance : first.occurrence.1.node.provenance with
          | realAtom => exact ⟨.linear first, by simp [provenance]⟩
          | ringDuplicate distance => exact ⟨.ringClosure first, by simp [provenance]⟩
          | multipleBondDuplicate distance =>
              simp [LocalizedRule3AxisPhysicalContinuation,
                LocalizedRule3PhysicalReferenceProvenance, provenance] at admissible
          | placeholder kind distance =>
              simp [LocalizedRule3AxisPhysicalContinuation,
                LocalizedRule3PhysicalReferenceProvenance, provenance] at admissible
      | cons second more => exact ⟨.branched first second more, rfl⟩

namespace DeclarativeLocalizedRule3AxisTopology

/-- A certified terminal has no physical order-two neighbor at all; in particular a ring-closing
zero-copy edge can never be mistaken for a terminal. -/
theorem terminal_no_physical_continuation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3AxisTopology cursor .terminal) :
    ∃ children,
      input.localizedRerootChildren? cursor = some children ∧
      input.DeclarativeLocalizedRerootChildren cursor children ∧
      ∀ child ∈ children,
        ¬ input.LocalizedRule3AxisPhysicalContinuation cursor child := by
  cases derived with
  | terminal frame =>
      rcases frame with ⟨children, computed, exactChildren, membership⟩
      refine ⟨children, computed, exactChildren, ?_⟩
      intro child childPresent physical
      have : child ∈ ([] : List (input.LocalizedRerootCursor carrierFuel)) :=
        (membership child).mpr ⟨childPresent, physical⟩
      simp at this

/-- A certified ring outcome is a real order-two edge to a zero-copy ring duplicate, rather than
a multiple-bond bookkeeping duplicate. -/
theorem ringClosure_physical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor closure : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3AxisTopology cursor (.ringClosure closure)) :
    input.LocalizedRule3AxisPhysicalContinuation cursor closure ∧
      ∃ distance, closure.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.ringDuplicate distance := by
  cases derived with
  | ringClosure frame ring =>
      rcases frame with ⟨children, _computed, _exactChildren, membership⟩
      have characterized := (membership closure).mp (by simp)
      exact ⟨characterized.2, ⟨_, ring⟩⟩

end DeclarativeLocalizedRule3AxisTopology

/-- Independent finite path relation for a unique nonbranching cumulated axis. -/
inductive DeclarativeLocalizedRule3CumulatedAxisWalk
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    input.LocalizedRerootCursor carrierFuel →
      List (input.LocalizedRerootCursor carrierFuel) → Prop
  | terminal {cursor}
      (topology : input.DeclarativeLocalizedRule3AxisTopology cursor .terminal) :
      input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor [cursor]
  | step {cursor next tail}
      (topology : input.DeclarativeLocalizedRule3AxisTopology cursor (.linear next))
      (rest : input.DeclarativeLocalizedRule3CumulatedAxisWalk next tail) :
      input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor (cursor :: tail)

/-- Follow the unique physical double-bond continuation.  Zero fuel may certify a terminal, but
cannot truncate a still-continuing chain. -/
noncomputable def walkLocalizedRule3CumulatedAxis?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    Nat → input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel))
  | 0, cursor => do
      let topology ← input.localizedRule3AxisTopology? cursor
      match topology with
      | .terminal => some [cursor]
      | .linear _ | .ringClosure _ | .branched _ _ _ => none
  | fuel + 1, cursor => do
      let topology ← input.localizedRule3AxisTopology? cursor
      match topology with
      | .terminal => some [cursor]
      | .linear next => do
          let tail ← input.walkLocalizedRule3CumulatedAxis? fuel next
          some (cursor :: tail)
      | .ringClosure _ | .branched _ _ _ => none

/-- Every successful axis walk is a proof-relevant sequence of unique physical order-two steps
ending at a proved terminal; in particular, fuel can never turn a continuation into a terminal. -/
theorem walkLocalizedRule3CumulatedAxis?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ traversalFuel (cursor : input.LocalizedRerootCursor carrierFuel)
      (path : List (input.LocalizedRerootCursor carrierFuel)),
      input.walkLocalizedRule3CumulatedAxis? traversalFuel cursor = some path →
        input.DeclarativeLocalizedRule3CumulatedAxisWalk cursor path
  | 0, cursor, path, computed => by
      unfold walkLocalizedRule3CumulatedAxis? at computed
      cases topologyComputed : input.localizedRule3AxisTopology? cursor with
      | none => simp [topologyComputed] at computed
      | some topology =>
          cases topology with
          | terminal =>
              simp [topologyComputed] at computed
              subst path
              exact DeclarativeLocalizedRule3CumulatedAxisWalk.terminal
                (input.localizedRule3AxisTopology?_sound
                  cursor .terminal topologyComputed)
          | linear next | ringClosure next => simp [topologyComputed] at computed
          | branched first second rest => simp [topologyComputed] at computed
  | traversalFuel + 1, cursor, path, computed => by
      unfold walkLocalizedRule3CumulatedAxis? at computed
      cases topologyComputed : input.localizedRule3AxisTopology? cursor with
      | none => simp [topologyComputed] at computed
      | some topology =>
          cases topology with
          | terminal =>
              simp [topologyComputed] at computed
              subst path
              exact DeclarativeLocalizedRule3CumulatedAxisWalk.terminal
                (input.localizedRule3AxisTopology?_sound
                  cursor .terminal topologyComputed)
          | linear next =>
              cases tailComputed :
                  input.walkLocalizedRule3CumulatedAxis? traversalFuel next with
              | none => simp [topologyComputed, tailComputed] at computed
              | some tail =>
                  simp [topologyComputed, tailComputed] at computed
                  subst path
                  exact DeclarativeLocalizedRule3CumulatedAxisWalk.step
                    (input.localizedRule3AxisTopology?_sound
                      cursor (.linear next) topologyComputed)
                    (input.walkLocalizedRule3CumulatedAxis?_sound
                      traversalFuel next tail tailComputed)
          | ringClosure closure => simp [topologyComputed] at computed
          | branched first second rest => simp [topologyComputed] at computed

/-- A ring-closing continuation is never accepted as the end of an open terminal-to-terminal
axis, regardless of the remaining traversal fuel. -/
theorem walkLocalizedRule3CumulatedAxis?_eq_none_of_ringClosure
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (cursor closure : input.LocalizedRerootCursor carrierFuel)
    (topologyComputed : input.localizedRule3AxisTopology? cursor =
      some (.ringClosure closure)) :
    input.walkLocalizedRule3CumulatedAxis? traversalFuel cursor = none := by
  cases traversalFuel <;>
    simp [walkLocalizedRule3CumulatedAxis?, topologyComputed]

/-- A cursor with two or more physical order-two continuations is never linearized by choosing an
enumeration-first branch. -/
theorem walkLocalizedRule3CumulatedAxis?_eq_none_of_branched
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (cursor first second : input.LocalizedRerootCursor carrierFuel)
    (rest : List (input.LocalizedRerootCursor carrierFuel))
    (topologyComputed : input.localizedRule3AxisTopology? cursor =
      some (.branched first second rest)) :
    input.walkLocalizedRule3CumulatedAxis? traversalFuel cursor = none := by
  cases traversalFuel <;>
    simp [walkLocalizedRule3CumulatedAxis?, topologyComputed]

/-- Exhaustive parent-side shape of an oriented real order-two occurrence.  Ring closure and
branching are retained as distinct data instead of being conflated with failure or a terminal. -/
inductive LocalizedRule3CumulatedAxisEntry
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  | terminalStart
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
  | internal
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (previousAxis : input.LocalizedRerootCursor carrierFuel)
  | ringClosure
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (closure : input.LocalizedRerootCursor carrierFuel)
  | branched
      (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (first second : input.LocalizedRerootCursor carrierFuel)
      (rest : List (input.LocalizedRerootCursor carrierFuel))

/-- Authority-facing local topology case represented by an occurrence entry.  This erases all
production cursor data and retains only the independent P-93 continuation class. -/
def LocalizedRule3CumulatedAxisEntry.authorityTopologyCase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    input.LocalizedRule3CumulatedAxisEntry carrierFuel →
      BlueBookP93.Acyclic.LocalDoubleBondTopologyCase
  | .terminalStart _ => .terminal
  | .internal _ _ => .linearContinuation
  | .ringClosure _ _ => .cyclicClosure
  | .branched _ _ _ _ => .multipleContinuations

/-- Classify the parent side of an oriented order-two edge using the exact zipper frame. -/
noncomputable def localizedRule3CumulatedAxisEntry?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3CumulatedAxisEntry carrierFuel) := do
  let initial ← input.localizedRule3PhysicalEndpointCursorFrame? occurrence
  let topology ← input.localizedRule3AxisTopology? initial.leftCursor
  match topology with
  | .terminal => some (.terminalStart initial)
  | .linear previousAxis => some (.internal initial previousAxis)
  | .ringClosure closure => some (.ringClosure initial closure)
  | .branched first second rest => some (.branched initial first second rest)

/-- Independent parent-side classification. -/
inductive DeclarativeLocalizedRule3CumulatedAxisEntry
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.LocalizedRule3CumulatedAxisEntry carrierFuel → Prop
  | terminalStart {initial}
      (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame
        occurrence initial)
      (terminal : input.DeclarativeLocalizedRule3AxisTopology
        initial.leftCursor .terminal) :
      input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence (.terminalStart initial)
  | internal {initial previousAxis}
      (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame
        occurrence initial)
      (continuation : input.DeclarativeLocalizedRule3AxisTopology
        initial.leftCursor (.linear previousAxis)) :
      input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.internal initial previousAxis)
  | ringClosure {initial closure}
      (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame
        occurrence initial)
      (closureTopology : input.DeclarativeLocalizedRule3AxisTopology
        initial.leftCursor (.ringClosure closure)) :
      input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.ringClosure initial closure)
  | branched {initial first second rest}
      (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame
        occurrence initial)
      (branchTopology : input.DeclarativeLocalizedRule3AxisTopology
        initial.leftCursor (.branched first second rest)) :
      input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
        (.branched initial first second rest)

/-- The executable entry classifier preserves the physical edge and exact parent-side
continuation cardinality. -/
theorem localizedRule3CumulatedAxisEntry?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (entry : input.LocalizedRule3CumulatedAxisEntry carrierFuel)
    (computed : input.localizedRule3CumulatedAxisEntry? occurrence = some entry) :
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence entry := by
  unfold localizedRule3CumulatedAxisEntry? at computed
  cases initialComputed :
      input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none => simp [initialComputed] at computed
  | some initial =>
      cases topologyComputed : input.localizedRule3AxisTopology? initial.leftCursor with
      | none => simp [initialComputed, topologyComputed] at computed
      | some topology =>
          cases topology with
          | terminal =>
              simp [initialComputed, topologyComputed] at computed
              subst entry
              exact DeclarativeLocalizedRule3CumulatedAxisEntry.terminalStart
                (input.localizedRule3PhysicalEndpointCursorFrame?_sound
                  occurrence initial initialComputed)
                (input.localizedRule3AxisTopology?_sound
                  initial.leftCursor .terminal topologyComputed)
          | linear previousAxis =>
              simp [initialComputed, topologyComputed] at computed
              subst entry
              exact DeclarativeLocalizedRule3CumulatedAxisEntry.internal
                (input.localizedRule3PhysicalEndpointCursorFrame?_sound
                  occurrence initial initialComputed)
                (input.localizedRule3AxisTopology?_sound
                  initial.leftCursor (.linear previousAxis) topologyComputed)
          | ringClosure closure =>
              simp [initialComputed, topologyComputed] at computed
              subst entry
              exact DeclarativeLocalizedRule3CumulatedAxisEntry.ringClosure
                (input.localizedRule3PhysicalEndpointCursorFrame?_sound
                  occurrence initial initialComputed)
                (input.localizedRule3AxisTopology?_sound
                  initial.leftCursor (.ringClosure closure) topologyComputed)
          | branched first second rest =>
              simp [initialComputed, topologyComputed] at computed
              subst entry
              exact DeclarativeLocalizedRule3CumulatedAxisEntry.branched
                (input.localizedRule3PhysicalEndpointCursorFrame?_sound
                  occurrence initial initialComputed)
                (input.localizedRule3AxisTopology?_sound initial.leftCursor
                  (.branched first second rest) topologyComputed)

/-- Independent authority meaning of a local topology classification returned by production. -/
def DeclarativeLocalizedRule3AuthorityTopologyCase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (authorityCase : BlueBookP93.Acyclic.LocalDoubleBondTopologyCase) : Prop :=
  ∃ entry,
    input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence entry ∧
      entry.authorityTopologyCase = authorityCase

/-- The occurrence-level production classifier refines the independent P-93 local topology
taxonomy; in particular it cannot erase a ring closure or branch into a terminal chain case. -/
theorem localizedRule3CumulatedAxisEntry?_authorityTopologyCase_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (entry : input.LocalizedRule3CumulatedAxisEntry carrierFuel)
    (computed : input.localizedRule3CumulatedAxisEntry? occurrence = some entry) :
    input.DeclarativeLocalizedRule3AuthorityTopologyCase occurrence
      entry.authorityTopologyCase :=
  ⟨entry, input.localizedRule3CumulatedAxisEntry?_sound occurrence entry computed, rfl⟩

/-- A production ring-closure result lands in the independent cyclic-closure case, so downstream
refusal is an explicit cyclic-perception boundary rather than a false terminal classification. -/
theorem localizedRule3CumulatedAxisEntry?_ringClosure_authorityCase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (computed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure)) :
    input.DeclarativeLocalizedRule3AuthorityTopologyCase occurrence .cyclicClosure :=
  ⟨.ringClosure initial closure,
    input.localizedRule3CumulatedAxisEntry?_sound occurrence
      (.ringClosure initial closure) computed,
    rfl⟩

/-- A production branch result lands in the independent multiple-continuation case.  This is the
local fact that justifies per-bond rather than cumulative-chain routing. -/
theorem localizedRule3CumulatedAxisEntry?_branched_authorityCase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (first second : input.LocalizedRerootCursor carrierFuel)
    (rest : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.branched initial first second rest)) :
    input.DeclarativeLocalizedRule3AuthorityTopologyCase occurrence .multipleContinuations :=
  ⟨.branched initial first second rest,
    input.localizedRule3CumulatedAxisEntry?_sound occurrence
      (.branched initial first second rest) computed,
    rfl⟩

/-- Once the oriented physical order-two edge has been recovered, entry classification cannot
fail: terminal, internal, ring-closing, and branched cases exhaust the exact zipper topology. -/
theorem exists_localizedRule3CumulatedAxisEntry_of_physicalFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (initialComputed : input.localizedRule3PhysicalEndpointCursorFrame? occurrence =
      some initial) :
    ∃ entry, input.localizedRule3CumulatedAxisEntry? occurrence = some entry := by
  obtain ⟨topology, topologyComputed⟩ :=
    input.exists_localizedRule3AxisTopology initial.leftCursor
  cases topology with
  | terminal =>
      exact ⟨.terminalStart initial, by
        simp [localizedRule3CumulatedAxisEntry?, initialComputed, topologyComputed]⟩
  | linear previousAxis =>
      exact ⟨.internal initial previousAxis, by
        simp [localizedRule3CumulatedAxisEntry?, initialComputed, topologyComputed]⟩
  | ringClosure closure =>
      exact ⟨.ringClosure initial closure, by
        simp [localizedRule3CumulatedAxisEntry?, initialComputed, topologyComputed]⟩
  | branched first second rest =>
      exact ⟨.branched initial first second rest, by
        simp [localizedRule3CumulatedAxisEntry?, initialComputed, topologyComputed]⟩

/-- Complete terminal-to-terminal topology for an ordinary double bond or any nonbranching
cumulated chain.  `rightward.length` is exactly its physical double-bond count. -/
structure LocalizedRule3CumulatedEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel
  rightward : List (input.LocalizedRerootCursor carrierFuel)
  rightPartnerCursor : input.LocalizedRerootCursor carrierFuel
  rightCursor : input.LocalizedRerootCursor carrierFuel
  rightPartner : input.Atom
  right : input.Atom

def LocalizedRule3CumulatedEndpointCursorFrame.doubleBondCount
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel) : Nat :=
  frame.rightward.length

/-- Follow a terminal-start edge to the opposite terminal.  Branching and fuel truncation remain
fail-closed; parity is intentionally not classified at this layer. -/
noncomputable def localizedRule3CumulatedEndpointCursorFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel) := do
  let entry ← input.localizedRule3CumulatedAxisEntry? occurrence
  match entry with
  | .internal _ _ | .ringClosure _ _ | .branched _ _ _ _ => none
  | .terminalStart initial =>
      let rightward ← input.walkLocalizedRule3CumulatedAxis?
        traversalFuel initial.rightCursor
      match (initial.leftCursor :: rightward).reverse with
      | rightCursor :: rightPartnerCursor :: _rest => do
          let rightPartner ← rightPartnerCursor.occurrence.1.node.current?
          let right ← rightCursor.occurrence.1.node.current?
          some { initial
                 rightward
                 rightPartnerCursor
                 rightCursor
                 rightPartner
                 right }
      | _ => none

/-- Independent exact topology of a complete terminal-start axis frame. -/
def DeclarativeLocalizedRule3CumulatedEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
      (.terminalStart frame.initial) ∧
    input.DeclarativeLocalizedRule3CumulatedAxisWalk
      frame.initial.rightCursor frame.rightward ∧
    (∃ rest, (frame.initial.leftCursor :: frame.rightward).reverse =
      frame.rightCursor :: frame.rightPartnerCursor :: rest) ∧
    frame.rightPartnerCursor.occurrence.1.node.current? = some frame.rightPartner ∧
    frame.rightCursor.occurrence.1.node.current? = some frame.right

/-- Every returned general frame is the complete unique terminal-to-terminal occurrence path. -/
theorem localizedRule3CumulatedEndpointCursorFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3CumulatedEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3CumulatedEndpointCursorFrame?
      traversalFuel occurrence = some frame) :
    input.DeclarativeLocalizedRule3CumulatedEndpointCursorFrame occurrence frame := by
  unfold localizedRule3CumulatedEndpointCursorFrame? at computed
  cases entryComputed : input.localizedRule3CumulatedAxisEntry? occurrence with
  | none => simp [entryComputed] at computed
  | some entry =>
      cases entry with
      | internal initial previousAxis => simp [entryComputed] at computed
      | ringClosure initial closure => simp [entryComputed] at computed
      | branched initial first second rest => simp [entryComputed] at computed
      | terminalStart initial =>
          cases rightwardComputed : input.walkLocalizedRule3CumulatedAxis?
              traversalFuel initial.rightCursor with
          | none => simp [entryComputed, rightwardComputed] at computed
          | some rightward =>
              generalize reversedIdentity :
                  rightward.reverse ++ [initial.leftCursor] = reversed at computed
              cases reversed with
              | nil => simp [entryComputed, rightwardComputed, reversedIdentity] at computed
              | cons rightCursor rest =>
                  cases rest with
                  | nil => simp [entryComputed, rightwardComputed, reversedIdentity] at computed
                  | cons rightPartnerCursor reverseTail =>
                      cases rightPartnerComputed :
                          rightPartnerCursor.occurrence.1.node.current? with
                      | none =>
                          simp [entryComputed, rightwardComputed, reversedIdentity,
                            rightPartnerComputed] at computed
                      | some rightPartner =>
                          cases rightComputed : rightCursor.occurrence.1.node.current? with
                          | none =>
                              simp [entryComputed, rightwardComputed, reversedIdentity,
                                rightPartnerComputed, rightComputed] at computed
                          | some right =>
                              simp [entryComputed, rightwardComputed, reversedIdentity,
                                rightPartnerComputed, rightComputed] at computed
                              subst frame
                              exact ⟨
                                input.localizedRule3CumulatedAxisEntry?_sound occurrence
                                  (.terminalStart initial) entryComputed,
                                input.walkLocalizedRule3CumulatedAxis?_sound
                                  traversalFuel initial.rightCursor rightward
                                  rightwardComputed,
                                ⟨reverseTail, by simpa using reversedIdentity⟩,
                                rightPartnerComputed,
                                rightComputed⟩

/-- A maximal odd cumulene represented by terminal occurrence cursors and the complete rightward
axis walk.  The number of physical double bonds is `rightward.length`: adjoining the left cursor
adds one atom and therefore exactly that many consecutive axis edges. -/
structure LocalizedRule3OddCumuleneEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel
  rightward : List (input.LocalizedRerootCursor carrierFuel)
  rightPartnerCursor : input.LocalizedRerootCursor carrierFuel
  rightCursor : input.LocalizedRerootCursor carrierFuel
  rightPartner : input.Atom
  right : input.Atom

/-- Physical double-bond count of the extended unit. -/
def LocalizedRule3OddCumuleneEndpointCursorFrame.doubleBondCount
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel) : Nat :=
  frame.rightward.length

/-- Detect a maximal planar cumulene beginning at an oriented terminal double-bond occurrence.
Ordinary one-bond alkenes and even cumulenes are not accepted by this constructor. -/
noncomputable def localizedRule3OddCumuleneEndpointCursorFrame?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel) := do
  let initial ← input.localizedRule3PhysicalEndpointCursorFrame? occurrence
  let leftTopology ← input.localizedRule3AxisTopology? initial.leftCursor
  match leftTopology with
  | .terminal =>
      let rightward ← input.walkLocalizedRule3CumulatedAxis?
        traversalFuel initial.rightCursor
      match rightward.reverse with
      | rightCursor :: rightPartnerCursor :: _rest =>
          if _admissible : 1 < rightward.length ∧ Odd rightward.length then do
            let rightPartner ← rightPartnerCursor.occurrence.1.node.current?
            let right ← rightCursor.occurrence.1.node.current?
            some { initial
                   rightward
                   rightPartnerCursor
                   rightCursor
                   rightPartner
                   right }
          else none
      | _ => none
  | .linear _ | .ringClosure _ | .branched _ _ _ => none

/-- Independent molecule/carrier meaning of a returned odd-cumulene endpoint frame. -/
def DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel) : Prop :=
  input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence frame.initial ∧
    input.DeclarativeLocalizedRule3AxisTopology frame.initial.leftCursor .terminal ∧
    input.DeclarativeLocalizedRule3CumulatedAxisWalk
      frame.initial.rightCursor frame.rightward ∧
    (∃ rest, frame.rightward.reverse =
      frame.rightCursor :: frame.rightPartnerCursor :: rest) ∧
    frame.rightPartnerCursor.occurrence.1.node.current? = some frame.rightPartner ∧
    frame.rightCursor.occurrence.1.node.current? = some frame.right ∧
    1 < frame.doubleBondCount ∧
    Odd frame.doubleBondCount

/-- Every detected frame is one maximal nonbranching odd-double-bond unit with exact endpoint
cursors. -/
theorem localizedRule3OddCumuleneEndpointCursorFrame?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (traversalFuel : Nat)
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel)
    (computed : input.localizedRule3OddCumuleneEndpointCursorFrame?
      traversalFuel occurrence = some frame) :
    input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame := by
  unfold localizedRule3OddCumuleneEndpointCursorFrame? at computed
  cases initialComputed :
      input.localizedRule3PhysicalEndpointCursorFrame? occurrence with
  | none =>
      rw [initialComputed] at computed
      simp at computed
  | some initial =>
      rw [initialComputed] at computed
      simp at computed
      cases leftComputed : input.localizedRule3AxisTopology? initial.leftCursor with
      | none =>
          rw [leftComputed] at computed
          simp at computed
      | some leftTopology =>
          rw [leftComputed] at computed
          simp at computed
          cases leftTopology with
          | terminal =>
            simp only at computed
            cases rightwardComputed : input.walkLocalizedRule3CumulatedAxis?
                traversalFuel initial.rightCursor with
            | none =>
                rw [rightwardComputed] at computed
                simp at computed
            | some rightward =>
                rw [rightwardComputed] at computed
                simp only [Option.bind_some] at computed
                generalize reversedIdentity : rightward.reverse = reversed at computed
                cases reversed with
                | nil => simp at computed
                | cons rightCursor rest =>
                    cases rest with
                    | nil => simp at computed
                    | cons rightPartnerCursor reverseTail =>
                        simp only at computed
                        by_cases admissible : 1 < rightward.length ∧ Odd rightward.length
                        · cases rightPartnerComputed :
                              rightPartnerCursor.occurrence.1.node.current? with
                          | none =>
                              rw [if_pos admissible, rightPartnerComputed] at computed
                              simp at computed
                          | some rightPartner =>
                              rw [if_pos admissible, rightPartnerComputed] at computed
                              simp only [Option.bind_some] at computed
                              cases rightComputed :
                                  rightCursor.occurrence.1.node.current? with
                              | none =>
                                  rw [rightComputed] at computed
                                  simp at computed
                              | some right =>
                                  rw [rightComputed] at computed
                                  simp only [Option.bind_some, Option.some.injEq] at computed
                                  subst frame
                                  exact ⟨
                                    input.localizedRule3PhysicalEndpointCursorFrame?_sound
                                      occurrence initial initialComputed,
                                    input.localizedRule3AxisTopology?_sound
                                      initial.leftCursor .terminal leftComputed,
                                    input.walkLocalizedRule3CumulatedAxis?_sound
                                      traversalFuel initial.rightCursor rightward
                                      rightwardComputed,
                                    ⟨reverseTail, reversedIdentity⟩,
                                    rightPartnerComputed,
                                    rightComputed,
                                    admissible.1,
                                    admissible.2⟩
                        · rw [if_neg admissible] at computed
                          simp at computed
          | linear next | ringClosure next => simp at computed
          | branched first second rest => simp at computed

namespace DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame

/-- The detected unit has an odd number of physical double bonds, as required for planar
extended-double-bond (`seqcis`/`seqtrans`) treatment. -/
theorem odd_bond_count
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel}
    (derived : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    Odd frame.doubleBondCount :=
  derived.2.2.2.2.2.2.2

/-- Even cumulenes cannot enter this Rule-3 planar-unit constructor. -/
theorem not_even_cumulene
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {frame : input.LocalizedRule3OddCumuleneEndpointCursorFrame carrierFuel}
    (derived : input.DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame occurrence frame) :
    ¬ Even frame.doubleBondCount :=
  Nat.not_even_iff_odd.mpr (odd_bond_count input derived)

end DeclarativeLocalizedRule3OddCumuleneEndpointCursorFrame

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
