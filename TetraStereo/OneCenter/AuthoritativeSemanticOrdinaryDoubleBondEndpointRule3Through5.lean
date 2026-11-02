import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondTopologyPartition
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Occurrence-exact Rules 1a--5 endpoint ranking for ordinary double bonds

The earlier source spatial-unit selector compared constitutional Rules 1a--2 keys only. This
module builds the stronger endpoint frame from the certified occurrence machinery: physical
Rule-3 units are cancelled once across the whole endpoint frame, then compound Rules 4a--5 are
appended to every candidate. No tetrahedral four-ligand assumption is used here.
-/

/-- The source occurrence-tree root at an arbitrary atom. -/
noncomputable def aromaticCanonicalRootOccurrence
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (atom : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOccurrence carrierFuel := by
  classical
  refine ⟨
    { root := atom
      address := []
      node := OfficialCIPNode.root atom
      remaining := carrierFuel + 1 }, ?_⟩
  apply (source.mem_aromaticCanonicalOccurrences_iff carrierFuel _).mpr
  exact DeclarativeAromaticCanonicalOccurrenceSubtree.subtreeRoot
    [] (carrierFuel + 1) (OfficialCIPNode.root atom)

/-- Root children that are real represented substituents other than the double-bond partner. -/
def AromaticCanonicalOrdinaryDoubleBondEndpointCursorCandidate
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) : Prop :=
  cursor ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalRootOccurrence carrierFuel endpoint
        previous? := none } ∧
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    ∃ reference : source.AromaticCanonicalAtom,
      cursor.occurrence.1.node.current? = some reference ∧ reference ≠ partner

/-- Finite exact endpoint-candidate cursor list. Duplicate and phantom provenance is excluded;
multiple-bond duplicate nodes remain inside branch expansion, where CIP requires them. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondEndpointCursors
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom) :
    List (source.AromaticCanonicalRerootCursor carrierFuel) := by
  classical
  exact (source.aromaticCanonicalRerootChildren
    { occurrence := source.aromaticCanonicalRootOccurrence carrierFuel endpoint
      previous? := none }).filter fun cursor =>
        decide
          (cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
            ∃ reference : source.AromaticCanonicalAtom,
              cursor.occurrence.1.node.current? = some reference ∧ reference ≠ partner)

@[simp] theorem mem_aromaticCanonicalOrdinaryDoubleBondEndpointCursors_iff
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    cursor ∈ source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
        carrierFuel endpoint partner ↔
      source.AromaticCanonicalOrdinaryDoubleBondEndpointCursorCandidate
        carrierFuel endpoint partner cursor := by
  classical
  simp [aromaticCanonicalOrdinaryDoubleBondEndpointCursors,
    AromaticCanonicalOrdinaryDoubleBondEndpointCursorCandidate]

theorem aromaticCanonicalOrdinaryDoubleBondEndpointCursors_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom) :
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
      carrierFuel endpoint partner).Nodup := by
  classical
  exact (source.aromaticCanonicalRerootChildren_nodup
    { occurrence := source.aromaticCanonicalRootOccurrence carrierFuel endpoint
      previous? := none }).filter _

/-- Every endpoint candidate is a path-valid cursor in the exact finite occurrence tree. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointCursor_valid
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (present : cursor ∈ source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
      carrierFuel endpoint partner) :
    source.AromaticCanonicalRerootCursorValid cursor := by
  have candidate :=
    (source.mem_aromaticCanonicalOrdinaryDoubleBondEndpointCursors_iff
      carrierFuel endpoint partner cursor).mp present
  let rootCursor : source.AromaticCanonicalRerootCursor carrierFuel :=
    { occurrence := source.aromaticCanonicalRootOccurrence carrierFuel endpoint
      previous? := none }
  exact source.aromaticCanonicalRerootChild_valid rootCursor cursor
    (source.aromaticCanonicalRerootChildren rootCursor)
    (source.aromaticCanonicalRerootChildren_sound rootCursor) candidate.1

/-- Executable endpoint-wide frame of complete occurrence Rules 1a--5 keys. -/
structure AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) where
  cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)
  rule3Frame : source.AromaticCanonicalRule3CanonicalKeyFrame
  keys : List source.AromaticCanonicalOccurrenceRule3Through5Key

noncomputable def buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat) :
    Option (source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) := do
  let cursors := source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
    carrierFuel endpoint partner
  let rule3Frame ← source.buildAromaticCanonicalRule3CanonicalKeyFrame?
    evaluationFuel cursors
  let keys ← cursors.mapM
    (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
      rule3Frame.excluded
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
      view evaluationFuel)
  some { cursors, rule3Frame, keys }

/-- Independent meaning of a compiled endpoint frame. -/
def DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) : Prop :=
  frame.cursors = source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
      carrierFuel endpoint partner ∧
    source.DeclarativeAromaticCanonicalRule3CanonicalKeyFrame
      evaluationFuel frame.cursors frame.rule3Frame ∧
    List.Forall₂
      (source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
        frame.rule3Frame.excluded
        (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
        view evaluationFuel)
      frame.cursors frame.keys

private theorem mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound_for_endpoint
    (source : AuthoritativeChemicalInput) {carrierFuel evaluationFuel : Nat}
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors keys,
      cursors.mapM
          (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view evaluationFuel) = some keys →
      List.Forall₂
        (source.DeclarativeAromaticCanonicalOccurrenceRule3Through5KeyExcept
          excluded target view evaluationFuel) cursors keys
  | [], keys, computed => by
      simp at computed
      subst keys
      exact .nil
  | cursor :: cursors, keys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed :
          source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            excluded target view evaluationFuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
                excluded target view evaluationFuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              exact .cons
                (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound
                  excluded target view evaluationFuel cursor head headComputed)
                (source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound_for_endpoint
                  excluded target view cursors tail tailComputed)

/-- Every compiled endpoint frame has exact source cursors, common physical Rule-3 cancellation,
and independently justified compound Rules 4a--5 keys. -/
theorem buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?_sound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel)
    (computed :
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
        carrierFuel endpoint partner view evaluationFuel = some frame) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel endpoint partner view evaluationFuel frame := by
  unfold buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame? at computed
  let cursors := source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
    carrierFuel endpoint partner
  cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
      evaluationFuel cursors with
  | none => simp [cursors, rule3Computed] at computed
  | some rule3Frame =>
      cases keysComputed : cursors.mapM
          (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
            rule3Frame.excluded
            (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
            view evaluationFuel) with
      | none => simp [cursors, rule3Computed, keysComputed] at computed
      | some keys =>
          simp [cursors, rule3Computed, keysComputed] at computed
          subst frame
          exact ⟨rfl,
            source.buildAromaticCanonicalRule3CanonicalKeyFrame?_sound
              evaluationFuel cursors rule3Frame rule3Computed,
            source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_sound_for_endpoint
              rule3Frame.excluded
              (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
              view cursors keys keysComputed⟩

/-- Chemical dependency evidence retained by endpoint-frame totality: all occurrence Rule-3
observations are resolved and the exhaustive physical-unit cancellation has a unique outcome. -/
structure AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom) : Prop where
  spatiallyResolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel
  topologyUnambiguous : ∀ rawKeys,
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
        carrierFuel endpoint partner).mapM
        (source.buildAromaticCanonicalUncancelledRule3SpatialKey?
          (2 * (carrierFuel + 1))) = some rawKeys →
      source.AromaticCanonicalRule3TopologyUnambiguous rawKeys

private theorem exists_mapM_rule3Through5Except_at_twice_of_valid_for_endpoint
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (resolved : source.AromaticCanonicalRule3SpatiallyResolved carrierFuel)
    (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, source.AromaticCanonicalRerootCursorValid cursor) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
          excluded target view (2 * (carrierFuel + 1))) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, valid => by
      obtain ⟨rule3, rule3Computed⟩ :=
        source.exists_buildAromaticCanonicalRule3SpatialKeyExcept?_at_twice
          resolved excluded cursor (valid cursor (by simp))
      obtain ⟨rule45, rule45Computed⟩ :=
        source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
          target view cursor (valid cursor (by simp))
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_rule3Through5Except_at_twice_of_valid_for_endpoint
          resolved excluded target view cursors
          (fun child present => valid child (by simp [present]))
      refine ⟨{ rule3, rule45 } :: keys, ?_⟩
      simp [buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?,
        rule3Computed, rule45Computed, keysComputed]

/-- At the proved finite occurrence bound, chemical dependency evidence is sufficient for the
complete endpoint Rules-1a--5 frame to exist; recursive-builder success is not assumed. -/
theorem exists_buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame_at_twice
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (resolved :
      source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5DependenciesResolved
        carrierFuel endpoint partner) :
    ∃ frame,
      source.buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?
        carrierFuel endpoint partner view (2 * (carrierFuel + 1)) = some frame := by
  let cursors := source.aromaticCanonicalOrdinaryDoubleBondEndpointCursors
    carrierFuel endpoint partner
  have valid : ∀ cursor ∈ cursors,
      source.AromaticCanonicalRerootCursorValid cursor := by
    intro cursor present
    exact source.aromaticCanonicalOrdinaryDoubleBondEndpointCursor_valid
      carrierFuel endpoint partner cursor present
  obtain ⟨rule3Frame, rule3Computed⟩ :=
    source.exists_buildAromaticCanonicalRule3CanonicalKeyFrame?_at_twice
      resolved.spatiallyResolved cursors valid resolved.topologyUnambiguous
  obtain ⟨keys, keysComputed⟩ :=
    source.exists_mapM_rule3Through5Except_at_twice_of_valid_for_endpoint
      resolved.spatiallyResolved rule3Frame.excluded
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint)
      view cursors valid
  exact ⟨{ cursors, rule3Frame, keys }, by
    simp [buildAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame?,
      cursors, rule3Computed, keysComputed]⟩

/-- Candidate cursor paired positionally with its common-policy Rules 1a--5 key. -/
abbrev AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat) :=
  source.AromaticCanonicalRerootCursor carrierFuel ×
    source.AromaticCanonicalOccurrenceRule3Through5Key

/-- Descriptor-facing comparison of two arbitrary endpoint keys.  The ordinary lawful ordering
is retained together with the Rule-5 enantiomorphic (`pseudo`) bit.  A Rule-3 decision can never
set that bit; Rule 5 is consulted only after Rule 3 ties. -/
noncomputable def compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalOccurrenceRule3Through5Key) :
    ConstitutionalRule5Comparison :=
  match source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      left.rule3 right.rule3 with
  | .lt => { ordering := .lt, pseudo := false }
  | .gt => { ordering := .gt, pseudo := false }
  | .eq => source.compareAromaticCanonicalRerootCompoundThroughRule5
      left.rule45 right.rule45

/-- The ordering projection of the descriptor-facing endpoint comparison is exactly the lawful
lexicographic Rules-1a--5 key comparator used by endpoint ranking. -/
theorem compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_ordering
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalOccurrenceRule3Through5Key) :
    (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
      left right).ordering =
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys left right := by
  unfold compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
    compareAromaticCanonicalOccurrenceRule3Through5Keys
  generalize rule3Comparison :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        left.rule3 right.rule3 = outcome
  cases outcome <;>
    simp [compareLex, Ordering.byKey, rule3Comparison,
      source.compareAromaticCanonicalRerootCompoundThroughRule5_ordering]

/-- A positive pseudo/enantiomorphic bit can arise only after the complete Rule-3 keys tie. -/
theorem compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5_pseudo_implies_rule3_eq
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalOccurrenceRule3Through5Key)
    (pseudo : (source.compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5
      left right).pseudo = true) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      left.rule3 right.rule3 = Ordering.eq := by
  unfold compareAromaticCanonicalOrdinaryDoubleBondEndpointThroughRule5 at pseudo
  generalize compared :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        left.rule3 right.rule3 = outcome at pseudo
  cases outcome <;> simp_all

def AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame.ranked
    {source : AuthoritativeChemicalInput} {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) :
    List (source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate carrierFuel) :=
  frame.cursors.zip frame.keys

/-- Executable strict-seniority test under the exact lexicographic Rules 1a--5 comparator. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate
      carrierFuel)
    (ranked : List
      (source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate carrierFuel)) : Bool := by
  classical
  exact ranked.all fun other =>
    if other.1 = candidate.1 then true
    else source.compareAromaticCanonicalOccurrenceRule3Through5Keys
      candidate.2 other.2 == Ordering.gt

/-- Independent strict maximum in one endpoint-wide common-policy frame. -/
def DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (ranked : List
      (source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate carrierFuel))
    (candidate : source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate
      carrierFuel) : Prop :=
  candidate ∈ ranked ∧
    ∀ other, other ∈ ranked → other.1 ≠ candidate.1 →
      source.compareAromaticCanonicalOccurrenceRule3Through5Keys
        candidate.2 other.2 = Ordering.gt

theorem aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll_eq_true_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (candidate : source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate
      carrierFuel)
    (ranked : List
      (source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate carrierFuel)) :
    source.aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll
        candidate ranked = true ↔
      ∀ other, other ∈ ranked → other.1 ≠ candidate.1 →
        source.compareAromaticCanonicalOccurrenceRule3Through5Keys
          candidate.2 other.2 = Ordering.gt := by
  rw [aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll,
    List.all_eq_true]
  constructor
  · intro checked other present different
    have comparison := checked other present
    simpa [different] using comparison
  · intro strict other present
    by_cases same : other.1 = candidate.1
    · simp [same]
    · simpa [same] using strict other present same

/-- Select a represented endpoint strict maximum, if one exists. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) :
    Option (source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate
      carrierFuel) :=
  frame.ranked.find? fun candidate =>
    source.aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll
      candidate frame.ranked

private theorem isSome_find?_iff_exists_mem_eq_true
    {α : Type*} (predicate : α → Bool) : ∀ items : List α,
    (items.find? predicate).isSome = true ↔
      ∃ item ∈ items, predicate item = true
  | [] => by simp
  | item :: items => by
      by_cases checked : predicate item = true
      · simp [List.find?, checked]
      · have falseChecked : predicate item = false :=
          Bool.eq_false_of_not_eq_true checked
        simp [List.find?, falseChecked,
          isSome_find?_iff_exists_mem_eq_true predicate items]

/-- Exact success readiness: selection succeeds exactly when the compiled common-policy frame
has an independently stated strict Rules-1a--5 maximum. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate?_isSome_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) :
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate? frame).isSome = true ↔
      ∃ candidate,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
          frame.ranked candidate := by
  rw [aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate?,
    isSome_find?_iff_exists_mem_eq_true]
  constructor
  · rintro ⟨candidate, present, checked⟩
    exact ⟨candidate, present,
      (source.aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll_eq_true_iff
        candidate frame.ranked).mp checked⟩
  · rintro ⟨candidate, present, strict⟩
    exact ⟨candidate, present,
      (source.aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll_eq_true_iff
        candidate frame.ranked).mpr strict⟩

/-- A concrete selected candidate is a member of the compiled frame and satisfies the independent
strict Rules-1a--5 seniority relation. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel)
    (candidate : source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate
      carrierFuel)
    (computed : source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate? frame =
      some candidate) :
    source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
      frame.ranked candidate := by
  have checked :
      source.aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll
        candidate frame.ranked = true :=
    @List.find?_some _
      (fun item =>
        source.aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll
          item frame.ranked)
      candidate frame.ranked computed
  have present : candidate ∈ frame.ranked := by
    rcases (List.find?_eq_some_iff_append.mp computed).2 with
      ⟨before, after, identity, _⟩
    rw [identity]
    simp
  exact ⟨present,
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointStrictlyOutranksAll_eq_true_iff
      candidate frame.ranked).mp checked⟩

/-- Every declaratively senior endpoint cursor names a real represented reference distinct from
the double-bond partner. -/
theorem exists_reference_of_declarativeEndpointStrictlySenior
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel)
    (frameDerived :
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel endpoint partner view evaluationFuel frame)
    (candidate : source.AromaticCanonicalOrdinaryDoubleBondEndpointRankedCandidate
      carrierFuel)
    (senior :
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
        frame.ranked candidate) :
    ∃ reference : source.AromaticCanonicalAtom,
      candidate.1.occurrence.1.node.current? = some reference ∧ reference ≠ partner := by
  have cursorPresent : candidate.1 ∈ frame.cursors :=
    (List.of_mem_zip senior.1).1
  rw [frameDerived.1] at cursorPresent
  exact ((source.mem_aromaticCanonicalOrdinaryDoubleBondEndpointCursors_iff
    carrierFuel endpoint partner candidate.1).mp cursorPresent).2.2

/-- Reference atom carried by the selected exact occurrence cursor. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) : Option source.AromaticCanonicalAtom := do
  let candidate ←
    source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate? frame
  candidate.1.occurrence.1.node.current?

theorem aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel)
    (reference : source.AromaticCanonicalAtom) :
    source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? frame =
        some reference ↔
      ∃ candidate,
        source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate? frame =
          some candidate ∧
        candidate.1.occurrence.1.node.current? = some reference := by
  unfold aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference?
  cases computed :
      source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate? frame <;>
    simp

/-- A reference emitted from a declaratively derived frame is exactly its independent strict
senior and is distinct from the double-bond partner. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference?_sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (endpoint partner : source.AromaticCanonicalAtom)
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel endpoint))
    (evaluationFuel : Nat)
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel)
    (frameDerived :
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
        carrierFuel endpoint partner view evaluationFuel frame)
    (reference : source.AromaticCanonicalAtom)
    (computed :
      source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference? frame =
        some reference) :
    ∃ candidate,
      source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
          frame.ranked candidate ∧
        candidate.1.occurrence.1.node.current? = some reference ∧
        reference ≠ partner := by
  obtain ⟨candidate, seniorComputed, current⟩ :=
    (source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorReference?_eq_some_iff
      frame reference).mp computed
  have senior :=
    source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate?_sound
      frame candidate seniorComputed
  obtain ⟨actualReference, actualCurrent, different⟩ :=
    source.exists_reference_of_declarativeEndpointStrictlySenior
      endpoint partner view evaluationFuel frame frameDerived candidate senior
  rw [current] at actualCurrent
  injection actualCurrent with identity
  subst actualReference
  exact ⟨candidate, senior, current, different⟩

/-- Exact fail-closed theorem: endpoint selection returns none exactly when no represented
strict Rules-1a--5 maximum exists. -/
theorem aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate?_eq_none_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (frame : source.AromaticCanonicalOrdinaryDoubleBondEndpointRule3Through5Frame
      carrierFuel) :
    source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate? frame = none ↔
      ¬∃ candidate,
        source.DeclarativeAromaticCanonicalOrdinaryDoubleBondEndpointStrictlySenior
          frame.ranked candidate := by
  rw [← source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate?_isSome_iff]
  cases source.aromaticCanonicalOrdinaryDoubleBondEndpointSeniorCandidate? frame <;> simp

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
