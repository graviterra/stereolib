import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3CanonicalFrameExact

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput

/-!
A reusable callback-parameterized two-pass Rule-3 frame. The callback's independent optional
outcome relation has a proved exact correspondence with its reader. This is a library parameter,
not an inhabited production-source claim. Raw recursive keys discover physical units; the existing
topology resolver selects one existing global exclusion policy; every actual cursor is recompiled
under that same policy. Exclusion observes first, so an unresolved outer None stays unresolved.
The returned record is shared with the existing frame API, while the canonical judgment below
retains the supplied callback's own recursive meaning. Production integration and concrete planar
source instantiation remain separate. This module neither reads nor manufactures spatial points.
-/

structure Rule3Observer (source : AuthoritativeChemicalInput) where
  observe : OfficialCIPNode source.AromaticCanonicalAtom → Option (Option source.AromaticCanonicalRule3SpatialNodeResult)
  NodeOutcome : OfficialCIPNode source.AromaticCanonicalAtom → Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  nodeExact : ∀ node outcome, observe node = some outcome ↔ NodeOutcome node outcome
variable {source : AuthoritativeChemicalInput} (observer : Rule3Observer source)
noncomputable def observeExcept (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option (Option source.AromaticCanonicalRule3SpatialNodeResult) := by
  classical
  exact match observer.observe node with
  | none => none
  | some none => some none
  | some (some result) =>
      if result.physicalUnitId ∈ excluded then some none else some (some result)
def NodeOutcomeExcept (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    Option source.AromaticCanonicalRule3SpatialNodeResult → Prop
  | none => observer.NodeOutcome node none ∨
      ∃ result, observer.NodeOutcome node (some result) ∧ result.physicalUnitId ∈ excluded
  | some result => observer.NodeOutcome node (some result) ∧ result.physicalUnitId ∉ excluded
variable (excluded : List source.AromaticCanonicalRule3PhysicalUnitId)
  (node : OfficialCIPNode source.AromaticCanonicalAtom) (result : source.AromaticCanonicalRule3SpatialNodeResult)
/-- Exclusion cannot turn a failed base observation into successful absence. -/
theorem observeExcept_preserves_unresolved
    (unresolved : observer.observe node = none) : observeExcept observer excluded node = none := by
  simp [observeExcept, unresolved]
theorem observeExcept_preserves_negative
    (negative : observer.observe node = some none) :
    observeExcept observer excluded node = some none := by simp [observeExcept, negative]
theorem observeExcept_cancels_resolved
    (resolved : observer.observe node = some (some result))
    (cancelled : result.physicalUnitId ∈ excluded) :
    observeExcept observer excluded node = some none := by simp [observeExcept, resolved, cancelled]
theorem observeExcept_retains_resolved
    (resolved : observer.observe node = some (some result))
    (retained : result.physicalUnitId ∉ excluded) :
    observeExcept observer excluded node = some (some result) := by
  simp [observeExcept, resolved, retained]
theorem observeExcept_eq_some_iff
    (outcome : Option source.AromaticCanonicalRule3SpatialNodeResult) :
    observeExcept observer excluded node = some outcome ↔
      NodeOutcomeExcept observer excluded node outcome := by
  classical
  constructor
  · intro computed
    unfold observeExcept at computed
    cases originalComputed : observer.observe node with
    | none => simp [originalComputed] at computed
    | some original =>
        cases original with
        | none =>
            simp [originalComputed] at computed
            subst outcome
            exact Or.inl ((observer.nodeExact node none).mp originalComputed)
        | some result =>
            have positive := (observer.nodeExact node (some result)).mp originalComputed
            by_cases cancelled : result.physicalUnitId ∈ excluded
            · simp [originalComputed, cancelled] at computed
              subst outcome
              exact Or.inr ⟨result, positive, cancelled⟩
            · simp [originalComputed, cancelled] at computed
              subst outcome
              exact ⟨positive, cancelled⟩
  · intro derived
    cases outcome with
    | none =>
        rcases derived with negative | ⟨result, positive, cancelled⟩
        · simp [observeExcept, (observer.nodeExact node none).mpr negative]
        · simp [observeExcept, (observer.nodeExact node (some result)).mpr positive, cancelled]
    | some result =>
        rcases derived with ⟨positive, retained⟩
        simp [observeExcept, (observer.nodeExact node (some result)).mpr positive, retained]
noncomputable def excludedObserver (excluded : List source.AromaticCanonicalRule3PhysicalUnitId) :
    Rule3Observer source :=
  { observe := observeExcept observer excluded
    NodeOutcome := NodeOutcomeExcept observer excluded
    nodeExact := observeExcept_eq_some_iff observer excluded }
/-- List exactness derived from the public generic single-key theorem. -/
theorem buildObserverKeyList_eq_some_iff {carrierFuel : Nat} (fuel : Nat) :
    ∀ (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
      (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey),
      cursors.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe fuel) =
          some keys ↔
        source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
          observer.NodeOutcome fuel cursors keys
  | [], keys => by
      constructor
      · intro computed
        simp at computed
        subst keys
        exact .nil fuel
      · intro derived
        cases derived
        rfl
  | cursor :: cursors, keys => by
      constructor
      · intro computed
        rw [List.mapM_cons] at computed
        cases headComputed : source.buildAromaticCanonicalRule3SpatialKeyWith?
            observer.observe fuel cursor with
        | none => simp [headComputed] at computed
        | some head =>
            cases tailComputed : cursors.mapM
                (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe fuel) with
            | none => simp [headComputed, tailComputed] at computed
            | some tail =>
                simp [headComputed, tailComputed] at computed
                subst keys
                exact .cons
                  ((source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                    observer.observe observer.NodeOutcome observer.nodeExact fuel cursor head).mp headComputed)
                  ((buildObserverKeyList_eq_some_iff fuel cursors tail).mp tailComputed)
      · intro derived
        cases derived with
        | cons head tail =>
            rw [List.mapM_cons,
              (source.buildAromaticCanonicalRule3SpatialKeyWith?_eq_some_iff_canonical
                observer.observe observer.NodeOutcome observer.nodeExact fuel _ _).mpr head,
              (buildObserverKeyList_eq_some_iff fuel _ _).mpr tail]
            rfl
noncomputable def buildRule3ObserverFrame? {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    Option source.AromaticCanonicalRule3CanonicalKeyFrame := do
  let rawKeys ← cursors.mapM (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe fuel)
  let resolution ← source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys
  let excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
  let keys ← cursors.mapM
    (source.buildAromaticCanonicalRule3SpatialKeyWith? (observeExcept observer excluded) fuel)
  some { rawKeys, resolution, excluded, keys }
def CanonicalRule3ObserverFrame {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) : Prop :=
  source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
      observer.NodeOutcome fuel cursors frame.rawKeys ∧
    source.DeclarativeAromaticCanonicalRule3PhysicalTopologyResolution frame.rawKeys frame.resolution ∧
    frame.excluded = source.aromaticCanonicalRule3ExcludedPhysicalUnits frame.rawKeys frame.resolution ∧
    source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
      (NodeOutcomeExcept observer frame.excluded) fuel cursors frame.keys
theorem buildRule3ObserverFrame?_eq_some_iff {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) (frame : source.AromaticCanonicalRule3CanonicalKeyFrame) :
    buildRule3ObserverFrame? observer fuel cursors = some frame ↔
      CanonicalRule3ObserverFrame observer fuel cursors frame := by
  constructor
  · intro computed
    unfold buildRule3ObserverFrame? at computed
    cases rawComputed : cursors.mapM
        (source.buildAromaticCanonicalRule3SpatialKeyWith? observer.observe fuel) with
    | none => simp [rawComputed] at computed
    | some rawKeys =>
        cases resolutionComputed : source.aromaticCanonicalRule3PhysicalTopologyResolution? rawKeys with
        | none => simp [rawComputed, resolutionComputed] at computed
        | some resolution =>
            let excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
            cases keysComputed : cursors.mapM
                (source.buildAromaticCanonicalRule3SpatialKeyWith? (observeExcept observer excluded) fuel) with
            | none => simp [rawComputed, resolutionComputed, excluded, keysComputed] at computed
            | some keys =>
                simp [rawComputed, resolutionComputed, excluded, keysComputed] at computed
                subst frame
                exact ⟨(buildObserverKeyList_eq_some_iff observer fuel cursors rawKeys).mp rawComputed,
                  (source.aromaticCanonicalRule3PhysicalTopologyResolution?_eq_some_iff_declarative
                    rawKeys resolution).mp resolutionComputed, rfl,
                  (buildObserverKeyList_eq_some_iff (excludedObserver observer excluded)
                    fuel cursors keys).mp keysComputed⟩
  · rintro ⟨rawDerived, resolutionDerived, excludedEq, keysDerived⟩
    have rawComputed := (buildObserverKeyList_eq_some_iff observer fuel cursors frame.rawKeys).mpr rawDerived
    have resolutionComputed :=
      (source.aromaticCanonicalRule3PhysicalTopologyResolution?_eq_some_iff_declarative
        frame.rawKeys frame.resolution).mpr resolutionDerived
    have keysComputed := (buildObserverKeyList_eq_some_iff (excludedObserver observer frame.excluded)
      fuel cursors frame.keys).mpr keysDerived
    have selectedKeysComputed : cursors.mapM
        (source.buildAromaticCanonicalRule3SpatialKeyWith?
          (observeExcept observer (source.aromaticCanonicalRule3ExcludedPhysicalUnits
            frame.rawKeys frame.resolution)) fuel) = some frame.keys := by
      rw [← excludedEq]
      exact keysComputed
    have frameEq :
        ({ rawKeys := frame.rawKeys
           resolution := frame.resolution
           excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits frame.rawKeys frame.resolution
           keys := frame.keys } : source.AromaticCanonicalRule3CanonicalKeyFrame) = frame := by
      cases frame
      simp_all
    simpa [buildRule3ObserverFrame?, rawComputed, resolutionComputed, selectedKeysComputed] using
      congrArg (fun value => (some value : Option source.AromaticCanonicalRule3CanonicalKeyFrame)) frameEq
theorem buildRule3ObserverFrame?_sound {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (computed : buildRule3ObserverFrame? observer fuel cursors = some frame) :
    CanonicalRule3ObserverFrame observer fuel cursors frame :=
  (buildRule3ObserverFrame?_eq_some_iff observer fuel cursors frame).mp computed
theorem buildRule3ObserverFrame?_complete {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (canonical : CanonicalRule3ObserverFrame observer fuel cursors frame) :
    buildRule3ObserverFrame? observer fuel cursors = some frame :=
  (buildRule3ObserverFrame?_eq_some_iff observer fuel cursors frame).mpr canonical
theorem buildRule3ObserverFrame?_eq_none_iff {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    buildRule3ObserverFrame? observer fuel cursors = none ↔
      ¬∃ frame, CanonicalRule3ObserverFrame observer fuel cursors frame := by
  constructor
  · intro absent ⟨frame, derived⟩
    have computed := (buildRule3ObserverFrame?_eq_some_iff observer fuel cursors frame).mpr derived
    rw [absent] at computed
    contradiction
  · intro absent
    cases computed : buildRule3ObserverFrame? observer fuel cursors with
    | none => rfl
    | some frame => exact False.elim (absent ⟨frame,
        (buildRule3ObserverFrame?_eq_some_iff observer fuel cursors frame).mp computed⟩)
private theorem canonicalList_length {carrierFuel fuel : Nat}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
      observer.NodeOutcome fuel cursors keys) : keys.length = cursors.length :=
  match derived with
  | .nil _ => rfl
  | .cons _ tail => congrArg Nat.succ (canonicalList_length tail)
theorem CanonicalRule3ObserverFrame.keys_length {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (derived : CanonicalRule3ObserverFrame observer fuel cursors frame) :
    frame.keys.length = cursors.length :=
  canonicalList_length (excludedObserver observer frame.excluded) derived.2.2.2
theorem CanonicalRule3ObserverFrame.global_exclusion_policy {carrierFuel : Nat} (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)) (frame : source.AromaticCanonicalRule3CanonicalKeyFrame)
    (derived : CanonicalRule3ObserverFrame observer fuel cursors frame) :
    frame.excluded = source.aromaticCanonicalRule3ExcludedPhysicalUnits frame.rawKeys frame.resolution :=
  derived.2.2.1
end TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
