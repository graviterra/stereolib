import TetraStereo.OneCenter.LocalizedShortCircuitWithChildren

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTie

/-- Successful optional mapping retains its slot-by-slot computations. -/
theorem mapM_forall₂ {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (computed : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => simpa using computed
  | cons x xs ih =>
      cases first : f x with
      | none => simp [List.mapM_cons, first] at computed
      | some y =>
          cases rest : xs.mapM f with
          | none => simp [List.mapM_cons, first, rest] at computed
          | some tail =>
              simp [List.mapM_cons, first, rest] at computed
              subst ys
              exact .cons first (ih tail rest)

private theorem pairwise_orientation {α : Type} {R : α → α → Prop} {xs : List α}
    (ordered : xs.Pairwise R) {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (ne : a ≠ b) :
    R a b ∨ R b a := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp ordered
      by_cases first : a = x
      · subst a
        have hb' : b ∈ xs := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
        exact Or.inl (head b hb')
      · have ha' : a ∈ xs := (List.mem_cons.mp ha).resolve_left first
        by_cases second : b = x
        · subst b
          exact Or.inr (head a ha')
        · have hb' : b ∈ xs := (List.mem_cons.mp hb).resolve_left second
          exact ih tail ha' hb'


/-- Two distinct tied slots cannot pass the all-pairs strict-order check. -/
theorem trackedOrder_none_of_tie
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (left right : Fin 4) (different : left ≠ right)
    (forward : input.compareLocalizedOccurrenceRule3Through5Keys
      (frame.keyAt left) (frame.keyAt right) = .eq)
    (backward : input.compareLocalizedOccurrenceRule3Through5Keys
      (frame.keyAt right) (frame.keyAt left) = .eq) :
    input.localizedNoDoubleTrackedOrderExec? frame = none := by
  cases computed : input.localizedNoDoubleTrackedOrderExec? frame with
  | none => rfl
  | some tracked =>
      have sound := input.safeLocalizedOccurrenceRule3Through5TrackedOrder?_sound frame tracked
        ((input.localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?
          frame).symm.trans computed)
      have leftMem : left ∈ tracked.highestFirst := sound.2.1.mem_iff.mpr (by simp)
      have rightMem : right ∈ tracked.highestFirst := sound.2.1.mem_iff.mpr (by simp)
      rcases pairwise_orientation sound.2.2 leftMem rightMem different with strict | strict
      · rw [input.compareLocalizedOccurrenceRule3Through5At_ordering, forward] at strict
        cases strict
      · rw [input.compareLocalizedOccurrenceRule3Through5At_ordering, backward] at strict
        cases strict

/-- Exact Rule3 key of a terminal structural nonunit. -/
def rule3Key (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : input.LocalizedRerootRecursiveRule3SpatialKey :=
  { constitutional := input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
    observations := input.localizedRule3SpatialRootObservations none
    rule3 := input.localizedRule3SpatialRootPriorities none }

theorem rule3Key_computed (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) (terminal : readChildren cursor = some [])
    (nonunit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence)
    (budget : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec? input readChildren
      target view budget excluded cursor = some (rule3Key input cursor) := by
  cases budget with
  | zero =>
      simp [WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec?, terminal,
        (input.localizedRule3StructuralNodeExec_eq_some_none_iff cursor.occurrence).mpr nonunit,
        rule3Key]
  | succ budget =>
      simp [WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec?, terminal,
        localizedRule3ShortCircuitNodeWithExec?, localizedRule3OrdinaryRouteCertificate?,
        localizedDescriptorBearingRule3NodeWithExec?, nonunit, rule3Key]

/-- Exact terminal key data. Actual Rule45 compilation reads the supplied dependency view. -/
structure KeyCertificate (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) where
  key : input.LocalizedOccurrenceRule3Through5Key
  rule3 : ∀ budget excluded, WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec?
    input readChildren target view budget excluded cursor = some key.rule3
  rule45 : WithChildren.buildLocalizedRerootCompoundRule45KeyExec? input readChildren
    target view (localizedOccurrenceRerootEvaluationFuel fuel) cursor = some key.rule45

/-- Full compound comparison is computed only after the cursor has been checked terminal.
Source provenance is retained; the final comparison, rather than literal key equality, detects ties. -/
def keyCertificate? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) :
    Option (KeyCertificate input readChildren target view cursor) :=
  match terminal : readChildren cursor with
  | some [] =>
    if nonunit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge cursor.occurrence then
      match computed : WithChildren.buildLocalizedRerootCompoundRule45KeyExec? input readChildren
          target view (localizedOccurrenceRerootEvaluationFuel fuel) cursor with
      | none => none
      | some rule45 => some
          { key := { rule3 := rule3Key input cursor, rule45 }
            rule3 := rule3Key_computed input readChildren target view cursor terminal nonunit
            rule45 := computed }
    else none
  | _ => none


/-- The rebuilt pass supplies the keys actually compared, for its chosen exclusion set. -/
theorem frame_second_pass
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (cursors : List (input.LocalizedRerootCursor fuel))
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : WithChildren.buildLocalizedShortCircuitRule3FrameExec?
      input readChildren target view budget cursors = some frame) :
    ∃ predecessor, cursors.mapM (WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec?
      input readChildren target view predecessor frame.excluded) = some frame.keys := by
  cases budget with
  | zero => simp [WithChildren.buildLocalizedShortCircuitRule3FrameExec?] at computed
  | succ budget =>
      unfold WithChildren.buildLocalizedShortCircuitRule3FrameExec? at computed
      cases raw : cursors.mapM (WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec?
          input readChildren target view budget []) with
      | none => simp [raw] at computed
      | some rawKeys =>
          cases topology : input.localizedRule3CoupledTopologyResolutionExec? rawKeys with
          | none => simp [raw, topology] at computed
          | some resolution =>
              cases keys : cursors.mapM (WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec?
                  input readChildren target view budget
                    (input.localizedRule3CoupledExcludedPhysicalUnits rawKeys resolution)) with
              | none => simp [raw, topology, keys] at computed
              | some finalKeys =>
                  simp [raw, topology, keys] at computed
                  subst frame
                  exact ⟨budget, keys⟩

/-- A successful complete comparison frame retains both aligned compiler results. -/
theorem keyFrame_compilations
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame fuel)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (computed : WithChildren.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?
      input readChildren target view base = some frame) :
    (∃ predecessor, base.cursors.mapM (WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec?
      input readChildren target view predecessor frame.rule3Frame.excluded) = some frame.rule3Frame.keys) ∧
    base.cursors.mapM (WithChildren.buildLocalizedRerootCompoundRule45KeyExec? input readChildren
      target view (localizedOccurrenceRerootEvaluationFuel fuel)) = some frame.rule45Keys := by
  unfold WithChildren.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame? at computed
  cases rule3 : WithChildren.buildLocalizedShortCircuitRule3FrameExec? input readChildren
      target view (localizedDescriptorBearingRule3EvaluationFuel fuel) base.cursors with
  | none => simp [rule3] at computed
  | some result =>
      by_cases length3 : result.keys.length = 4
      · cases rule45 : base.cursors.mapM (WithChildren.buildLocalizedRerootCompoundRule45KeyExec?
            input readChildren target view (localizedOccurrenceRerootEvaluationFuel fuel)) with
        | none => simp [rule3, rule45] at computed
        | some results =>
            by_cases length45 : results.length = 4
            · simp [rule3, length3, rule45, length45] at computed
              subst frame
              exact ⟨frame_second_pass input readChildren target view _ base.cursors result rule3, rfl⟩
            · simp [rule3, rule45, length45] at computed
      · simp [rule3, length3] at computed

theorem KeyCertificate.aligned
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    {base : input.LocalizedOccurrenceFourLigandFrame fuel} {index : Fin 4}
    (certificate : KeyCertificate input readChildren target view (base.cursorAt index))
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (computed : WithChildren.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?
      input readChildren target view base = some frame) : frame.keyAt index = certificate.key := by
  obtain ⟨⟨budget, rule3⟩, rule45⟩ := keyFrame_compilations input readChildren target view base frame computed
  have baseLength := base.length_eq
  have length3 := frame.rule3Length
  have length45 := frame.rule45Length
  have slot3 := (mapM_forall₂ _ _ _ rule3).get
    (i := index.val) (by omega : index.val < base.cursors.length)
    (by omega : index.val < frame.rule3Frame.keys.length)
  have slot45 := (mapM_forall₂ _ _ _ rule45).get
    (i := index.val) (by omega : index.val < base.cursors.length)
    (by omega : index.val < frame.rule45Keys.length)
  change WithChildren.buildLocalizedRerootShortCircuitRule3KeyExec? input readChildren
    target view budget frame.rule3Frame.excluded (base.cursorAt index) = some (frame.keyAt index).rule3 at slot3
  change WithChildren.buildLocalizedRerootCompoundRule45KeyExec? input readChildren
    target view (localizedOccurrenceRerootEvaluationFuel fuel) (base.cursorAt index) =
      some (frame.keyAt index).rule45 at slot45
  have eq3 : (frame.keyAt index).rule3 = certificate.key.rule3 :=
    Option.some.inj (slot3.symm.trans (certificate.rule3 budget frame.rule3Frame.excluded))
  have eq45 : (frame.keyAt index).rule45 = certificate.key.rule45 :=
    Option.some.inj (slot45.symm.trans certificate.rule45)
  cases h : frame.keyAt index
  cases k : certificate.key
  simp_all

structure RefusalCertificate (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame fuel) where
  left : Fin 4
  right : Fin 4
  different : left ≠ right
  first : KeyCertificate input readChildren target view (base.cursorAt left)
  second : KeyCertificate input readChildren target view (base.cursorAt right)
  forward : input.compareLocalizedOccurrenceRule3Through5Keys first.key second.key = .eq
  backward : input.compareLocalizedOccurrenceRule3Through5Keys second.key first.key = .eq

theorem RefusalCertificate.tracked_none
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    {base : input.LocalizedOccurrenceFourLigandFrame fuel}
    (certificate : RefusalCertificate input readChildren target view base)
    (frame : input.LocalizedOccurrenceRule3Through5KeyFrame fuel)
    (computed : WithChildren.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?
      input readChildren target view base = some frame) :
    input.localizedNoDoubleTrackedOrderExec? frame = none := by
  apply trackedOrder_none_of_tie input frame certificate.left certificate.right certificate.different
  · rw [certificate.first.aligned frame computed, certificate.second.aligned frame computed]
    exact certificate.forward
  · rw [certificate.second.aligned frame computed, certificate.first.aligned frame computed]
    exact certificate.backward


/-- Check one pair against its real terminal keys and both actual comparison directions. -/
def pairCertificate? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame fuel) (left right : Fin 4) :
    Option (RefusalCertificate input readChildren target view base) :=
  if ordered : left < right then do
    let first ← keyCertificate? input readChildren target view (base.cursorAt left)
    let second ← keyCertificate? input readChildren target view (base.cursorAt right)
    if forward : input.compareLocalizedOccurrenceRule3Through5Keys first.key second.key = .eq then
      if backward : input.compareLocalizedOccurrenceRule3Through5Keys second.key first.key = .eq then
        some { left, right, different := ne_of_lt ordered, first, second, forward, backward }
      else none
    else none
  else none

def refusalCertificate? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame fuel) :
    Option (RefusalCertificate input readChildren target view base) :=
  (List.finRange 4).findSome? fun left =>
    (List.finRange 4).findSome? fun right =>
      pairCertificate? input readChildren target view base left right

theorem RefusalCertificate.descriptor_none
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel))}
    {target : input.LocalizedCIPOccurrence fuel} {view : input.LocalizedDependencyView target}
    {base : input.LocalizedOccurrenceFourLigandFrame fuel}
    (certificate : RefusalCertificate input readChildren target view base)
    (baseComputed : WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target = some base) :
    WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?
      input readChildren target view = none := by
  unfold WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?
    WithChildren.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases frameComputed : WithChildren.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?
          input readChildren target view base with
      | none => simp [baseComputed, frameComputed]
      | some frame => simp [baseComputed, frameComputed, certificate.tracked_none frame frameComputed]

/-- Exact early rejection of terminal ties. Other cases retain the complete existing evaluator. -/
def descriptor? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some _ =>
      match WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target with
      | none => none
      | some base =>
          match refusalCertificate? input readChildren target view base with
          | some _ => none
          | none => WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?
              input readChildren target view

theorem descriptor?_eq_original (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (readChildren : input.LocalizedRerootCursor fuel → Option (List (input.LocalizedRerootCursor fuel)))
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    descriptor? input readChildren target view =
      WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor? input readChildren target view := by
  unfold descriptor?
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none => simp [WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?,
      WithChildren.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?, centerComputed]
  | some center =>
      cases baseComputed : WithChildren.localizedNoDoubleFourLigandFrameExec? input readChildren target with
      | none => simp [WithChildren.localizedOccurrenceShortCircuitRule3Through5Descriptor?,
          WithChildren.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?, centerComputed, baseComputed]
      | some base =>
          cases refused : refusalCertificate? input readChildren target view base with
          | none => simp only [refused]
          | some certificate => simpa only [refused] using (certificate.descriptor_none baseComputed).symm

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput.TerminalTie
