import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteUnifiedAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondExactReadinessCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact completeness boundary for the canonical Rules 4b/5 partition

The fixed root-key frame and initial-partition builders are characterized exactly by recursive,
builder-free canonical normal forms.  Those normal forms lift unconditionally through branch,
scheduled-molecule, concrete, and source-independent provision judgments.  Earlier conditional
reverse-transport and tied-permutation scaffolding has been removed; it is superseded by these
exact normal-form equivalences.
-/

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-! ## Unconditional exact canonical normal form -/

/-- Builder-free recursive normal form of the four-root Rules-1a--5 frame.  Unlike the broad
declarative relation, every recursive Rule-3 and Rules-4a--5 component uses the exact canonical
relation already proved equivalent to its fixed production compiler. -/
def CanonicalAromaticCanonicalRule3Through5RootKeyFrame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel) : Prop :=
  roots.length = 4 ∧ frame.rootsLength = roots.length ∧
    source.CanonicalAromaticCanonicalRule3CanonicalKeyFrame
      fuel roots frame.rule3Frame ∧
    List.Forall₂
      (source.CanonicalAromaticCanonicalOccurrenceRule3Through5KeyExcept
        frame.rule3Frame.excluded target view fuel) roots frame.keys ∧
    frame.keys.length = 4

/-- The fixed root-frame builder is exactly its builder-free canonical recursive normal form. -/
theorem buildAromaticCanonicalRule3Through5RootKeyFrame?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (frame : source.AromaticCanonicalRule3Through5RootKeyFrame carrierFuel) :
    source.buildAromaticCanonicalRule3Through5RootKeyFrame?
        target view fuel roots = some frame ↔
      source.CanonicalAromaticCanonicalRule3Through5RootKeyFrame
        target view fuel roots frame := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalRule3Through5RootKeyFrame? at computed
    by_cases rootsLength : roots.length = 4
    · cases rule3Computed : source.buildAromaticCanonicalRule3CanonicalKeyFrame?
          fuel roots with
      | none => simp [rootsLength, rule3Computed] at computed
      | some rule3Frame =>
          cases keysComputed : roots.mapM
              (source.buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?
                rule3Frame.excluded target view fuel) with
          | none => simp [rootsLength, rule3Computed, keysComputed] at computed
          | some keys =>
              by_cases keysLength : keys.length = 4
              · simp [rootsLength, rule3Computed, keysComputed, keysLength] at computed
                subst frame
                exact ⟨rootsLength, rootsLength.symm,
                  (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
                    fuel roots rule3Frame).mp rule3Computed,
                  (source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
                    rule3Frame.excluded target view fuel roots keys).mp
                    keysComputed,
                  keysLength⟩
              · simp [rootsLength, rule3Computed, keysComputed, keysLength] at computed
    · simp [rootsLength] at computed
  · rintro ⟨rootsLength, frameRootsLength, rule3Canonical, keysCanonical, keysLength⟩
    have rule3Computed :=
      (source.buildAromaticCanonicalRule3CanonicalKeyFrame?_eq_some_iff_canonical
        fuel roots frame.rule3Frame).mpr rule3Canonical
    have keysComputed :=
      (source.mapM_buildAromaticCanonicalOccurrenceRule3Through5KeyExcept?_eq_some_iff_canonical
        frame.rule3Frame.excluded target view fuel roots frame.keys).mpr
        keysCanonical
    cases frame
    simp_all [buildAromaticCanonicalRule3Through5RootKeyFrame?]

/-- Builder-free canonical normal form of the complete initial partition.  The frame is exact,
and the representative is the single lawful production sort rather than an arbitrary descending
permutation. -/
def CanonicalAromaticCanonicalRule3Through5InitialPartition
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) : Prop :=
  source.CanonicalAromaticCanonicalRule3Through5RootKeyFrame
      target view fuel roots partition.frame ∧
    partition.sorted = sortAromaticCanonicalRule3Through5RootPositions
      (source.compareAromaticCanonicalRule3Through5RootPositions partition.frame)
      (List.finRange 4) ∧
    partition.adjacent = aromaticCanonicalRule3Through5RootAdjacent
      (source.compareAromaticCanonicalRule3Through5RootPositions partition.frame)
      partition.sorted

/-- Initial-partition production is exactly the canonical builder-free normal form. -/
theorem buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel) :
    source.buildAromaticCanonicalRule3Through5InitialPartition?
        target view fuel roots = some partition ↔
      source.CanonicalAromaticCanonicalRule3Through5InitialPartition
        target view fuel roots partition := by
  constructor
  · intro computed
    unfold buildAromaticCanonicalRule3Through5InitialPartition? at computed
    cases frameComputed : source.buildAromaticCanonicalRule3Through5RootKeyFrame?
        target view fuel roots with
    | none => simp [frameComputed] at computed
    | some frame =>
        simp [frameComputed] at computed
        subst partition
        exact ⟨
          (source.buildAromaticCanonicalRule3Through5RootKeyFrame?_eq_some_iff_canonical
            target view fuel roots frame).mp frameComputed,
          rfl, rfl⟩
  · rintro ⟨frameCanonical, sortedEq, adjacentEq⟩
    have frameComputed :=
      (source.buildAromaticCanonicalRule3Through5RootKeyFrame?_eq_some_iff_canonical
        target view fuel roots partition.frame).mpr frameCanonical
    unfold buildAromaticCanonicalRule3Through5InitialPartition?
    simp [frameComputed, ← sortedEq, ← adjacentEq]

/-- Canonical normal forms refine the existing broad independent partition semantics. -/
theorem CanonicalAromaticCanonicalRule3Through5InitialPartition.sound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (canonical : source.CanonicalAromaticCanonicalRule3Through5InitialPartition
      target view fuel roots partition) :
    source.DeclarativeAromaticCanonicalRule3Through5InitialPartition
      target view fuel roots partition :=
  source.buildAromaticCanonicalRule3Through5InitialPartition?_sound
    target view fuel roots partition
    ((source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
      target view fuel roots partition).mpr canonical)

/-- Builder-free canonical-complete meaning of one Rules-1a--6 branch descriptor. -/
def AromaticCanonicalRule3Through6CanonicalCompleteDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS) : Prop :=
  ∃ (rootsLength : roots.length = 4)
      (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel),
    source.CanonicalAromaticCanonicalRule3Through5InitialPartition
        target view fuel roots partition ∧
      source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition ∧
      source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
        target view fuel roots partition parity descriptor

/-- The executable branch judgment and builder-free canonical-complete mathematics coincide
without assumptions. -/
theorem aromaticCanonicalRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS) :
    source.AromaticCanonicalRule3Through6ExecutableDescriptorJudgment
        center target view fuel roots parity descriptor ↔
      source.AromaticCanonicalRule3Through6CanonicalCompleteDescriptorJudgment
        center target view fuel roots parity descriptor := by
  constructor <;> rintro ⟨rootsLength, partition, partitionExact, topology, branch⟩
  · exact ⟨rootsLength, partition,
      (source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
        target view fuel roots partition).mp partitionExact,
      topology, branch⟩
  · exact ⟨rootsLength, partition,
      (source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
        target view fuel roots partition).mpr partitionExact,
      topology, branch⟩

/-- Canonical-complete branch mathematics implies the existing broad complete judgment. -/
theorem AromaticCanonicalRule3Through6CanonicalCompleteDescriptorJudgment.complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS)
    (judged : source.AromaticCanonicalRule3Through6CanonicalCompleteDescriptorJudgment
      center target view fuel roots parity descriptor) :
    source.AromaticCanonicalRule3Through6CompleteDescriptorJudgment
      center target view fuel roots parity descriptor := by
  rcases judged with ⟨rootsLength, partition, canonical, topology, branch⟩
  exact ⟨rootsLength, partition, canonical.sound, topology, branch⟩

/-- Molecule-level canonical-complete meaning.  Root and parity perception retain their exact
fixed evaluator equations; the strategically disputed initial partition is replaced by the
builder-free canonical recursive normal form above. -/
def AromaticCanonicalScheduledRule3Through6CanonicalCompleteDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) : Prop :=
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  ∃ roots parity,
    source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
      source.aromaticCanonicalRerootFrameParity? roots = some parity ∧
      source.AromaticCanonicalRule3Through6CanonicalCompleteDescriptorJudgment center.1 target
        (source.aromaticCanonicalDependencyView state target)
        ruleFuel roots parity descriptor

/-- Exact scheduled execution is unconditionally the canonical-complete molecule judgment. -/
theorem aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) :
    source.AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
        semantics ruleFuel center descriptor ↔
      source.AromaticCanonicalScheduledRule3Through6CanonicalCompleteDescriptorJudgment
        semantics ruleFuel center descriptor := by
  unfold AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
    AromaticCanonicalScheduledRule3Through6CanonicalCompleteDescriptorJudgment
  dsimp only
  constructor <;> rintro ⟨roots, parity, rootsComputed, parityComputed, finalJudgment⟩
  · exact ⟨roots, parity, rootsComputed, parityComputed,
      (source.aromaticCanonicalRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
        center.1 _ _ ruleFuel roots parity descriptor).mp finalJudgment⟩
  · exact ⟨roots, parity, rootsComputed, parityComputed,
      (source.aromaticCanonicalRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
        center.1 _ _ ruleFuel roots parity descriptor).mpr finalJudgment⟩

/-- Parameter-free canonical-complete meaning of the concrete production endpoint. -/
def AromaticCanonicalConcreteRule3Through6CanonicalCompleteDescriptorJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) : Prop :=
  source.AromaticCanonicalScheduledRule3Through6CanonicalCompleteDescriptorJudgment
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center descriptor

/-- The actual concrete endpoint is unconditionally exact for the builder-free canonical
whole-molecule judgment. -/
theorem aromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) :
    source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
        carrierFuel ruleFuel center descriptor ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalCompleteDescriptorJudgment
        carrierFuel ruleFuel center descriptor :=
  source.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center descriptor

/-- Canonical-complete concrete mathematics entails the existing broader complete judgment and
its independently proved causal fixed-point model. -/
theorem AromaticCanonicalConcreteRule3Through6CanonicalCompleteDescriptorJudgment.complete
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS)
    (judged : source.AromaticCanonicalConcreteRule3Through6CanonicalCompleteDescriptorJudgment
      carrierFuel ruleFuel center descriptor) :
    source.AromaticCanonicalConcreteRule3Through6DescriptorJudgment
      carrierFuel ruleFuel center descriptor := by
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  rcases judged with ⟨roots, parity, rootsComputed, parityComputed, finalJudgment⟩
  refine ⟨⟨roots, parity, ?_, ?_, finalJudgment.complete⟩, ?_⟩
  · exact (source.aromaticCanonicalOccurrenceLigandFrame?_eq_some_iff target roots).mp
      rootsComputed
  · exact (source.aromaticCanonicalRerootFrameParity?_eq_some_iff roots parity).mp
      parityComputed
  · exact source.aromaticCanonicalScheduledAuxiliaryState_cipModel semantics


end AuthoritativeChemicalInput
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRule3Through5RootKeyFrame?_eq_some_iff_canonical
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.CanonicalAromaticCanonicalRule3Through5InitialPartition.sound
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment_iff_canonicalComplete
assert_kernel_only
  TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalConcreteRule3Through6CanonicalCompleteDescriptorJudgment.complete
