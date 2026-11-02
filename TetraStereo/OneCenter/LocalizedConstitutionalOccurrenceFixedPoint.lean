import TetraStereo.OneCenter.LocalizedOccurrenceFixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Constitution-only seed model on the localized occurrence carrier

This is the first concrete instance of the localized fixed-point boundary.  At every real
tetrahedral occurrence it emits an uppercase `R/S` label exactly when Rules 1a--2 plus exact
spatial geometry determine that label without auxiliary descriptors.  Non-centers and unresolved
centers produce the resolved optional outcome `none`.

The declarative relation is defined independently through real-occurrence evidence and
`RuleMajorLocalizedTetrahedralDescriptor`; it includes explicit negative clauses for `none`.
The executable evaluator uses the molecular recognizer and seed pipeline.  Their complete
optional-outcome correspondence is proved below.  Because this base evaluator reads no auxiliary
state, its unique model consists precisely of the constitution-only uppercase seeds from which
later Rule-4c evaluation can proceed.
-/

namespace CertifiedLocalizedCIPInput

/-- Exact reference boundary for one constitution-only `R/S` seed. -/
theorem constitutionalSeedDescriptorAt?_eq_some_iff_reference
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (descriptor : RS) :
    input.constitutionalSeedDescriptorAt? center = some descriptor ↔
      RuleMajorLocalizedTetrahedralDescriptor input center
        emptyOfficialContext descriptor := by
  exact input.ruleMajorTetrahedralSpatialDescriptorAt?_eq_some_iff
    center emptyOfficialContext descriptor

/-- Independent complete optional-outcome semantics for constitution-only occurrence seeds. -/
def DeclarativeLocalizedConstitutionalOccurrenceOutcome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  (outcome = none ∧
      ((∀ center, ¬ input.RealTetrahedralCenterNode target.1.node center) ∨
        ∃ center, input.RealTetrahedralCenterNode target.1.node center ∧
          ∀ descriptor, ¬ RuleMajorLocalizedTetrahedralDescriptor input center
            emptyOfficialContext descriptor)) ∨
    ∃ center descriptor,
      input.RealTetrahedralCenterNode target.1.node center ∧
        outcome = some (.chiral descriptor) ∧
        RuleMajorLocalizedTetrahedralDescriptor input center
          emptyOfficialContext descriptor

/-- Executable constitution-only seed evaluator.  Its dependency view is intentionally unused:
these are precisely the uppercase base facts that precede auxiliary fixed-point evaluation. -/
def localizedConstitutionalOccurrenceRule
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (_view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel :=
  match input.localizedOccurrenceDescriptorCenter? target with
  | none => none
  | some center =>
      (input.constitutionalSeedDescriptorAt? center).map
        LocalizedTetrahedralRSPseudoDescriptor.chiral

/-- The independent complete outcome relation agrees with the executable seed evaluator for
every occurrence and every optional outcome. -/
theorem declarativeLocalizedConstitutionalOccurrenceOutcome_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) :
    input.DeclarativeLocalizedConstitutionalOccurrenceOutcome target outcome ↔
      input.localizedConstitutionalOccurrenceRule target
        (input.localizedDependencyView state target) = outcome := by
  constructor
  · intro derived
    rcases derived with unresolved | labeled
    · rcases unresolved with ⟨rfl, notCenter | centerUnresolved⟩
      · unfold localizedConstitutionalOccurrenceRule
        cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
        | none => rfl
        | some center =>
            have atNode :=
              (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mp
                centerComputed
            exact (notCenter center atNode).elim
      · rcases centerUnresolved with ⟨center, atNode, noDescriptor⟩
        have centerComputed :
            input.localizedOccurrenceDescriptorCenter? target = some center :=
          (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mpr atNode
        unfold localizedConstitutionalOccurrenceRule
        rw [centerComputed]
        cases descriptorComputed : input.constitutionalSeedDescriptorAt? center with
        | none => simp [descriptorComputed]
        | some descriptor =>
            have reference :=
              (input.constitutionalSeedDescriptorAt?_eq_some_iff_reference
                center descriptor).mp descriptorComputed
            exact (noDescriptor descriptor reference).elim
    · rcases labeled with ⟨center, descriptor, atNode, rfl, reference⟩
      have centerComputed :
          input.localizedOccurrenceDescriptorCenter? target = some center :=
        (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mpr atNode
      have descriptorComputed :
          input.constitutionalSeedDescriptorAt? center = some descriptor :=
        (input.constitutionalSeedDescriptorAt?_eq_some_iff_reference
          center descriptor).mpr reference
      simp [localizedConstitutionalOccurrenceRule, centerComputed, descriptorComputed]
  · intro computed
    unfold localizedConstitutionalOccurrenceRule at computed
    cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
    | none =>
        have outcomeNone : outcome = none := by simpa [centerComputed] using computed.symm
        apply Or.inl
        refine ⟨outcomeNone, Or.inl ?_⟩
        intro center atNode
        have present :=
          (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mpr atNode
        rw [centerComputed] at present
        contradiction
    | some center =>
        have atNode :=
          (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mp
            centerComputed
        cases descriptorComputed : input.constitutionalSeedDescriptorAt? center with
        | none =>
            have outcomeNone : outcome = none := by
              simpa [centerComputed, descriptorComputed] using computed.symm
            apply Or.inl
            refine ⟨outcomeNone, Or.inr ⟨center, atNode, ?_⟩⟩
            intro descriptor reference
            have present :=
              (input.constitutionalSeedDescriptorAt?_eq_some_iff_reference
                center descriptor).mpr reference
            rw [descriptorComputed] at present
            contradiction
        | some descriptor =>
            have outcomeLabel :
                outcome = some (.chiral descriptor) := by
              simpa [centerComputed, descriptorComputed] using computed.symm
            apply Or.inr
            exact ⟨center, descriptor, atNode, outcomeLabel,
              (input.constitutionalSeedDescriptorAt?_eq_some_iff_reference
                center descriptor).mp descriptorComputed⟩

/-- Concrete localized occurrence semantics for the constitution-only uppercase seed stratum. -/
noncomputable def localizedConstitutionalAuxiliarySemantics
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation := fun _state target outcome =>
    input.DeclarativeLocalizedConstitutionalOccurrenceOutcome target outcome
  executableRule := input.localizedConstitutionalOccurrenceRule
  derivation_executable_iff := by
    intro state target outcome
    exact input.declarativeLocalizedConstitutionalOccurrenceOutcome_iff
      state target outcome

/-- Direct executable seed state.  The arbitrary empty view is observationally irrelevant because
the constitution-only rule has no auxiliary inputs. -/
def localizedConstitutionalOccurrenceState
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryState fuel :=
  fun target => input.localizedConstitutionalOccurrenceRule target
    (fun _source _dependency => none)

/-- Exact positive characterization of the direct seed state. -/
theorem localizedConstitutionalOccurrenceState_eq_some_chiral_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (descriptor : RS) :
    input.localizedConstitutionalOccurrenceState fuel target =
        some (.chiral descriptor) ↔
      ∃ center,
        input.RealTetrahedralCenterNode target.1.node center ∧
          RuleMajorLocalizedTetrahedralDescriptor input center
            emptyOfficialContext descriptor := by
  unfold localizedConstitutionalOccurrenceState localizedConstitutionalOccurrenceRule
  cases centerComputed : input.localizedOccurrenceDescriptorCenter? target with
  | none =>
      constructor
      · simp
      · rintro ⟨center, atNode, _reference⟩
        have present :=
          (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mpr atNode
        rw [centerComputed] at present
        contradiction
  | some center =>
      constructor
      · intro computed
        have descriptorComputed :
            input.constitutionalSeedDescriptorAt? center = some descriptor := by
          simpa [centerComputed] using computed
        exact ⟨center,
          (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target center).mp
            centerComputed,
          (input.constitutionalSeedDescriptorAt?_eq_some_iff_reference
            center descriptor).mp descriptorComputed⟩
      · rintro ⟨otherCenter, atNode, reference⟩
        have otherComputed :=
          (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target otherCenter).mpr atNode
        have centerIdentity : otherCenter = center := by
          rw [centerComputed] at otherComputed
          exact (Option.some.inj otherComputed).symm
        subst otherCenter
        have descriptorComputed :=
          (input.constitutionalSeedDescriptorAt?_eq_some_iff_reference
            center descriptor).mpr reference
        simp [descriptorComputed]

/-- Constitution-only base evaluation can never invent a lowercase label. -/
theorem localizedConstitutionalOccurrenceState_ne_some_pseudoasymmetric
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (descriptor : PseudoRS) :
    input.localizedConstitutionalOccurrenceState fuel target ≠
      some (.pseudoasymmetric descriptor) := by
  unfold localizedConstitutionalOccurrenceState localizedConstitutionalOccurrenceRule
  cases input.localizedOccurrenceDescriptorCenter? target with
  | none => simp
  | some center =>
      cases input.constitutionalSeedDescriptorAt? center <;> simp

/-- The direct seed state is a model of the independent complete seed relation. -/
theorem localizedConstitutionalOccurrenceState_cipModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedConstitutionalAuxiliarySemantics fuel)).CIPModel
        (input.localizedConstitutionalOccurrenceState fuel) := by
  rw [(input.localizedAuxiliaryOccurrenceSystem
    (input.localizedConstitutionalAuxiliarySemantics fuel)).cipModel_iff_executableStateStep_fixed
      (input.localizedAuxiliaryDerivationStepCorrespondence
        (input.localizedConstitutionalAuxiliarySemantics fuel))]
  funext target
  rfl

/-- Constitution-only uppercase seeds have one and only one complete occurrence state. -/
theorem existsUnique_localizedConstitutionalOccurrenceModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ∃! state,
      (input.localizedAuxiliaryOccurrenceSystem
        (input.localizedConstitutionalAuxiliarySemantics fuel)).CIPModel state :=
  input.existsUnique_localizedAuxiliaryCIPModel
    (input.localizedConstitutionalAuxiliarySemantics fuel)

/-- The causal scheduler computes a model of the concrete constitution-only seed semantics. -/
theorem localizedConstitutionalSchedulerClosure_cipModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedConstitutionalAuxiliarySemantics fuel)).CIPModel
        (DeclarativeCIP.OccurrenceScheduler.decode
          (input.localizedAuxiliaryOccurrenceSystem
            (input.localizedConstitutionalAuxiliarySemantics fuel))
          (@input.LocalizedDepthDependency fuel)
          (DeclarativeCIP.OccurrenceScheduler.closure
            (input.localizedAuxiliaryOccurrenceSystem
              (input.localizedConstitutionalAuxiliarySemantics fuel))
            (@input.LocalizedDepthDependency fuel))) :=
  input.localizedAuxiliarySchedulerClosure_cipModel
    (input.localizedConstitutionalAuxiliarySemantics fuel)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
