import TetraStereo.OneCenter.AuthoritativeSemanticMancudeConcreteTetrahedralExactOnceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact molecule-level canonical readiness for source tetrahedral descriptors

The earlier finite-bound readiness package is a useful sufficient chemical contract, but it is
deliberately stronger than the exact success boundary.  This module removes that asymmetry.  The
new relation contains no descriptor and no premise asserting success of the molecule endpoint: it
requires the independently specified canonical first zipper frame, its exact rational-coordinate
parity, and the already-proved lower Rules-1a--6 chemical readiness relation.
-/

/-- Minimal descriptor-free chemical readiness of the complete molecule-level tetrahedral
endpoint.  Frame perception and parity are stated by their independent declarative relations; the
lower readiness relation contains the canonical initial-partition inputs, topology admissibility,
and applicable P-92 branch agreement. -/
def AromaticCanonicalScheduledRule3Through6CanonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  ∃ roots parity,
    source.DeclarativeAromaticCanonicalRerootChildren
        { occurrence := target, previous? := none } roots ∧
      source.DeclarativeAromaticCanonicalRerootFrameParity roots parity ∧
      source.AromaticCanonicalRule3Through6ChemicallyReady
        center.1 target view ruleFuel roots parity

/-- The executable molecule readiness relation is exactly the descriptor-free canonical chemical
readiness relation.  This is the converse missing from the earlier sufficient finite-bound
theorem. -/
theorem aromaticCanonicalScheduledRule3Through6Ready_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalScheduledRule3Through6Ready semantics ruleFuel center ↔
      source.AromaticCanonicalScheduledRule3Through6CanonicalChemicalReadiness
        semantics ruleFuel center := by
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  let view := source.aromaticCanonicalDependencyView state target
  unfold AromaticCanonicalScheduledRule3Through6Ready
    AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
    AromaticCanonicalScheduledRule3Through6CanonicalChemicalReadiness
  dsimp only
  constructor
  · rintro ⟨descriptor, roots, parity, rootsComputed, parityComputed, finalJudgment⟩
    refine ⟨roots, parity,
      (source.aromaticCanonicalOccurrenceLigandFrame?_eq_some_iff
        target roots).mp rootsComputed,
      (source.aromaticCanonicalRerootFrameParity?_eq_some_iff
        roots parity).mp parityComputed, ?_⟩
    exact
      (source.aromaticCanonicalRule3Through6ChemicallyReady_iff_ready
        center.1 target view ruleFuel roots parity).mpr
          ⟨descriptor, finalJudgment⟩
  · rintro ⟨roots, parity, rootsDerived, parityDerived, chemicallyReady⟩
    obtain ⟨descriptor, finalJudgment⟩ :=
      (source.aromaticCanonicalRule3Through6ChemicallyReady_iff_ready
        center.1 target view ruleFuel roots parity).mp chemicallyReady
    exact ⟨descriptor, roots, parity,
      (source.aromaticCanonicalOccurrenceLigandFrame?_eq_some_iff
        target roots).mpr rootsDerived,
      (source.aromaticCanonicalRerootFrameParity?_eq_some_iff
        roots parity).mpr parityDerived,
      finalJudgment⟩

/-- Molecule execution succeeds exactly on the canonical chemical-readiness relation. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_isSome_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics ruleFuel center).isSome = true ↔
      source.AromaticCanonicalScheduledRule3Through6CanonicalChemicalReadiness
        semantics ruleFuel center := by
  rw [Option.isSome_iff_exists,
    ← source.aromaticCanonicalScheduledRule3Through6Ready_iff_exists_descriptor
      semantics ruleFuel center,
    source.aromaticCanonicalScheduledRule3Through6Ready_iff_canonicalChemicalReadiness
      semantics ruleFuel center]

/-- Molecule refusal has no hidden operational case: it is precisely failure of canonical
chemical readiness. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_eq_none_iff_not_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics ruleFuel center = none ↔
      ¬ source.AromaticCanonicalScheduledRule3Through6CanonicalChemicalReadiness
        semantics ruleFuel center := by
  rw [source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_none_iff_not_ready
      semantics ruleFuel center,
    source.aromaticCanonicalScheduledRule3Through6Ready_iff_canonicalChemicalReadiness
      semantics ruleFuel center]

/-- Parameter-free specialization using the unique source-canonical auxiliary fixed point. -/
abbrev AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  source.AromaticCanonicalScheduledRule3Through6CanonicalChemicalReadiness
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center

/-- Concrete executable readiness and the canonical chemical relation coincide for every fuel,
not only at the uniform sufficient bound. -/
theorem aromaticCanonicalConcreteRule3Through6Ready_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalConcreteRule3Through6Ready carrierFuel ruleFuel center ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  exact source.aromaticCanonicalScheduledRule3Through6Ready_iff_canonicalChemicalReadiness
    (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel) ruleFuel center

/-- Exact concrete success boundary against independent canonical chemical readiness. -/
theorem aromaticCanonicalConcreteRule3Through6Descriptor?_isSome_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalConcreteRule3Through6Descriptor?
        carrierFuel ruleFuel center).isSome = true ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  exact
    source.aromaticCanonicalScheduledRule3Through6Descriptor?_isSome_iff_canonicalChemicalReadiness
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel) ruleFuel center

/-- Exact concrete refusal boundary against independent canonical chemical readiness. -/
theorem aromaticCanonicalConcreteRule3Through6Descriptor?_eq_none_iff_not_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalConcreteRule3Through6Descriptor?
        carrierFuel ruleFuel center = none ↔
      ¬ source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  exact
    source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_none_iff_not_canonicalChemicalReadiness
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel) ruleFuel center

/-- A physical source center occurs in the concrete tetrahedral list exactly when it satisfies
canonical chemical readiness.  This is unconditional; nonstereogenic or unresolved candidates
are classified by the negated right-hand side rather than by a global all-centers-ready premise. -/
theorem exists_mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ assignment,
        assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
          carrierFuel ruleFuel ∧ assignment.center = center) ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  constructor
  · rintro ⟨assignment, present, centerIdentity⟩
    have executable :=
      (source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
        carrierFuel ruleFuel assignment).mp present
    have ready : source.AromaticCanonicalConcreteRule3Through6Ready
        carrierFuel ruleFuel assignment.center := ⟨assignment.descriptor, executable⟩
    rw [centerIdentity] at ready
    exact
      (source.aromaticCanonicalConcreteRule3Through6Ready_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mp ready
  · intro chemicallyReady
    obtain ⟨descriptor, executable⟩ :=
      (source.aromaticCanonicalConcreteRule3Through6Ready_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mpr chemicallyReady
    let assignment : source.AromaticCanonicalScheduledRule3Through6Assignment :=
      { center, descriptor }
    refine ⟨assignment, ?_, rfl⟩
    exact
      (source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
        carrierFuel ruleFuel assignment).mpr executable

/-- Canonical chemical readiness is also exactly unique physical-center occurrence.  Determinism
of the per-center option fixes the descriptor, while the record retains the center identity. -/
theorem existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃! assignment,
        assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
          carrierFuel ruleFuel ∧ assignment.center = center) ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact
      (source.exists_mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mp ⟨assignment, property⟩
  · intro chemicallyReady
    obtain ⟨assignment, assignmentPresent, assignmentCenter⟩ :=
      (source.exists_mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mpr chemicallyReady
    refine ⟨assignment, ⟨assignmentPresent, assignmentCenter⟩, ?_⟩
    intro other ⟨otherPresent, otherCenter⟩
    have assignmentComputed :
        source.aromaticCanonicalConcreteRule3Through6Descriptor?
            carrierFuel ruleFuel assignment.center = some assignment.descriptor :=
      (source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
        carrierFuel ruleFuel assignment.center assignment.descriptor).mpr
        ((source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
          carrierFuel ruleFuel assignment).mp assignmentPresent)
    have otherComputed :
        source.aromaticCanonicalConcreteRule3Through6Descriptor?
            carrierFuel ruleFuel other.center = some other.descriptor :=
      (source.aromaticCanonicalConcreteRule3Through6Descriptor?_eq_some_iff_executableJudgment
        carrierFuel ruleFuel other.center other.descriptor).mpr
        ((source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
          carrierFuel ruleFuel other).mp otherPresent)
    have descriptorIdentity : other.descriptor = assignment.descriptor := by
      rw [otherCenter, ← assignmentCenter, assignmentComputed] at otherComputed
      exact Option.some.inj otherComputed.symm
    cases assignment
    cases other
    simp only at assignmentCenter otherCenter descriptorIdentity
    subst_vars
    rfl

/-- Literal count-one coverage is equivalent to the same readiness relation. -/
theorem exists_count_analyzeAromaticCanonicalConcreteRule3Through6_eq_one_iff_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (∃ assignment,
        assignment.center = center ∧
          (source.analyzeAromaticCanonicalConcreteRule3Through6
            carrierFuel ruleFuel).count assignment = 1) ↔
      source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
        carrierFuel ruleFuel center := by
  constructor
  · rintro ⟨assignment, centerIdentity, countOne⟩
    apply
      (source.exists_mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mp
    refine ⟨assignment, ?_, centerIdentity⟩
    exact List.count_pos_iff.mp (by omega)
  · intro chemicallyReady
    obtain ⟨assignment, property, _unique⟩ :=
      (source.existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_canonicalChemicalReadiness
        carrierFuel ruleFuel center).mpr chemicallyReady
    refine ⟨assignment, property.2, ?_⟩
    rw [(source.analyzeAromaticCanonicalConcreteRule3Through6_nodup
      carrierFuel ruleFuel).count]
    simp [property.1]

/-- The previous stronger finite-bound readiness package entails the exact canonical relation.
It remains useful as a sufficient chemical construction theorem, but it is no longer confused
with the minimal success boundary. -/
theorem aromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness_of_readyAtBound
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6ChemicallyReadyAtBound
      carrierFuel center) :
    source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
      carrierFuel (2 * (carrierFuel + 1)) center := by
  obtain ⟨descriptor, computed⟩ :=
    source.exists_aromaticCanonicalConcreteRule3Through6Descriptor?_at_bound
      carrierFuel center ready
  have executableReady : source.AromaticCanonicalConcreteRule3Through6Ready
      carrierFuel (2 * (carrierFuel + 1)) center :=
    (source.aromaticCanonicalConcreteRule3Through6Ready_iff_exists_descriptor
      carrierFuel (2 * (carrierFuel + 1)) center).mpr ⟨descriptor, computed⟩
  exact
    (source.aromaticCanonicalConcreteRule3Through6Ready_iff_canonicalChemicalReadiness
      carrierFuel (2 * (carrierFuel + 1)) center).mp executableReady

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
