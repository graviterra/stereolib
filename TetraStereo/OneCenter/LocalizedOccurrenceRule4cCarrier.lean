import TetraStereo.OneCenter.LocalizedConstitutionalOccurrenceFixedPoint

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact occurrence-local Rule-4c carrier

Rule 4c may inspect lowercase auxiliary descriptors only at strict dependencies of the target.
This module extracts that carrier without flattening occurrences to atom identities.  Every fact
retains its exact final root, address, provenance node, and history through the carrier subtype.

The executable extractor receives only `LocalizedDependencyView`, so a shallower occurrence or an
occurrence below another final root cannot even be queried.  Its proof-facing relation records the
dependency witness and exact lowercase state lookup.  The whole carrier theorem is bidirectional:
there are neither invented facts nor silently omitted eligible lowercase facts.
-/

namespace CertifiedLocalizedCIPInput

/-- One exact lowercase source available to Rule 4c. -/
structure LocalizedRule4cSource
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  occurrence : input.LocalizedCIPOccurrence fuel
  descriptor : PseudoRS

/-- Inspect one enumerated coordinate through the target's restricted view. -/
def localizedRule4cSource?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (source : input.LocalizedCIPOccurrence fuel) :
    Option (input.LocalizedRule4cSource fuel) :=
  if dependency : input.LocalizedDepthDependency source target then
    match view source dependency with
    | some (.pseudoasymmetric descriptor) =>
        some { occurrence := source, descriptor := descriptor }
    | none | some (.chiral _) => none
  else none

/-- Independent meaning of one extracted Rule-4c source. -/
def DeclarativeLocalizedRule4cSource
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (source : input.LocalizedCIPOccurrence fuel)
    (fact : input.LocalizedRule4cSource fuel) : Prop :=
  fact.occurrence = source ∧
    ∃ dependency : input.LocalizedDepthDependency source target,
      view source dependency = some (.pseudoasymmetric fact.descriptor)

/-- One-coordinate extraction is sound and complete for the independent source relation. -/
theorem localizedRule4cSource?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (source : input.LocalizedCIPOccurrence fuel)
    (fact : input.LocalizedRule4cSource fuel) :
    input.localizedRule4cSource? target view source = some fact ↔
      input.DeclarativeLocalizedRule4cSource target view source fact := by
  unfold localizedRule4cSource? DeclarativeLocalizedRule4cSource
  split
  · rename_i dependency
    cases observed : view source dependency with
    | none => simp [observed]
    | some label =>
        cases label with
        | chiral descriptor => simp [observed]
        | pseudoasymmetric descriptor =>
            constructor
            · intro computed
              simp at computed
              subst fact
              exact ⟨rfl, dependency, observed⟩
            · rintro ⟨rfl, otherDependency, otherObserved⟩
              have proofIdentity : otherDependency = dependency := Subsingleton.elim _ _
              subst otherDependency
              rw [observed] at otherObserved
              have descriptorIdentity := Option.some.inj otherObserved
              injection descriptorIdentity with descriptorIdentity
              subst descriptorIdentity
              simp
  · rename_i notDependency
    constructor
    · simp
    · rintro ⟨_rfl, dependency, _observed⟩
      exact (notDependency dependency).elim

/-- Enumerate all and only lowercase strict dependencies.  `attach` retains the membership proof
for each exact occurrence frame in the executable molecular carrier. -/
def localizedRule4cCarrier
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) :
    List (input.LocalizedRule4cSource fuel) :=
  (input.localizedOccurrences fuel).attach.filterMap fun source =>
    input.localizedRule4cSource? target view source

/-- Exact whole-carrier characterization: a fact is emitted iff some enumerated occurrence has
the independent strict-dependency/lowercase-source derivation for that exact fact. -/
theorem mem_localizedRule4cCarrier_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (fact : input.LocalizedRule4cSource fuel) :
    fact ∈ input.localizedRule4cCarrier target view ↔
      ∃ source : input.LocalizedCIPOccurrence fuel,
        input.DeclarativeLocalizedRule4cSource target view source fact := by
  rw [localizedRule4cCarrier, List.mem_filterMap]
  constructor
  · rintro ⟨source, _sourcePresent, computed⟩
    exact ⟨source,
      (input.localizedRule4cSource?_eq_some_iff target view source fact).mp computed⟩
  · rintro ⟨source, derived⟩
    exact ⟨source, by simp,
      (input.localizedRule4cSource?_eq_some_iff target view source fact).mpr derived⟩

/-- Every emitted Rule-4c fact is below the same final root as its target. -/
theorem localizedRule4cCarrier_source_root_eq
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (fact : input.LocalizedRule4cSource fuel)
    (present : fact ∈ input.localizedRule4cCarrier target view) :
    fact.occurrence.1.root = target.1.root := by
  rcases (input.mem_localizedRule4cCarrier_iff target view fact).mp present with
    ⟨source, identity, dependency, _observed⟩
  subst source
  exact dependency.1

/-- Every emitted Rule-4c fact is causally earlier: its remaining-depth measure is strictly less
than the target's. -/
theorem localizedRule4cCarrier_source_remaining_lt
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (fact : input.LocalizedRule4cSource fuel)
    (present : fact ∈ input.localizedRule4cCarrier target view) :
    fact.occurrence.1.remaining < target.1.remaining := by
  rcases (input.mem_localizedRule4cCarrier_iff target view fact).mp present with
    ⟨source, identity, dependency, _observed⟩
  subst source
  exact input.localizedDepthDependency_remaining_lt dependency

/-- The constitution-only seed state has an empty Rule-4c carrier at every target.  Lowercase
facts can therefore enter only through a later, independently justified auxiliary rule. -/
theorem localizedRule4cCarrier_constitutionalState_eq_nil
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) :
    input.localizedRule4cCarrier target
      (input.localizedDependencyView
        (input.localizedConstitutionalOccurrenceState fuel) target) = [] := by
  unfold localizedRule4cCarrier
  rw [List.filterMap_eq_nil_iff]
  intro source _sourcePresent
  unfold localizedRule4cSource?
  split
  · rename_i dependency
    have noPseudo :=
      input.localizedConstitutionalOccurrenceState_ne_some_pseudoasymmetric
        source PseudoRS.r
    cases stateComputed : input.localizedConstitutionalOccurrenceState fuel source with
    | none => simp [localizedDependencyView, stateComputed]
    | some label =>
        cases label with
        | chiral descriptor => simp [localizedDependencyView, stateComputed]
        | pseudoasymmetric descriptor =>
            cases descriptor with
            | r => exact (noPseudo stateComputed).elim
            | s =>
                have noPseudoS :=
                  input.localizedConstitutionalOccurrenceState_ne_some_pseudoasymmetric
                    source PseudoRS.s
                exact (noPseudoS stateComputed).elim
  · rfl

/-- Primitive Rule-4c comparison on two exact carrier facts.  Cross-family refusal is inherited
from the official comparator; the current source type contains only tetrahedral `r/s`. -/
def compareLocalizedRule4cSources?
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (left right : input.LocalizedRule4cSource fuel) : Option Ordering :=
  OfficialPseudoasymmetricDescriptor.compare?
    (OfficialPseudoasymmetricDescriptor.ofPseudoRS left.descriptor)
    (OfficialPseudoasymmetricDescriptor.ofPseudoRS right.descriptor)

@[simp] theorem compareLocalizedRule4cSources_r_s
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (leftOccurrence rightOccurrence : input.LocalizedCIPOccurrence fuel) :
    compareLocalizedRule4cSources?
      ({ occurrence := leftOccurrence, descriptor := .r } :
        input.LocalizedRule4cSource fuel)
      ({ occurrence := rightOccurrence, descriptor := .s } :
        input.LocalizedRule4cSource fuel) = some Ordering.gt :=
  rfl

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
