import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3SpatialUnitExact

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact virtual-ligand completion for Rule-3 endpoints

The format-neutral semantic molecule may leave an alkene hydrogen or a heteroatom lone pair
unmaterialized.  The represented-atom Rule-3 evaluator is already exact, but by itself a singleton
represented substituent cannot distinguish these chemically different cases:

* one real substituent plus implicit protium;
* one real substituent plus a lone pair;
* an invalid/incomplete endpoint spelling.

This module supplies a typed endpoint-completion boundary.  Virtual positions participate in the
strict-seniority check but are never used as spatial reference points: a positive descriptor still
requires a represented, strictly senior reference atom.  In particular, explicitly represented
ordinary hydrogen ties an implicit protium and is refused, whereas deuterium is admitted by the
exact Rule-2 mass comparison.

The completion is explicit evidence.  Deriving it from general element, charge, valence, and
electron-state chemistry is the next molecule-perception theorem; it is not assumed here.
-/

/-- Virtual ligand positions needed at the currently represented ordinary-double-bond boundary. -/
inductive AromaticCanonicalRule3VirtualLigand where
  | implicitProtium
  | lonePair
  deriving DecidableEq, Repr

/-- Exhaustive endpoint shapes for the first virtual-ligand closure.

`representedOnly` has two real non-partner substituents.  The two singleton cases have one real
substituent and one virtual competitor.  The three zero-represented cases exhaust the unordered
two-position multisets over implicit protium and lone-pair positions; none can provide the
represented senior reference required by a positive spatial unit. -/
inductive AromaticCanonicalRule3EndpointCompletion where
  | representedOnly
  | oneImplicitProtium
  | twoImplicitProtia
  | oneLonePair
  | implicitProtiumAndLonePair
  | twoLonePairs
  deriving DecidableEq, Repr

namespace AromaticCanonicalRule3EndpointCompletion

def virtualLigands : AromaticCanonicalRule3EndpointCompletion →
    List AromaticCanonicalRule3VirtualLigand
  | .representedOnly => []
  | .oneImplicitProtium => [.implicitProtium]
  | .twoImplicitProtia => [.implicitProtium, .implicitProtium]
  | .oneLonePair => [.lonePair]
  | .implicitProtiumAndLonePair => [.implicitProtium, .lonePair]
  | .twoLonePairs => [.lonePair, .lonePair]

def representedCount : AromaticCanonicalRule3EndpointCompletion → ℕ
  | .representedOnly => 2
  | .oneImplicitProtium => 1
  | .twoImplicitProtia => 0
  | .oneLonePair => 1
  | .implicitProtiumAndLonePair => 0
  | .twoLonePairs => 0

@[simp] theorem virtualLigands_length_add_representedCount
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    completion.virtualLigands.length + completion.representedCount = 2 := by
  cases completion <;> rfl

end AromaticCanonicalRule3EndpointCompletion

/-- The endpoint completion accounts for exactly the represented non-partner neighbors. -/
def CanonicalAromaticCanonicalRule3EndpointCompletion
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) : Prop :=
  (source.aromaticCanonicalRule3Substituents endpoint partner).length =
    completion.representedCount

noncomputable def aromaticCanonicalRule3EndpointCompletionCompatible?
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) : Bool :=
  decide ((source.aromaticCanonicalRule3Substituents endpoint partner).length =
    completion.representedCount)

@[simp] theorem aromaticCanonicalRule3EndpointCompletionCompatible?_eq_true_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    source.aromaticCanonicalRule3EndpointCompletionCompatible?
        endpoint partner completion = true ↔
      source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner completion := by
  simp [aromaticCanonicalRule3EndpointCompletionCompatible?,
    CanonicalAromaticCanonicalRule3EndpointCompletion]

@[simp] theorem canonicalEndpointCompletion_representedOnly_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner .representedOnly ↔
      (source.aromaticCanonicalRule3Substituents endpoint partner).length = 2 := by
  rfl

@[simp] theorem canonicalEndpointCompletion_oneImplicitProtium_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner .oneImplicitProtium ↔
      (source.aromaticCanonicalRule3Substituents endpoint partner).length = 1 := by
  rfl

@[simp] theorem canonicalEndpointCompletion_twoImplicitProtia_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner .twoImplicitProtia ↔
      source.aromaticCanonicalRule3Substituents endpoint partner = [] := by
  unfold CanonicalAromaticCanonicalRule3EndpointCompletion
  simp [AromaticCanonicalRule3EndpointCompletion.representedCount]

@[simp] theorem canonicalEndpointCompletion_oneLonePair_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner .oneLonePair ↔
      (source.aromaticCanonicalRule3Substituents endpoint partner).length = 1 := by
  rfl

@[simp] theorem canonicalEndpointCompletion_implicitProtiumAndLonePair_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner .implicitProtiumAndLonePair ↔
      source.aromaticCanonicalRule3Substituents endpoint partner = [] := by
  unfold CanonicalAromaticCanonicalRule3EndpointCompletion
  simp [AromaticCanonicalRule3EndpointCompletion.representedCount]

@[simp] theorem canonicalEndpointCompletion_twoLonePairs_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom) :
    source.CanonicalAromaticCanonicalRule3EndpointCompletion
        endpoint partner .twoLonePairs ↔
      source.aromaticCanonicalRule3Substituents endpoint partner = [] := by
  unfold CanonicalAromaticCanonicalRule3EndpointCompletion
  simp [AromaticCanonicalRule3EndpointCompletion.representedCount]

/-- Exact source-backed mass assigned to ordinary implicit hydrogen under Rule 2. -/
def aromaticCanonicalImplicitProtiumMass : ℕ :=
  (CIPRule2MassData.rule2MassPico? 1 none).getD 0

/-- A represented reference strictly outranks one virtual endpoint position.

Every real atom outranks a lone pair's zero atomic-number position.  Against implicit protium,
Rule 1a decides when the real atom has atomic number greater than one; a represented hydrogen must
instead win strictly by the exact Rule-2 mass datum. -/
def AromaticCanonicalRule3ReferenceOutranksVirtual
    (source : AuthoritativeChemicalInput)
    (reference : source.AromaticCanonicalAtom)
    (virtual : AromaticCanonicalRule3VirtualLigand) : Prop :=
  match virtual with
  | .lonePair => True
  | .implicitProtium =>
      1 < source.molecule.toLocalizedMoleculeGraph.atomZ reference ∨
        (source.molecule.toLocalizedMoleculeGraph.atomZ reference = 1 ∧
          aromaticCanonicalImplicitProtiumMass <
            source.molecule.toLocalizedMoleculeGraph.atomMass reference)

def aromaticCanonicalRule3ReferenceOutranksVirtual?
    (source : AuthoritativeChemicalInput)
    (reference : source.AromaticCanonicalAtom)
    (virtual : AromaticCanonicalRule3VirtualLigand) : Bool :=
  match virtual with
  | .lonePair => true
  | .implicitProtium =>
      decide (1 < source.molecule.toLocalizedMoleculeGraph.atomZ reference) ||
        (decide (source.molecule.toLocalizedMoleculeGraph.atomZ reference = 1) &&
          decide (aromaticCanonicalImplicitProtiumMass <
            source.molecule.toLocalizedMoleculeGraph.atomMass reference))

@[simp] theorem aromaticCanonicalRule3ReferenceOutranksVirtual?_eq_true_iff
    (source : AuthoritativeChemicalInput)
    (reference : source.AromaticCanonicalAtom)
    (virtual : AromaticCanonicalRule3VirtualLigand) :
    source.aromaticCanonicalRule3ReferenceOutranksVirtual? reference virtual = true ↔
      source.AromaticCanonicalRule3ReferenceOutranksVirtual reference virtual := by
  cases virtual <;>
    simp [aromaticCanonicalRule3ReferenceOutranksVirtual?,
      AromaticCanonicalRule3ReferenceOutranksVirtual]

theorem aromaticCanonicalRule3Reference_outranks_lonePair
    (source : AuthoritativeChemicalInput)
    (reference : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalRule3ReferenceOutranksVirtual reference .lonePair := by
  trivial

theorem aromaticCanonicalRule3Reference_outranks_implicitProtium_of_atomicNumber_gt_one
    (source : AuthoritativeChemicalInput)
    (reference : source.AromaticCanonicalAtom)
    (higher : 1 < source.molecule.toLocalizedMoleculeGraph.atomZ reference) :
    source.AromaticCanonicalRule3ReferenceOutranksVirtual
      reference .implicitProtium := by
  exact Or.inl higher

theorem aromaticCanonicalRule3HydrogenReference_outranks_implicitProtium_of_mass_gt
    (source : AuthoritativeChemicalInput)
    (reference : source.AromaticCanonicalAtom)
    (hydrogen : source.molecule.toLocalizedMoleculeGraph.atomZ reference = 1)
    (heavier : aromaticCanonicalImplicitProtiumMass <
      source.molecule.toLocalizedMoleculeGraph.atomMass reference) :
    source.AromaticCanonicalRule3ReferenceOutranksVirtual
      reference .implicitProtium := by
  exact Or.inr ⟨hydrogen, heavier⟩

theorem aromaticCanonicalRule3HydrogenReference_not_outrank_implicitProtium_of_mass_le
    (source : AuthoritativeChemicalInput)
    (reference : source.AromaticCanonicalAtom)
    (hydrogen : source.molecule.toLocalizedMoleculeGraph.atomZ reference = 1)
    (notHeavier : source.molecule.toLocalizedMoleculeGraph.atomMass reference ≤
      aromaticCanonicalImplicitProtiumMass) :
    ¬ source.AromaticCanonicalRule3ReferenceOutranksVirtual
      reference .implicitProtium := by
  rintro (higher | ⟨_, heavier⟩)
  · rw [hydrogen] at higher
    exact (Nat.lt_irrefl 1) higher
  · exact (not_lt_of_ge notHeavier) heavier

/-- The chosen represented reference passes the supplied virtual completion. -/
def CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) : Prop :=
  source.CanonicalAromaticCanonicalRule3EndpointCompletion endpoint partner completion ∧
    ∀ virtual, virtual ∈ completion.virtualLigands →
      source.AromaticCanonicalRule3ReferenceOutranksVirtual reference virtual

noncomputable def aromaticCanonicalRule3EndpointReferenceAccepted?
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) : Bool :=
  source.aromaticCanonicalRule3EndpointCompletionCompatible? endpoint partner completion &&
    completion.virtualLigands.all
      (source.aromaticCanonicalRule3ReferenceOutranksVirtual? reference)

@[simp] theorem aromaticCanonicalRule3EndpointReferenceAccepted?_eq_true_iff
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    source.aromaticCanonicalRule3EndpointReferenceAccepted?
        endpoint partner reference completion = true ↔
      source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
        endpoint partner reference completion := by
  simp [aromaticCanonicalRule3EndpointReferenceAccepted?,
    CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance]

/-- Exact virtual-aware senior-reference meaning: the represented branches have one strict
constitutional maximum, the completion has the right shape, and that maximum also strictly
outranks every virtual position. -/
def CanonicalAromaticCanonicalRule3VirtualSeniorReference
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) : Prop :=
  source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference
      endpoint partner reference ∧
    source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
      endpoint partner reference completion

noncomputable def aromaticCanonicalRule3VirtualSeniorReference?
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    Option source.AromaticCanonicalAtom := do
  let reference ← source.aromaticCanonicalRule3ConstitutionalSeniorReference? endpoint partner
  if source.aromaticCanonicalRule3EndpointReferenceAccepted?
      endpoint partner reference completion then
    some reference
  else
    none

/-- The virtual-aware endpoint selector succeeds exactly on the completed strict-seniority
relation. -/
theorem aromaticCanonicalRule3VirtualSeniorReference?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    source.aromaticCanonicalRule3VirtualSeniorReference?
        endpoint partner completion = some reference ↔
      source.CanonicalAromaticCanonicalRule3VirtualSeniorReference
        endpoint partner reference completion := by
  constructor
  · intro computed
    unfold aromaticCanonicalRule3VirtualSeniorReference? at computed
    cases seniorComputed : source.aromaticCanonicalRule3ConstitutionalSeniorReference?
        endpoint partner with
    | none => simp [seniorComputed] at computed
    | some senior =>
        cases accepted : source.aromaticCanonicalRule3EndpointReferenceAccepted?
            endpoint partner senior completion <;>
          simp [seniorComputed, accepted] at computed
        subst reference
        exact ⟨
          (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
            endpoint partner senior).mp seniorComputed,
          (source.aromaticCanonicalRule3EndpointReferenceAccepted?_eq_true_iff
            endpoint partner senior completion).mp accepted⟩
  · rintro ⟨seniorDerived, acceptedDerived⟩
    have seniorComputed :=
      (source.aromaticCanonicalRule3ConstitutionalSeniorReference?_eq_some_iff_canonical
        endpoint partner reference).mpr seniorDerived
    have accepted :=
      (source.aromaticCanonicalRule3EndpointReferenceAccepted?_eq_true_iff
        endpoint partner reference completion).mpr acceptedDerived
    simp [aromaticCanonicalRule3VirtualSeniorReference?, seniorComputed, accepted]

theorem aromaticCanonicalRule3VirtualSeniorReference?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput)
    (endpoint partner : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion) :
    source.aromaticCanonicalRule3VirtualSeniorReference?
        endpoint partner completion = none ↔
      ¬ ∃ reference, source.CanonicalAromaticCanonicalRule3VirtualSeniorReference
        endpoint partner reference completion := by
  cases computed : source.aromaticCanonicalRule3VirtualSeniorReference?
      endpoint partner completion with
  | none =>
      simp only [true_iff]
      rintro ⟨reference, derived⟩
      have positive :=
        (source.aromaticCanonicalRule3VirtualSeniorReference?_eq_some_iff_canonical
          endpoint partner reference completion).mpr derived
      rw [computed] at positive
      contradiction
  | some reference =>
      simp only [reduceCtorEq, false_iff]
      intro absent
      exact absent ⟨reference,
        (source.aromaticCanonicalRule3VirtualSeniorReference?_eq_some_iff_canonical
          endpoint partner reference completion).mp computed⟩

/-- Exact meaning of a positive spatial unit after completing both endpoint ligand frames. -/
def CanonicalAromaticCanonicalRule3SpatialUnitWithVirtualEndpoints
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (leftCompletion rightCompletion : AromaticCanonicalRule3EndpointCompletion)
    (result : source.AromaticCanonicalRule3SpatialUnitResult) : Prop :=
  source.CanonicalAromaticCanonicalRule3SpatialUnit left right result ∧
    source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
      left right result.leftReference leftCompletion ∧
    source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
      right left result.rightReference rightCompletion

noncomputable def aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (leftCompletion rightCompletion : AromaticCanonicalRule3EndpointCompletion) :
    Option source.AromaticCanonicalRule3SpatialUnitResult := do
  let result ← source.aromaticCanonicalRule3SpatialUnit? left right
  if source.aromaticCanonicalRule3EndpointReferenceAccepted?
        left right result.leftReference leftCompletion &&
      source.aromaticCanonicalRule3EndpointReferenceAccepted?
        right left result.rightReference rightCompletion then
    some result
  else
    none

/-- The virtual-aware spatial-unit evaluator succeeds exactly on the represented structural,
coordinate, geometry, and completed endpoint-priority relation. -/
theorem aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (leftCompletion rightCompletion : AromaticCanonicalRule3EndpointCompletion)
    (result : source.AromaticCanonicalRule3SpatialUnitResult) :
    source.aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?
        left right leftCompletion rightCompletion = some result ↔
      source.CanonicalAromaticCanonicalRule3SpatialUnitWithVirtualEndpoints
        left right leftCompletion rightCompletion result := by
  constructor
  · intro computed
    unfold aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints? at computed
    cases spatialComputed : source.aromaticCanonicalRule3SpatialUnit? left right with
    | none => simp [spatialComputed] at computed
    | some observed =>
        cases leftAccepted : source.aromaticCanonicalRule3EndpointReferenceAccepted?
            left right observed.leftReference leftCompletion <;>
          cases rightAccepted : source.aromaticCanonicalRule3EndpointReferenceAccepted?
            right left observed.rightReference rightCompletion <;>
          simp [spatialComputed, leftAccepted, rightAccepted] at computed
        subst result
        exact ⟨
          (source.aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
            left right observed).mp spatialComputed,
          (source.aromaticCanonicalRule3EndpointReferenceAccepted?_eq_true_iff
            left right observed.leftReference leftCompletion).mp leftAccepted,
          (source.aromaticCanonicalRule3EndpointReferenceAccepted?_eq_true_iff
            right left observed.rightReference rightCompletion).mp rightAccepted⟩
  · rintro ⟨spatialDerived, leftDerived, rightDerived⟩
    have spatialComputed :=
      (source.aromaticCanonicalRule3SpatialUnit?_eq_some_iff_canonical
        left right result).mpr spatialDerived
    have leftAccepted :=
      (source.aromaticCanonicalRule3EndpointReferenceAccepted?_eq_true_iff
        left right result.leftReference leftCompletion).mpr leftDerived
    have rightAccepted :=
      (source.aromaticCanonicalRule3EndpointReferenceAccepted?_eq_true_iff
        right left result.rightReference rightCompletion).mpr rightDerived
    simp [aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?, spatialComputed,
      leftAccepted, rightAccepted]

/-- Virtual-aware spatial refusal is exactly absence of the completed canonical relation. -/
theorem aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?_eq_none_iff_no_canonical
    (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalAtom)
    (leftCompletion rightCompletion : AromaticCanonicalRule3EndpointCompletion) :
    source.aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?
        left right leftCompletion rightCompletion = none ↔
      ¬ ∃ result,
        source.CanonicalAromaticCanonicalRule3SpatialUnitWithVirtualEndpoints
          left right leftCompletion rightCompletion result := by
  cases computed : source.aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?
      left right leftCompletion rightCompletion with
  | none =>
      simp only [true_iff]
      rintro ⟨result, derived⟩
      have positive :=
        (source.aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?_eq_some_iff_canonical
          left right leftCompletion rightCompletion result).mpr derived
      rw [computed] at positive
      contradiction
  | some result =>
      simp only [reduceCtorEq, false_iff]
      intro absent
      exact absent ⟨result,
        (source.aromaticCanonicalRule3SpatialUnitWithVirtualEndpoints?_eq_some_iff_canonical
          left right leftCompletion rightCompletion result).mp computed⟩

/-- Any zero-represented completion cannot produce the represented senior reference required by
the spatial descriptor relation. -/
theorem no_virtualSeniorReference_of_representedCount_eq_zero
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom)
    (completion : AromaticCanonicalRule3EndpointCompletion)
    (representedZero : completion.representedCount = 0) :
    ¬ source.CanonicalAromaticCanonicalRule3VirtualSeniorReference
      endpoint partner reference completion := by
  rintro ⟨⟨ranked, senior, rankedDerived, seniorStrict, seniorAtom⟩,
    compatible, _virtuals⟩
  have candidatesLengthZero :
      (source.aromaticCanonicalRule3Substituents endpoint partner).length = 0 := by
    exact compatible.trans representedZero
  have candidatesNil :
      source.aromaticCanonicalRule3Substituents endpoint partner = [] :=
    List.length_eq_zero_iff.mp candidatesLengthZero
  have rankedNil : ranked = [] := by
    rw [candidatesNil] at rankedDerived
    cases rankedDerived
    rfl
  subst ranked
  simpa using seniorStrict.1

/-- Two implicit hydrogens cannot supply a represented senior reference. -/
theorem no_virtualSeniorReference_of_twoImplicitProtia
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom) :
    ¬ source.CanonicalAromaticCanonicalRule3VirtualSeniorReference
      endpoint partner reference .twoImplicitProtia := by
  exact source.no_virtualSeniorReference_of_representedCount_eq_zero
    endpoint partner reference .twoImplicitProtia rfl

/-- An implicit protium plus a lone pair likewise has no represented spatial reference. -/
theorem no_virtualSeniorReference_of_implicitProtiumAndLonePair
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom) :
    ¬ source.CanonicalAromaticCanonicalRule3VirtualSeniorReference
      endpoint partner reference .implicitProtiumAndLonePair := by
  exact source.no_virtualSeniorReference_of_representedCount_eq_zero
    endpoint partner reference .implicitProtiumAndLonePair rfl

/-- Two lone-pair positions likewise cannot supply a represented spatial reference. -/
theorem no_virtualSeniorReference_of_twoLonePairs
    (source : AuthoritativeChemicalInput)
    (endpoint partner reference : source.AromaticCanonicalAtom) :
    ¬ source.CanonicalAromaticCanonicalRule3VirtualSeniorReference
      endpoint partner reference .twoLonePairs := by
  exact source.no_virtualSeniorReference_of_representedCount_eq_zero
    endpoint partner reference .twoLonePairs rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
