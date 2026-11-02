import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3FuelCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Total source-canonical classification of circular Rule-3 auxiliaries

The source-canonical physical-topology layer exhaustively enumerates the independent four-ligand
coupled-unit relation.  This module turns that finite search into a total, evidence-bearing
classification.  Every represented frame is one of:

* ordinary circular cancellation, because no valid coupled pair exists;
* one uniquely coupled physical-unit pair; or
* genuine ambiguity, witnessed by two distinct independently valid pairs.

The result closes the represented-frame classification boundary.  It does not assert that every
chemically conceivable coupled network is already expressible by the four-ligand relation.
-/

/-- The three source-canonical circular-auxiliary outcomes.  Unlike the operational resolver,
ambiguity is retained as a typed outcome rather than encoded only as `none`. -/
inductive AromaticCanonicalRule3CircularAuxiliaryClassification
    (source : AuthoritativeChemicalInput) where
  | ordinary
  | coupled (pair : source.AromaticCanonicalRule3CoupledUnitPair)
  | ambiguous
  deriving DecidableEq, Repr

/-- Independent exact meaning of every circular-auxiliary outcome. -/
inductive DeclarativeAromaticCanonicalRule3CircularAuxiliaryClassification
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.AromaticCanonicalRule3CircularAuxiliaryClassification → Prop
  | ordinary
      (absent : ∀ pair,
        ¬ source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair) :
      source.DeclarativeAromaticCanonicalRule3CircularAuxiliaryClassification
        keys .ordinary
  | coupled
      (pair : source.AromaticCanonicalRule3CoupledUnitPair)
      (derived : source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair)
      (unique : ∀ other,
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys other →
          other = pair) :
      source.DeclarativeAromaticCanonicalRule3CircularAuxiliaryClassification
        keys (.coupled pair)
  | ambiguous
      (first second : source.AromaticCanonicalRule3CoupledUnitPair)
      (firstDerived :
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys first)
      (secondDerived :
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys second)
      (different : first ≠ second) :
      source.DeclarativeAromaticCanonicalRule3CircularAuxiliaryClassification
        keys .ambiguous

/-- No retained coupled pair is exactly the ordinary circular-cancellation result. -/
theorem aromaticCanonicalRule3PhysicalTopologyResolution?_eq_ordinary_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some .ordinary ↔
      ∀ pair, ¬ source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair := by
  constructor
  · intro computed
    have derived := source.aromaticCanonicalRule3PhysicalTopologyResolution?_sound
      keys .ordinary computed
    cases derived with
    | ordinary absent => exact absent
  · intro absent
    have empty : source.aromaticCanonicalRule3CoupledUnitPairs keys = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro pair present
      exact absent pair
        ((source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys pair).mp present)
    simp [aromaticCanonicalRule3PhysicalTopologyResolution?, empty]

/-- A retained coupled pair is exactly one independently valid pair and its uniqueness among all
valid pairs. -/
theorem aromaticCanonicalRule3PhysicalTopologyResolution?_eq_coupled_iff
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (pair : source.AromaticCanonicalRule3CoupledUnitPair) :
    source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some (.coupled pair) ↔
      source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys pair ∧
        ∀ other,
          source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys other →
            other = pair := by
  constructor
  · intro computed
    have resolutionDerived :=
      source.aromaticCanonicalRule3PhysicalTopologyResolution?_sound
        keys (.coupled pair) computed
    cases resolutionDerived with
    | coupled derived unique => exact ⟨derived, unique⟩
  · rintro ⟨derived, unique⟩
    have pairPresent : pair ∈ source.aromaticCanonicalRule3CoupledUnitPairs keys :=
      (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys pair).mpr derived
    have foundNodup := source.aromaticCanonicalRule3CoupledUnitPairs_nodup keys
    have singleton : source.aromaticCanonicalRule3CoupledUnitPairs keys = [pair] := by
      cases foundIdentity : source.aromaticCanonicalRule3CoupledUnitPairs keys with
      | nil => simp [foundIdentity] at pairPresent
      | cons first tail =>
          have firstDerived :
              source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys first :=
            (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys first).mp (by
              rw [foundIdentity]
              simp)
          have firstIdentity : first = pair := unique first firstDerived
          subst first
          have tailEmpty : tail = [] := by
            rw [List.eq_nil_iff_forall_not_mem]
            intro other otherPresent
            have otherDerived :
                source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys other :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys other).mp (by
                rw [foundIdentity]
                simp [otherPresent])
            have otherIdentity : other = pair := unique other otherDerived
            subst other
            rw [foundIdentity] at foundNodup
            exact (List.nodup_cons.mp foundNodup).1 otherPresent
          simp [tailEmpty]
    simp [aromaticCanonicalRule3PhysicalTopologyResolution?, singleton]

/-- Resolver refusal is neither missing data nor list-order choice: it is exactly two distinct
independently valid coupled physical-unit pairs. -/
theorem aromaticCanonicalRule3PhysicalTopologyResolution?_eq_none_iff_ambiguous
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = none ↔
      ∃ left right,
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys left ∧
        source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys right ∧
        left ≠ right := by
  constructor
  · intro refused
    unfold aromaticCanonicalRule3PhysicalTopologyResolution? at refused
    cases foundIdentity : source.aromaticCanonicalRule3CoupledUnitPairs keys with
    | nil => simp [foundIdentity] at refused
    | cons first tail =>
        cases tail with
        | nil => simp [foundIdentity] at refused
        | cons second rest =>
            have firstDerived :
                source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys first :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys first).mp (by
                rw [foundIdentity]
                simp)
            have secondDerived :
                source.DeclarativeAromaticCanonicalRule3CoupledUnitPair keys second :=
              (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys second).mp (by
                rw [foundIdentity]
                simp)
            have foundNodup := source.aromaticCanonicalRule3CoupledUnitPairs_nodup keys
            rw [foundIdentity] at foundNodup
            exact ⟨first, second, firstDerived, secondDerived,
              fun same => (List.nodup_cons.mp foundNodup).1 (by simp [same])⟩
  · rintro ⟨left, right, leftDerived, rightDerived, different⟩
    have leftPresent : left ∈ source.aromaticCanonicalRule3CoupledUnitPairs keys :=
      (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys left).mpr leftDerived
    have rightPresent : right ∈ source.aromaticCanonicalRule3CoupledUnitPairs keys :=
      (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys right).mpr rightDerived
    unfold aromaticCanonicalRule3PhysicalTopologyResolution?
    cases foundIdentity : source.aromaticCanonicalRule3CoupledUnitPairs keys with
    | nil => simp [foundIdentity] at leftPresent
    | cons first tail =>
        cases tail with
        | nil =>
            simp [foundIdentity] at leftPresent rightPresent
            exact (different (leftPresent.trans rightPresent.symm)).elim
        | cons second rest => rfl

/-- Total finite classifier for the represented circular-auxiliary frame. -/
noncomputable def classifyAromaticCanonicalRule3CircularAuxiliary
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.AromaticCanonicalRule3CircularAuxiliaryClassification :=
  match source.aromaticCanonicalRule3CoupledUnitPairs keys with
  | [] => .ordinary
  | [pair] => .coupled pair
  | _ :: _ :: _ => .ambiguous

/-- The total classifier always carries its independent chemical-topology meaning. -/
theorem classifyAromaticCanonicalRule3CircularAuxiliary_sound
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.DeclarativeAromaticCanonicalRule3CircularAuxiliaryClassification keys
      (source.classifyAromaticCanonicalRule3CircularAuxiliary keys) := by
  unfold classifyAromaticCanonicalRule3CircularAuxiliary
  cases foundIdentity : source.aromaticCanonicalRule3CoupledUnitPairs keys with
  | nil =>
      exact .ordinary (by
        intro pair derived
        have present := (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff
          keys pair).mpr derived
        simp [foundIdentity] at present)
  | cons first tail =>
      cases tail with
      | nil =>
          exact .coupled first
            ((source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys first).mp (by
              rw [foundIdentity]
              simp))
            (by
              intro other derived
              have present :=
                (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff
                  keys other).mpr derived
              rw [foundIdentity] at present
              simpa using present)
      | cons second rest =>
          have firstDerived :=
            (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys first).mp (by
              rw [foundIdentity]
              simp)
          have secondDerived :=
            (source.mem_aromaticCanonicalRule3CoupledUnitPairs_iff keys second).mp (by
              rw [foundIdentity]
              simp)
          have foundNodup := source.aromaticCanonicalRule3CoupledUnitPairs_nodup keys
          rw [foundIdentity] at foundNodup
          exact .ambiguous first second firstDerived secondDerived
            (fun same => (List.nodup_cons.mp foundNodup).1 (by simp [same]))

/-- Every represented source-canonical frame has an independent circular-auxiliary
classification. -/
theorem exists_declarativeAromaticCanonicalRule3CircularAuxiliaryClassification
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    ∃ classification,
      source.DeclarativeAromaticCanonicalRule3CircularAuxiliaryClassification
        keys classification :=
  ⟨source.classifyAromaticCanonicalRule3CircularAuxiliary keys,
    source.classifyAromaticCanonicalRule3CircularAuxiliary_sound keys⟩

/-- Erasing typed ambiguity back to the legacy optional resolver is exact. -/
theorem classifyAromaticCanonicalRule3CircularAuxiliary_resolver
    (source : AuthoritativeChemicalInput)
    (keys : List source.AromaticCanonicalUncancelledRule3SpatialKey) :
    match source.classifyAromaticCanonicalRule3CircularAuxiliary keys with
    | .ordinary =>
        source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some .ordinary
    | .coupled pair =>
        source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = some (.coupled pair)
    | .ambiguous =>
        source.aromaticCanonicalRule3PhysicalTopologyResolution? keys = none := by
  unfold classifyAromaticCanonicalRule3CircularAuxiliary
  unfold aromaticCanonicalRule3PhysicalTopologyResolution?
  cases source.aromaticCanonicalRule3CoupledUnitPairs keys with
  | nil => rfl
  | cons first tail =>
      cases tail <;> rfl

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
