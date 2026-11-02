import TetraStereo.OneCenter.LocalizedRule3Spatial
import TetraStereo.OneCenter.LocalizedOccurrenceCarrier

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Fail-closed Rule 3 observations on official occurrences

Rule-3 geometry belongs to a physical double-bond unit encountered in a particular ligand
occurrence, not to an arbitrary atom-global context.  This module recognizes real parent/current
edges in the finite localized occurrence carrier and gives the recognizer three outcomes:

* `some none`: this occurrence is not a real double-bond edge;
* `some (some result)`: it is a double-bond edge with proved spatial Rule-3 evidence; and
* `none`: it is a double-bond edge, but the current strict reference/geometry analyzer cannot
  justify a descriptor.

The outer refusal is essential.  A scan may skip only `some none`; it must propagate `none`, so an
unresolved geometrical unit cannot silently become an absent Rule-3 observation.
-/

namespace CertifiedLocalizedCIPInput

/-- Rule-3 result attached to the actual oriented parent/current edge of one official occurrence. -/
structure LocalizedOccurrenceRule3SpatialResult
    (input : CertifiedLocalizedCIPInput) where
  left : input.Atom
  right : input.Atom
  unit : input.LocalizedRule3SpatialUnitResult
  deriving DecidableEq, Repr

/-- Structural proposition saying that an occurrence is the real child end of a physical
order-two bond. -/
def LocalizedOccurrenceHasRule3DoubleBondEdge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) : Prop :=
  occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    ∃ current parent,
      occurrence.1.node.current? = some current ∧
      occurrence.1.node.parent? = some parent ∧
      input.moleculeGraph.bond parent current = 2

/-- Independent positive meaning of a Rule-3 spatial observation at one carrier occurrence. -/
def DeclarativeLocalizedOccurrenceRule3SpatialUnit
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (result : input.LocalizedOccurrenceRule3SpatialResult) : Prop :=
  occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
    occurrence.1.node.current? = some result.right ∧
    occurrence.1.node.parent? = some result.left ∧
    input.moleculeGraph.bond result.left result.right = 2 ∧
    input.DeclarativeLocalizedRule3SpatialUnit result.left result.right result.unit

/-- Tri-state Rule-3 reading at one occurrence.  Only a structural nonunit is skippable. -/
noncomputable def localizedOccurrenceRule3SpatialUnit?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    Option (Option input.LocalizedOccurrenceRule3SpatialResult) :=
  if occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom then
    match occurrence.1.node.current?, occurrence.1.node.parent? with
    | some current, some parent =>
        if input.moleculeGraph.bond parent current = 2 then
          match input.localizedRule3SpatialUnit? parent current with
          | none => none
          | some unit => some (some { left := parent, right := current, unit := unit })
        else some none
    | _, _ => some none
  else some none

/-- Every positive occurrence reading is backed by the exact physical edge and molecule-level
Rule-3 derivation. -/
theorem localizedOccurrenceRule3SpatialUnit?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (result : input.LocalizedOccurrenceRule3SpatialResult)
    (computed : input.localizedOccurrenceRule3SpatialUnit? occurrence = some (some result)) :
    input.DeclarativeLocalizedOccurrenceRule3SpatialUnit occurrence result := by
  unfold localizedOccurrenceRule3SpatialUnit? at computed
  by_cases real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real] at computed
    cases currentComputed : occurrence.1.node.current? with
    | none => simp [currentComputed] at computed
    | some current =>
        cases parentComputed : occurrence.1.node.parent? with
        | none => simp [currentComputed, parentComputed] at computed
        | some parent =>
            by_cases doubleBond : input.moleculeGraph.bond parent current = 2
            · rw [currentComputed, parentComputed] at computed
              change (if input.moleculeGraph.bond parent current = 2 then
                  match input.localizedRule3SpatialUnit? parent current with
                  | none => none
                  | some unit => some (some
                      { left := parent, right := current, unit := unit })
                else some none) = some (some result) at computed
              rw [if_pos doubleBond] at computed
              cases unitComputed : input.localizedRule3SpatialUnit? parent current with
              | none => simp [unitComputed] at computed
              | some unit =>
                  simp [unitComputed] at computed
                  subst result
                  exact ⟨real, currentComputed, parentComputed, doubleBond,
                    input.localizedRule3SpatialUnit?_sound parent current unit unitComputed⟩
            · simp [currentComputed, parentComputed, doubleBond] at computed
  · simp [real] at computed

/-- The skippable outcome is exact on the structural side: it proves that no real order-two
parent/current edge occurs at this carrier coordinate. -/
theorem localizedOccurrenceRule3SpatialUnit?_eq_some_none_implies_not_edge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (computed : input.localizedOccurrenceRule3SpatialUnit? occurrence = some none) :
    ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  rintro ⟨real, current, parent, currentComputed, parentComputed, doubleBond⟩
  unfold localizedOccurrenceRule3SpatialUnit? at computed
  rw [if_pos real, currentComputed, parentComputed] at computed
  change (if input.moleculeGraph.bond parent current = 2 then
      match input.localizedRule3SpatialUnit? parent current with
      | none => none
      | some unit => some (some
          ({ left := parent, right := current, unit := unit } :
            input.LocalizedOccurrenceRule3SpatialResult))
    else some none) = some none at computed
  rw [if_pos doubleBond] at computed
  cases unitComputed : input.localizedRule3SpatialUnit? parent current <;>
    simp [unitComputed] at computed

/-- Conversely, outer refusal can arise only at a genuine real double-bond occurrence; structural
nonunits are always explicitly skippable. -/
theorem localizedOccurrenceRule3SpatialUnit?_eq_none_implies_edge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (computed : input.localizedOccurrenceRule3SpatialUnit? occurrence = none) :
    input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  unfold localizedOccurrenceRule3SpatialUnit? at computed
  by_cases real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real] at computed
    cases currentComputed : occurrence.1.node.current? with
    | none => simp [currentComputed] at computed
    | some current =>
        cases parentComputed : occurrence.1.node.parent? with
        | none => simp [currentComputed, parentComputed] at computed
        | some parent =>
            by_cases doubleBond : input.moleculeGraph.bond parent current = 2
            · exact ⟨real, current, parent, currentComputed, parentComputed, doubleBond⟩
            · simp [currentComputed, parentComputed, doubleBond] at computed
  · simp [real] at computed

/-- A retained scan element records the carrier occurrence at which its unit was observed. -/
structure LocalizedRule3SpatialOccurrenceObservation
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  source : input.LocalizedCIPOccurrence fuel
  result : input.LocalizedOccurrenceRule3SpatialResult
  deriving DecidableEq, Repr

/-- Independent meaning of one retained occurrence observation. -/
def DeclarativeLocalizedRule3SpatialOccurrenceObservation
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (observation : input.LocalizedRule3SpatialOccurrenceObservation fuel) : Prop :=
  observation.source = occurrence ∧
    input.DeclarativeLocalizedOccurrenceRule3SpatialUnit occurrence observation.result

/-- Fail-closed scan of an already ordered occurrence list.  Genuine unresolved double-bond units
abort the whole scan; only proved structural nonunits are skipped. -/
noncomputable def localizedRule3SpatialOccurrenceScan?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat} :
    List (input.LocalizedCIPOccurrence fuel) →
      Option (List (input.LocalizedRule3SpatialOccurrenceObservation fuel))
  | [] => some []
  | occurrence :: occurrences =>
      match input.localizedOccurrenceRule3SpatialUnit? occurrence with
      | none => none
      | some none => input.localizedRule3SpatialOccurrenceScan? occurrences
      | some (some result) => do
          let tail ← input.localizedRule3SpatialOccurrenceScan? occurrences
          some ({ source := occurrence, result := result } :: tail)

/-- Proof-relevant exact accounting of every scan input: each occurrence is either proved not to
be a Rule-3 edge or retained with a declarative molecule-backed unit derivation. -/
inductive DeclarativeLocalizedRule3SpatialOccurrenceScan
    (input : CertifiedLocalizedCIPInput) {fuel : Nat} :
    List (input.LocalizedCIPOccurrence fuel) →
      List (input.LocalizedRule3SpatialOccurrenceObservation fuel) → Prop
  | nil : input.DeclarativeLocalizedRule3SpatialOccurrenceScan [] []
  | skip {occurrence occurrences observations}
      (notUnit : ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence)
      (tail : input.DeclarativeLocalizedRule3SpatialOccurrenceScan occurrences observations) :
      input.DeclarativeLocalizedRule3SpatialOccurrenceScan
        (occurrence :: occurrences) observations
  | keep {occurrence occurrences observation observations}
      (unit : input.DeclarativeLocalizedRule3SpatialOccurrenceObservation
        occurrence observation)
      (tail : input.DeclarativeLocalizedRule3SpatialOccurrenceScan occurrences observations) :
      input.DeclarativeLocalizedRule3SpatialOccurrenceScan
        (occurrence :: occurrences) (observation :: observations)

/-- Every successful fail-closed scan has an independent derivation accounting for every supplied
carrier occurrence. -/
theorem localizedRule3SpatialOccurrenceScan?_sound
    (input : CertifiedLocalizedCIPInput) {fuel : Nat} :
    ∀ (occurrences : List (input.LocalizedCIPOccurrence fuel))
      (observations : List (input.LocalizedRule3SpatialOccurrenceObservation fuel)),
      input.localizedRule3SpatialOccurrenceScan? occurrences = some observations →
        input.DeclarativeLocalizedRule3SpatialOccurrenceScan occurrences observations
  | [], observations, computed => by
      simp [localizedRule3SpatialOccurrenceScan?] at computed
      subst observations
      exact DeclarativeLocalizedRule3SpatialOccurrenceScan.nil
  | occurrence :: occurrences, observations, computed => by
      unfold localizedRule3SpatialOccurrenceScan? at computed
      cases unitComputed : input.localizedOccurrenceRule3SpatialUnit? occurrence with
      | none => simp [unitComputed] at computed
      | some optionalUnit =>
          cases optionalUnit with
          | none =>
              simp only [unitComputed] at computed
              exact DeclarativeLocalizedRule3SpatialOccurrenceScan.skip
                (input.localizedOccurrenceRule3SpatialUnit?_eq_some_none_implies_not_edge
                  occurrence unitComputed)
                (input.localizedRule3SpatialOccurrenceScan?_sound
                  occurrences observations computed)
          | some result =>
              cases tailComputed : input.localizedRule3SpatialOccurrenceScan? occurrences with
              | none => simp [unitComputed, tailComputed] at computed
              | some tail =>
                  simp [unitComputed, tailComputed] at computed
                  subst observations
                  exact DeclarativeLocalizedRule3SpatialOccurrenceScan.keep
                    ⟨rfl, input.localizedOccurrenceRule3SpatialUnit?_sound
                      occurrence result unitComputed⟩
                    (input.localizedRule3SpatialOccurrenceScan?_sound
                      occurrences tail tailComputed)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
