import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeRule6SchedulerAttachment
import TetraStereo.OneCenter.LocalizedTetrahedralSpiroIncidenceCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open BlueBookP93.Cyclic

/-!
# Reference-coherent P-93 spiro ligand-pattern attachment

Rule 6 does not assign one context-free key to a ligand.  Consequently the authoritative P-93
spiro classifier must be run once for each P-92 reference row.  This module converts each of the
four canonical ligand atoms back to its unique `Fin 4` position, feeds the corresponding matrix
row to the existing exact `Xabcd`/`Xabab`/`Xaabb` classifier, and accepts a whole-center pattern
only when all four reference rows return that same pattern.
-/

/-- Partial inverse of the injective canonical four-ligand enumeration. -/
noncomputable def authoritativeSpiroLigandPosition?
    (input : CertifiedLocalizedCIPInput)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (atom : input.Atom) : Option (Fin 4) :=
  if existsPosition : ∃ position : Fin 4,
      input.certified.input.aromaticCanonicalLigandAtom center position = atom then
    some existsPosition.choose
  else none

/-- The partial inverse succeeds at exactly the canonical ligand position naming the atom. -/
theorem authoritativeSpiroLigandPosition?_eq_some_iff
    (input : CertifiedLocalizedCIPInput)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (atom : input.Atom) (position : Fin 4) :
    input.authoritativeSpiroLigandPosition? center atom = some position ↔
      input.certified.input.aromaticCanonicalLigandAtom center position = atom := by
  constructor
  · intro computed
    by_cases existsPosition : ∃ candidate : Fin 4,
        input.certified.input.aromaticCanonicalLigandAtom center candidate = atom
    · have chosenEq : existsPosition.choose = position := by
        apply Option.some.inj
        simpa [authoritativeSpiroLigandPosition?, existsPosition] using computed
      subst position
      exact existsPosition.choose_spec
    · simp [authoritativeSpiroLigandPosition?, existsPosition] at computed
  · intro atomEq
    have existsPosition : ∃ candidate : Fin 4,
        input.certified.input.aromaticCanonicalLigandAtom center candidate = atom :=
      ⟨position, atomEq⟩
    have chosenEq : existsPosition.choose = position :=
      input.certified.input.aromaticCanonicalLigandAtom_injective center
        (existsPosition.choose_spec.trans atomEq.symm)
    simp [authoritativeSpiroLigandPosition?, existsPosition, chosenEq]

/-- One atom-indexed key builder obtained from a single reference row of the exact 4×4 matrix. -/
noncomputable def authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (referencePosition : Fin 4) (atom : input.Atom) :
    Option input.AuthoritativeSpiroBranchKey := do
  let branchPosition ← input.authoritativeSpiroLigandPosition? center atom
  input.authoritativeSpiroRule3Through6BranchKey?
    carrierFuel evaluationFuel center view referencePosition branchPosition

/-- Exact independent meaning of one atom-indexed matrix-row key. -/
theorem authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.certified.input.AromaticCanonicalTetrahedralCenter)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel center))
    (referencePosition : Fin 4) (atom : input.Atom)
    (key : input.AuthoritativeSpiroBranchKey) :
    input.authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
        carrierFuel evaluationFuel center view referencePosition atom = some key ↔
      ∃ branchPosition : Fin 4,
        input.certified.input.aromaticCanonicalLigandAtom center branchPosition = atom ∧
          input.CanonicalAuthoritativeSpiroRule3Through6BranchKey
            carrierFuel evaluationFuel center view referencePosition branchPosition key := by
  unfold authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
  cases positionComputed : input.authoritativeSpiroLigandPosition? center atom with
  | none =>
      constructor
      · simp
      · rintro ⟨position, atomEq, _canonical⟩
        have someEq :=
          (input.authoritativeSpiroLigandPosition?_eq_some_iff center atom position).mpr atomEq
        rw [positionComputed] at someEq
        contradiction
  | some position =>
      rw [input.authoritativeSpiroLigandPosition?_eq_some_iff center atom position] at positionComputed
      change
        input.authoritativeSpiroRule3Through6BranchKey?
            carrierFuel evaluationFuel center view referencePosition position = some key ↔ _
      rw [input.authoritativeSpiroRule3Through6BranchKey?_eq_some_iff_canonical]
      constructor
      · intro canonical
        exact ⟨position, positionComputed, canonical⟩
      · rintro ⟨branchPosition, atomEq, canonical⟩
        have branchEq : branchPosition = position :=
          input.certified.input.aromaticCanonicalLigandAtom_injective center
            (atomEq.trans positionComputed.symm)
        subst branchPosition
        exact canonical

/-- Matrix readiness resolves every actual ring branch in every reference row. -/
theorem AuthoritativeSpiroRule3Through6KeyMatrixReady.matrixRow_branchKeysResolved
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) view)
    (referencePosition : Fin 4) :
    input.LocalizedSpiroBranchKeysResolved center carrier
      (input.authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
        carrierFuel evaluationFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
        view referencePosition) := by
  intro ring _ringPresent occurrence occurrencePresent
  have graphAdjacent : input.moleculeGraph.Adj center occurrence :=
    (input.mem_localizedCycleNeighbors_iff ring center occurrence).mp occurrencePresent |>.2
  have sourceAdjacent := (input.moleculeGraph_adj_iff_aromaticCanonicalAdjacent
    center occurrence).mp graphAdjacent
  obtain ⟨branchPosition, atomEq⟩ :=
    input.certified.input.exists_aromaticCanonicalLigandAtom_eq_of_adjacent
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
      occurrence sourceAdjacent
  obtain ⟨key, canonical⟩ := ready referencePosition branchPosition
  exact ⟨key,
    (input.authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?_eq_some_iff_canonical
      carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
      view referencePosition occurrence key).mpr ⟨branchPosition, atomEq, canonical⟩⟩

/-- Independent P-93 ligand-pattern meaning for one P-92 reference row. -/
def DeclarativeAuthoritativeSpiroMatrixRowLigandPattern
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (referencePosition : Fin 4) (pattern : SpiroLigandPattern) : Prop :=
  input.DeclarativeLocalizedSpiroLigandPattern center carrier
    (SpiroOccurrencePattern.SameResolvedKey
      (input.authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
        carrierFuel evaluationFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
        view referencePosition)
      input.AuthoritativeSpiroBranchKeyEquivalent) pattern

/-- Executable P-93 classifier for one reference row. -/
noncomputable def localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (referencePosition : Fin 4) : Option SpiroLigandPattern :=
  input.localizedSpiroLigandPatternFromAuthoritativeKeys? center carrier
    (input.authoritativeSpiroRule3Through6MatrixRowKeyAtAtom?
      carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)
      view referencePosition)

/-- Under exact matrix readiness, one row emits exactly its independent P-93 pattern judgment. -/
theorem localizedSpiroLigandPatternFromAuthoritativeMatrixRow?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) view)
    (referencePosition : Fin 4) (pattern : SpiroLigandPattern) :
    input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
        carrierFuel evaluationFuel center carrier judged view referencePosition = some pattern ↔
      input.DeclarativeAuthoritativeSpiroMatrixRowLigandPattern
        carrierFuel evaluationFuel center carrier judged view referencePosition pattern := by
  rw [localizedSpiroLigandPatternFromAuthoritativeMatrixRow?,
    input.localizedSpiroLigandPatternFromAuthoritativeKeys?_eq_some_iff
      center carrier judged.1]
  exact and_iff_right
    (ready.matrixRow_branchKeysResolved input carrierFuel evaluationFuel center carrier judged
      view referencePosition)

/-- Reference-independent meaning of the final P-93 pattern: every P-92 reference row yields the
same occurrence-aware ligand pattern. -/
def DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (pattern : SpiroLigandPattern) : Prop :=
  ∀ referencePosition : Fin 4,
    input.DeclarativeAuthoritativeSpiroMatrixRowLigandPattern
      carrierFuel evaluationFuel center carrier judged view referencePosition pattern

/-- Final guarded P-93 pattern classifier.  It evaluates every reference row and rejects an
otherwise resolved center if those four pattern classifications disagree. -/
noncomputable def localizedSpiroLigandPatternFromAuthoritativeMatrix?
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged))) :
    Option SpiroLigandPattern := do
  let first ← input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
    carrierFuel evaluationFuel center carrier judged view (0 : Fin 4)
  let second ← input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
    carrierFuel evaluationFuel center carrier judged view (1 : Fin 4)
  let third ← input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
    carrierFuel evaluationFuel center carrier judged view (2 : Fin 4)
  let fourth ← input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
    carrierFuel evaluationFuel center carrier judged view (3 : Fin 4)
  if _coherent : first = second ∧ first = third ∧ first = fourth then
    some first
  else none

/-- The full four-row classifier succeeds exactly for the independent reference-coherent P-93
ligand-pattern judgment. -/
theorem localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) view)
    (pattern : SpiroLigandPattern) :
    input.localizedSpiroLigandPatternFromAuthoritativeMatrix?
        carrierFuel evaluationFuel center carrier judged view = some pattern ↔
      input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
        carrierFuel evaluationFuel center carrier judged view pattern := by
  let row := fun referencePosition =>
    input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
      carrierFuel evaluationFuel center carrier judged view referencePosition
  have rowExact := fun referencePosition candidate =>
    input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?_eq_some_iff
      carrierFuel evaluationFuel center carrier judged view ready referencePosition candidate
  constructor
  · intro computed
    unfold localizedSpiroLigandPatternFromAuthoritativeMatrix? at computed
    cases firstComputed : row (0 : Fin 4) with
    | none => simp [row, firstComputed] at computed
    | some first =>
        cases secondComputed : row (1 : Fin 4) with
        | none => simp [row, firstComputed, secondComputed] at computed
        | some second =>
            cases thirdComputed : row (2 : Fin 4) with
            | none => simp [row, firstComputed, secondComputed, thirdComputed] at computed
            | some third =>
                cases fourthComputed : row (3 : Fin 4) with
                | none =>
                    simp [row, firstComputed, secondComputed, thirdComputed,
                      fourthComputed] at computed
                | some fourth =>
                    have firstComputed' :
                        input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
                            carrierFuel evaluationFuel center carrier judged view 0 = some first := by
                      simpa [row] using firstComputed
                    have secondComputed' :
                        input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
                            carrierFuel evaluationFuel center carrier judged view 1 = some second := by
                      simpa [row] using secondComputed
                    have thirdComputed' :
                        input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
                            carrierFuel evaluationFuel center carrier judged view 2 = some third := by
                      simpa [row] using thirdComputed
                    have fourthComputed' :
                        input.localizedSpiroLigandPatternFromAuthoritativeMatrixRow?
                            carrierFuel evaluationFuel center carrier judged view 3 = some fourth := by
                      simpa [row] using fourthComputed
                    rw [firstComputed', secondComputed', thirdComputed', fourthComputed'] at computed
                    change
                      (if _coherent : first = second ∧ first = third ∧ first = fourth then
                        some first else none) = some pattern at computed
                    by_cases coherent : first = second ∧ first = third ∧ first = fourth
                    · have firstEq : first = pattern := by
                        rw [dif_pos coherent] at computed
                        exact Option.some.inj computed
                      subst first
                      rcases coherent with ⟨rfl, rfl, rfl⟩
                      intro referencePosition
                      fin_cases referencePosition
                      · exact (rowExact 0 pattern).mp (by simpa [row] using firstComputed)
                      · exact (rowExact 1 pattern).mp (by simpa [row] using secondComputed)
                      · exact (rowExact 2 pattern).mp (by simpa [row] using thirdComputed)
                      · exact (rowExact 3 pattern).mp (by simpa [row] using fourthComputed)
                    · rw [dif_neg coherent] at computed
                      contradiction
  · intro coherent
    have firstComputed := (rowExact (0 : Fin 4) pattern).mpr (coherent 0)
    have secondComputed := (rowExact (1 : Fin 4) pattern).mpr (coherent 1)
    have thirdComputed := (rowExact (2 : Fin 4) pattern).mpr (coherent 2)
    have fourthComputed := (rowExact (3 : Fin 4) pattern).mpr (coherent 3)
    simp [localizedSpiroLigandPatternFromAuthoritativeMatrix?,
      firstComputed, secondComputed, thirdComputed, fourthComputed]

/-- Exhaustive negative boundary: the final classifier returns `none` exactly when no
reference-coherent P-93 ligand pattern exists. -/
theorem localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) view) :
    input.localizedSpiroLigandPatternFromAuthoritativeMatrix?
        carrierFuel evaluationFuel center carrier judged view = none ↔
      ∀ pattern,
        ¬ input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
          carrierFuel evaluationFuel center carrier judged view pattern := by
  constructor
  · intro refused pattern judgedPattern
    have accepted :=
      (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
        carrierFuel evaluationFuel center carrier judged view ready pattern).mpr judgedPattern
    rw [refused] at accepted
    contradiction
  · intro absent
    cases computed : input.localizedSpiroLigandPatternFromAuthoritativeMatrix?
        carrierFuel evaluationFuel center carrier judged view with
    | none => rfl
    | some pattern =>
        exact False.elim (absent pattern
          ((input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
            carrierFuel evaluationFuel center carrier judged view ready pattern).mp computed))

/-- Readiness form of the exact positive theorem. -/
theorem localizedSpiroLigandPatternFromAuthoritativeMatrix?_isSome_iff
    (input : CertifiedLocalizedCIPInput) (carrierFuel evaluationFuel : Nat)
    (center : input.Atom) (carrier : input.LocalizedSpiroCenter center)
    (judged : input.DeclarativeLocalizedConnectivityOnlyTetrahedralSpiroCenter center carrier)
    (view : input.certified.input.AromaticCanonicalDependencyView
      (input.certified.input.aromaticCanonicalFinalOccurrence carrierFuel
        (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged)))
    (ready : input.AuthoritativeSpiroRule3Through6KeyMatrixReady carrierFuel evaluationFuel
      (input.aromaticCanonicalTetrahedralCenterOfLocalizedSpiro center carrier judged) view) :
    (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?
        carrierFuel evaluationFuel center carrier judged view).isSome = true ↔
      ∃ pattern,
        input.DeclarativeAuthoritativeSpiroReferenceCoherentLigandPattern
          carrierFuel evaluationFuel center carrier judged view pattern := by
  rw [Option.isSome_iff_exists]
  constructor <;> rintro ⟨pattern, witnessed⟩
  · exact ⟨pattern,
      (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
        carrierFuel evaluationFuel center carrier judged view ready pattern).mp witnessed⟩
  · exact ⟨pattern,
      (input.localizedSpiroLigandPatternFromAuthoritativeMatrix?_eq_some_iff
        carrierFuel evaluationFuel center carrier judged view ready pattern).mpr witnessed⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
