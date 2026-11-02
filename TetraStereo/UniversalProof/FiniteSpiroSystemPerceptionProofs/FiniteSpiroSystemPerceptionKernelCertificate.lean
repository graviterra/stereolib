import TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.FiniteSpiroSystemPerception

set_option autoImplicit false

/-! Closed finite graph fixtures check the literal Boolean validator. Detector membership is
then derived by reflection, avoiding reduction of the factorial candidate enumeration. Neither
fixture supplies stereogenicity, a spatial frame, source observation or source approval. -/
namespace TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.Regression
open TetraStereo.OneCenter

def carbon : SemanticAtom :=
  { element := { atomicNumber := 6, positive := by decide, atMost118 := by decide } }

def bond (left right : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .unspecifiedCovalent }

def twoTriangles : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, carbon, carbon, carbon, carbon]
        interactions := [bond 0 1, bond 1 2, bond 2 0, bond 0 3, bond 3 4, bond 4 0] } }

def proper : P93AuthoritySpiroSystem := ⟨0, [1, 2], [3, 4]⟩
def overlapping : P93AuthoritySpiroSystem := ⟨0, [1, 2], [1, 2]⟩

theorem proper_check : spiroMechanicalValidityCheck twoTriangles proper = true := by decide

theorem overlap_check : spiroMechanicalValidityCheck twoTriangles overlapping = false := by decide

theorem proper_detected : proper ∈ perceivedSpiroSystems twoTriangles :=
  (mem_perceivedSpiroSystems_iff twoTriangles proper).mpr
    ((spiroMechanicalValidityCheck_eq_true_iff twoTriangles proper).mp proper_check)

theorem overlap_refused : overlapping ∉ perceivedSpiroSystems twoTriangles := by
  intro member
  have valid := (mem_perceivedSpiroSystems_iff twoTriangles overlapping).mp member
  have accepted := (spiroMechanicalValidityCheck_eq_true_iff twoTriangles overlapping).mpr valid
  rw [overlap_check] at accepted
  exact Bool.false_ne_true accepted

end TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.Regression

assert_kernel_only TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.Regression.proper_check
assert_kernel_only TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.Regression.overlap_check
assert_kernel_only TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.Regression.proper_detected
assert_kernel_only TetraStereo.UniversalProof.FiniteSpiroSystemPerceptionProofs.Regression.overlap_refused
