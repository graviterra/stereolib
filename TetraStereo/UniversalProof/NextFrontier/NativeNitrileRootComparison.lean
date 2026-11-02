import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRootFrame
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileLeafRoots
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileOccurrenceComparison

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery

-- Callback specialization uses the proved labels without reducing hydrogen expansion.
attribute [local irreducible] expanded

/-- Independent priority slots: F, nitrile C, aminoalkyl C, H. -/
def priorityCursor (n : Nat) (slot : Fin 4) : CanonicalRerootCursor :=
  match slot.val with
  | 0 => nitrileRootCursor 1
  | 1 => nitrileCursor
  | 2 => aminoCursor
  | _ => nitrileRootCursor (n + 7)

def ActualRootCallback (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (ordering : Ordering) : Prop :=
  compareOccurrenceBranches? mol state fuel left right = some { ordering := ordering } ∧
    compareOccurrenceBranchesAuthoritative? mol state fuel left right =
      some { ordering := ordering } ∧
    compareOccurrenceBranchesComplete? mol state fuel left right = some { ordering := ordering }

private theorem atomic_root_callback (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) (left right leftZ rightZ : Nat)
    (leftObserved : (expanded parity n).atomZAt left = leftZ)
    (rightObserved : (expanded parity n).atomZAt right = rightZ)
    (different : leftZ ≠ rightZ)
    (acyclic : (expanded parity n).atomLiesInCycle fuel left = false ∨
      (expanded parity n).atomLiesInCycle fuel right = false) :
    ActualRootCallback (expanded parity n) state fuel
      (nitrileRootCursor left) (nitrileRootCursor right) (compare leftZ rightZ) := by
  have labels : (expanded parity n).atomZAt (nitrileRootCursor left).node.atom ≠
      (expanded parity n).atomZAt (nitrileRootCursor right).node.atom := by
    change (expanded parity n).atomZAt left ≠ (expanded parity n).atomZAt right
    rw [leftObserved, rightObserved]
    exact different
  have fast := compareOccurrenceBranches?_eq_of_rule1a (expanded parity n) state fuel
    (nitrileRootCursor left) (nitrileRootCursor right) rfl rfl labels acyclic
  have authoritative := compareOccurrenceBranchesAuthoritative?_eq_of_rule1a
    (expanded parity n) state fuel (nitrileRootCursor left) (nitrileRootCursor right)
    rfl rfl labels acyclic
  have complete := compareOccurrenceBranchesComplete?_eq_of_rule1a (expanded parity n)
    state fuel (nitrileRootCursor left) (nitrileRootCursor right) rfl rfl labels acyclic
  simpa only [ActualRootCallback, nitrileRootCursor, canonicalRoot,
    leftObserved, rightObserved] using And.intro fast (And.intro authoritative complete)

/-- Every off-diagonal production root callback is computed. The equal-Z carbon pair uses
the actual sorted multiple-bond duplicate proof; every other pair uses actual atomic labels. -/
theorem actual_root_priority_callbacks (parity : TetrahedralInputParity) (n fuel : Nat)
    (state : OccurrenceAuxState) (left right : Fin 4) (different : left ≠ right) :
    ActualRootCallback (expanded parity n) state (fuel + 2)
      (priorityCursor n left) (priorityCursor n right) (compare right.val left.val) := by
  rcases expanded_local_atomic_numbers parity n with
    ⟨_, fluorine, nitrile, _, amino, _, _, hydrogen, _⟩
  have fCycle := expanded_fluorine_acyclic parity n (fuel + 2)
  have hCycle := expanded_center_hydrogen_acyclic parity n (fuel + 2)
  have fn := atomic_root_callback parity n (fuel + 2) state 1 2 9 6
    fluorine nitrile (by decide) (Or.inl fCycle)
  have fa := atomic_root_callback parity n (fuel + 2) state 1 4 9 6
    fluorine amino (by decide) (Or.inl fCycle)
  have fh := atomic_root_callback parity n (fuel + 2) state 1 (n + 7) 9 1
    fluorine hydrogen (by decide) (Or.inl fCycle)
  have nf := atomic_root_callback parity n (fuel + 2) state 2 1 6 9
    nitrile fluorine (by decide) (Or.inr fCycle)
  have nh := atomic_root_callback parity n (fuel + 2) state 2 (n + 7) 6 1
    nitrile hydrogen (by decide) (Or.inr hCycle)
  have af := atomic_root_callback parity n (fuel + 2) state 4 1 6 9
    amino fluorine (by decide) (Or.inr fCycle)
  have ah := atomic_root_callback parity n (fuel + 2) state 4 (n + 7) 6 1
    amino hydrogen (by decide) (Or.inr hCycle)
  have hf := atomic_root_callback parity n (fuel + 2) state (n + 7) 1 1 9
    hydrogen fluorine (by decide) (Or.inl hCycle)
  have hn := atomic_root_callback parity n (fuel + 2) state (n + 7) 2 1 6
    hydrogen nitrile (by decide) (Or.inl hCycle)
  have ha := atomic_root_callback parity n (fuel + 2) state (n + 7) 4 1 6
    hydrogen amino (by decide) (Or.inl hCycle)
  have carbons := actual_nitrile_amino_occurrence_comparison parity n fuel state
  have completeCarbons := actual_nitrile_amino_complete_comparison parity n fuel state
  have na : ActualRootCallback (expanded parity n) state (fuel + 2)
      nitrileCursor aminoCursor .gt := ⟨carbons.1, carbons.2.1, completeCarbons.1⟩
  have an : ActualRootCallback (expanded parity n) state (fuel + 2)
      aminoCursor nitrileCursor .lt := ⟨carbons.2.2.1, carbons.2.2.2, completeCarbons.2⟩
  fin_cases left <;> fin_cases right
  all_goals first
    | exact False.elim (different rfl)
    | exact fn
    | exact fa
    | exact fh
    | exact nf
    | exact na
    | exact nh
    | exact af
    | exact an
    | exact ah
    | exact hf
    | exact hn
    | exact ha

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
