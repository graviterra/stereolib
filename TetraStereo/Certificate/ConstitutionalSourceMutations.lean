import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceOrdering

set_option autoImplicit false

namespace TetraStereo.Certificate.ConstitutionalSourceMutations

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.Certificate.Constitutional
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceOrdering

/-!
Observation checking and chemical checking are distinct. These corrupt packets still provide
enough numerical information to propose the same order, but cannot satisfy actual source
realization. An accepted observation ranking is deliberately insufficient for a chemical claim.
-/

def omittedDuplicate : Four LigandPrefix :=
  { nitrileObservations with b := ⟨6, some [7, 7]⟩ }

def substitutedAtoms : Four LigandPrefix :=
  { nitrileObservations with b := ⟨6, some [8, 8, 8]⟩ }

theorem omitted_duplicate_observation_checked :
    checkRanking omittedDuplicate identityCertificate = .ok identityRanking := by rfl

theorem substituted_atoms_observation_checked :
    checkRanking substitutedAtoms identityCertificate = .ok identityRanking := by rfl

theorem omitted_duplicate_cannot_bind (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    ¬ SourcePrefixRealization (nitrileSource parity n) (nitrileFrame parity n 1)
      (nitrileViewKeys parity n 1 view) (roleSlots n parity) omittedDuplicate := by
  intro corrupt
  have actual := source_prefix_realization n parity view
  have completeCount := SourcePrefixRealization.child_count _ _ _ _ _ actual 1 [7, 7, 7] (by rfl)
  have corruptCount := SourcePrefixRealization.child_count _ _ _ _ _ corrupt 1 [7, 7] (by rfl)
  simp only [List.length_cons, List.length_nil] at completeCount corruptCount
  omega

theorem substituted_atoms_cannot_bind (n : Nat) (parity : TetrahedralInputParity)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence 1 (nitrileCenter parity n))) :
    ¬ SourcePrefixRealization (nitrileSource parity n) (nitrileFrame parity n 1)
      (nitrileViewKeys parity n 1 view) (roleSlots n parity) substitutedAtoms := by
  intro corrupt
  have actual := source_prefix_realization n parity view
  have good := actual.children 1 [7, 7, 7] (by rfl)
  have bad := corrupt.children 1 [8, 8, 8] (by rfl)
  have sameNumbers := good.symm.trans bad
  have impossible := sameNumbers.mem_iff.mp
    (show DeclarativeCIP.ExactAtomicNumber.ofNat 7 ∈
      [7, 7, 7].map DeclarativeCIP.ExactAtomicNumber.ofNat by simp)
  simp [DeclarativeCIP.ExactAtomicNumber.ofNat] at impossible

end TetraStereo.Certificate.ConstitutionalSourceMutations
