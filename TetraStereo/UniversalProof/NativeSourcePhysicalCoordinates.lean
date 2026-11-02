import TetraStereo.UniversalProof.NativeRawAtomicNumber
import TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput

/-- Successful conversion observes the SAME physical atom's atomic number at the SAME index. -/
theorem converted_atomic_number (raw : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (atom : source.AromaticCanonicalAtom) :
    source.molecule.toLocalizedMoleculeGraph.atomZ atom = raw.atomZAt atom.val := by
  have indexed := raw.toSemanticMolecule?_atomAt? source.molecule converted atom.val
  have lookup := listGet?_eq_some_get source.molecule.atoms atom
  rw [lookup] at indexed
  cases observed : raw.atomAt? atom.val with
  | none => simp [observed] at indexed
  | some spec =>
      have single : spec.toSemanticAtom? = some (source.molecule.atoms.get atom) := by
        simpa [observed] using indexed.symm
      change (source.molecule.atoms.get atom).element.atomicNumber = raw.atomZAt atom.val
      exact (AtomSpec.toSemanticAtom?_exact spec _ single).1.trans
        (TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.atomZAt_eq_of_atomAt?
          raw atom.val spec observed).symm

end TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment

namespace TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment

/-- The exact zip-index lookup used by occurrenceFactAuthoritative?. -/
def writtenSlot? (written : List Nat) (atom : Nat) : Option Nat :=
  (written.zipIdx.find? fun entry => entry.1 == atom).map Prod.snd

/-- A unique actual written atom is recovered at its real written position. -/
theorem writtenSlot?_eq_some (written : List Nat) (distinct : written.Nodup)
    (index atom : Nat) (observed : written[index]? = some atom) :
    writtenSlot? written atom = some index := by
  obtain ⟨bound, value⟩ := List.getElem?_eq_some_iff.mp observed
  unfold writtenSlot?
  have predicateEqual : (fun entry : Nat × Nat => entry.1 == atom) =
      (fun entry : Nat × Nat => match entry with | (value, _) => value == atom) := by
    funext entry
    cases entry
    rfl
  rw [predicateEqual]
  change (written.zipIdx.find? (fun ⟨value, _⟩ => value == atom)).map
    (fun entry => entry.2) = some index
  rw [← List.findIdx?_eq_fst_find?_zipIdx
    (xs := written) (p := fun value : Nat => value == atom)]
  apply List.findIdx?_eq_some_iff_getElem.mpr
  refine ⟨bound, by simp [value], ?_⟩
  intro earlier before same
  have valueEqual : written.get ⟨earlier, Nat.lt_trans before bound⟩ = written.get ⟨index, bound⟩ := by
    simpa only [List.get_eq_getElem, value] using (beq_iff_eq.mp same)
  have indexEqual := congrArg Fin.val (distinct.injective_get valueEqual)
  change earlier = index at indexEqual
  omega

end TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
