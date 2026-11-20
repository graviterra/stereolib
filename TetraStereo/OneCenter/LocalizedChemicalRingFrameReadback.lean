import TetraStereo.OneCenter.LocalizedChemicalRingFrameComparison
import TetraStereo.OneCenter.LocalizedMarkedDetectedOrdinaryExecution
import TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact raw-coordinate readback for the actual certified four-ligand frames. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingFrameReadback
open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedOperations LocalizedMarkedDetectedOrdinaryExecution
open LocalizedMarkedFramePositionBridge LocalizedMarkedRetainedStateReader
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedGenericMarkedRecalculation (frameAtoms? atomsAt? atomsAt)
open RawLocalizedChildNodeTransport
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingRelabel

variable (input : CertifiedLocalizedCIPInput)

abbrev atomAt (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (slot : Fin 4) : Option Nat :=
  (frame.cursorAt slot).occurrence.1.node.current?.map Fin.val

structure Readback (atoms : List Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)) where
  index : Fin 4 → Nat
  positions : ∀ sorted, positions? input atoms frame sorted = some (sorted.map index)
  atom : ∀ slot, atoms[index slot]? = atomAt input frame slot

/-- Derives the conversion for any actual frame at a real detected reached occurrence. -/
theorem readback_exists (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target)
    (real : target.1.node.provenance = .realAtom)
    (detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom)
    (atoms : List Nat) (rawFrame : frameAtoms? mol node = some atoms)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    Nonempty (Readback input atoms frame) := by
  let unit : DetectedOccurrence input.moleculeGraph := ⟨input.molecularFrameUnit target.1, detected⟩
  let execution := rawStateFrames input single [] target real unit rfl
  have same : execution.frame = frame := by
    have h := execution.frameComputed
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?, computed] at h
    exact (Option.some.inj h).symm
  obtain ⟨actual, length, reindex, raw, nodup, read⟩ := exists_frame_position_permutation
    mol input agreement admissible supported single (rawStateDescriptorMap input []) target execution
    node reached (lookup?_sound input node target found)
  have atomEq : actual = atoms := Option.some.inj (raw.symm.trans rawFrame)
  subst actual
  rw [same] at read
  refine ⟨⟨fun i => (reindex.symm i).val,
    positions?_eq_inverse_reindex input atoms length nodup frame reindex read, ?_⟩⟩
  intro slot
  have h := read (reindex.symm slot)
  rw [Equiv.apply_symm_apply] at h
  change atoms[(reindex.symm slot).val]? = (frame.cursorAt slot).occurrence.1.node.current?.map Fin.val
  rw [h]
  exact List.getElem?_eq_getElem (by rw [length]; exact (reindex.symm slot).isLt)

theorem Readback.atoms (atoms : List Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (read : Readback input atoms frame) (sorted : List (Fin 4)) :
    atomsAt? atoms (sorted.map read.index) = sorted.mapM (atomAt input frame) := by
  simp only [atomsAt?, List.mapM_map]
  congr 1
  funext slot
  exact read.atom slot

theorem Readback.filter (atoms : List Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (read : Readback input atoms frame) (sorted : List (Fin 4)) :
    atomsAt atoms (sorted.map read.index) = sorted.filterMap (atomAt input frame) := by
  simp only [atomsAt, List.filterMap_map]
  congr 1
  funext slot
  exact read.atom slot

theorem atomAt_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (center : input.TetrahedralCenter) (frames : input.ActualFrameSlotTransport single e target center)
    (slot : Fin 4) :
    atomAt input frames.imageFrame (frames.slotPerm slot) =
      (atomAt input frames.sourceFrame slot).map (relabelOf input (e : Equiv.Perm input.Atom)) := by
  simp only [atomAt, frames.current_eq, Option.map_map]
  congr 1
  funext atom
  exact (relabelOf_val input (e : Equiv.Perm input.Atom) atom).symm

end TetraStereo.OneCenter.LocalizedChemicalRingFrameReadback
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrameReadback.readback_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrameReadback.atomAt_transport
