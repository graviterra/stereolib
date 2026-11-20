import TetraStereo.OneCenter.LocalizedChemicalRingFrameSetup
import TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Covariance of the actual retained ordinary callback

The actual comparison matrix determines the sorting relation. Image keys are the pullback of
the source keys along the derived frame permutation, avoiding any assumption that independently
chosen sufficient padding windows are equal. Strict orders transport exactly; tied reference
populations transport up to permutation. Reached three-coordinate frames are refused by both
certified ordinary callbacks.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingFrameComparison
open LocalizedChemicalRingFrameSetup LocalizedChemicalRingFrameReadback
open LocalizedChemicalRingOrderingTransport
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedOperations LocalizedMarkedRetainedStateReader
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedCertifiedTerminalRefusal
open LocalizedGenericMarkedRecalculation (frameAtoms? atomsAt? eligibleOf)

variable (input : CertifiedLocalizedCIPInput)

theorem partition_eq_of_frame_keys
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (key : Fin 4 → CompleteLigandRule5Key)
    (before : rawStateBefore input [] target frame =
      fun a b => some (compare (key a) (key b))) :
    ordinaryPartition? input [] target = some (keyOrder key (List.finRange 4),
      adjacentBy (fun a b => some (compare (key a) (key b)))
        (keyOrder key (List.finRange 4))) := by
  unfold ordinaryPartition?
  rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?, computed]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [before, sortBy?_key compare completeLigandRule5Key_compare_lt_iff key]
  rfl

theorem mapM_atoms_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (center : input.TetrahedralCenter) (frames : input.ActualFrameSlotTransport single e target center) :
    ∀ xs : List (Fin 4),
      (xs.map frames.slotPerm).mapM (atomAt input frames.imageFrame) =
        (xs.mapM (atomAt input frames.sourceFrame)).map
          (List.map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.mapM_cons, atomAt_transport, ih]
      cases hx : atomAt input frames.sourceFrame x <;>
        cases ht : xs.mapM (atomAt input frames.sourceFrame) <;> rfl

theorem filter_atoms_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (center : input.TetrahedralCenter) (frames : input.ActualFrameSlotTransport single e target center) :
    ∀ xs : List (Fin 4),
      (xs.map frames.slotPerm).filterMap (atomAt input frames.imageFrame) =
        (xs.filterMap (atomAt input frames.sourceFrame)).map
          (relabelOf input (e : Equiv.Perm input.Atom)) := by
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.filterMap_cons, atomAt_transport, ih]
      cases hx : atomAt input frames.sourceFrame x <;> rfl

/-- Actual degree-four ordinary covariance; all sorting and atom readback are derived from
the setup's actual frames and the already proved comparison matrix transport. -/
theorem ordinaryRel_of_setup (mol : RawMolecule)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (node : RawMolecule.CanonicalBranchNode) (atoms atoms' : List Nat)
    (raw : frameAtoms? mol node = some atoms)
    (raw' : frameAtoms? mol (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some atoms')
    (setup : Setup input single e node atoms atoms') :
    OrdinaryRel (relabelOf input (e : Equiv.Perm input.Atom)) atoms atoms'
      (ordinary input mol [] (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node))
      (ordinary input mol [] node) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit setup.target.1, setup.detected⟩
  let key := rawStateKeys input single [] setup.target setup.real unit rfl
  let imageKey := fun slot => key (setup.frames.slotPerm.symm slot)
  let sourceOrder := keyOrder key (List.finRange 4)
  let imageOrder := keyOrder imageKey (List.finRange 4)
  let sourceBefore := fun a b => some (compare (key a) (key b))
  let imageBefore := fun a b => some (compare (imageKey a) (imageKey b))
  have frameEq : (rawStateFrames input single [] setup.target setup.real unit rfl).frame =
      setup.frames.sourceFrame := by
    have h := (rawStateFrames input single [] setup.target setup.real unit rfl).frameComputed
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?,
      setup.frames.sourceComputed] at h
    exact (Option.some.inj h).symm
  have sourceBeforeEq : rawStateBefore input [] setup.target setup.frames.sourceFrame = sourceBefore := by
    funext a b
    have h := rawStateBefore_eq_keys input single [] setup.target setup.real unit rfl a b
    rw [frameEq] at h
    exact h
  have imageBeforeEq : rawStateBefore input [] (input.transportOccurrence single e setup.target)
      setup.frames.imageFrame = imageBefore := by
    funext a b
    have h := rawStateBefore_transport input single e sym [] [] (List.Perm.refl [])
      (by simp) setup.target setup.center setup.frames (setup.frames.slotPerm.symm a)
      (setup.frames.slotPerm.symm b)
    simpa only [Equiv.apply_symm_apply, sourceBeforeEq] using h
  have sourcePart := partition_eq_of_frame_keys input setup.target setup.frames.sourceFrame
    setup.frames.sourceComputed key sourceBeforeEq
  have imagePart := partition_eq_of_frame_keys input _ setup.frames.imageFrame
    setup.frames.imageComputed imageKey imageBeforeEq
  have sourceOrd : ordinary input mol [] node =
      some (sourceOrder.map setup.sourceRead.index, adjacentBy sourceBefore sourceOrder) := by
    unfold ordinary
    rw [setup.found, raw]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?,
      setup.frames.sourceComputed, sourcePart]
    simp only [Option.bind_some, setup.sourceRead.positions]
    rfl
  have imageOrd : ordinary input mol [] (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) =
      some (imageOrder.map setup.imageRead.index, adjacentBy imageBefore imageOrder) := by
    unfold ordinary
    rw [setup.imageFound, raw']
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?,
      setup.frames.imageComputed, imagePart]
    simp only [Option.bind_some, setup.imageRead.positions]
    rfl
  have population := setup.frames.slotPerm.map_finRange_perm.symm
  have preserved : ∀ a ∈ List.finRange 4, imageKey (setup.frames.slotPerm a) = key a := by
    intro a _
    exact congrArg key (setup.frames.slotPerm.symm_apply_apply a)
  have keys := mapped_keys_perm setup.frames.slotPerm key imageKey (List.finRange 4)
    (List.finRange 4) population preserved
  have flags := adjacent_flags_eq compare key imageKey (List.finRange 4) (List.finRange 4) keys
  rw [sourceOrd, imageOrd, ordinaryRel_some_some]
  refine ⟨flags.1, flags.2, ?_, ?_⟩
  · intro strict
    have orderEq := keyOrder_transport_of_strict compare completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff setup.frames.slotPerm key imageKey
      (List.finRange 4) (List.finRange 4) (List.nodup_finRange 4) population preserved strict
    rw [setup.imageRead.atoms, setup.sourceRead.atoms]
    change imageOrder.mapM (atomAt input setup.frames.imageFrame) = _
    rw [show imageOrder = sourceOrder.map setup.frames.slotPerm from orderEq]
    exact mapM_atoms_transport input single e setup.target setup.center setup.frames sourceOrder
  · have ties := tied_sorted_transport compare completeLigandRule5Key_compare_eq_iff
      setup.frames.slotPerm setup.frames.slotPerm.injective key imageKey
      (List.finRange 4) (List.finRange 4) (List.nodup_finRange 4) population preserved
    rw [eligibleOf_tiedEntries, eligibleOf_tiedEntries]
    simp only [setup.imageRead.atom, setup.sourceRead.atom]
    exact (ties.filterMap (atomAt input setup.frames.imageFrame)).trans
      (List.Perm.of_eq (filter_atoms_transport input single e setup.target setup.center setup.frames _))

theorem ordinary_none_of_three (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (three : (mol.canonicalIncidentNeighbors node.atom).length = 3) :
    ordinary input mol [] node = none := by
  cases found : lookup? input node with
  | none => simp [ordinary, found]
  | some target =>
      have refused := noFrame_of_three input mol agreement admissible supported single
        node reached atoms raw three target found
      simp [ordinary, found, raw, refused]

/-- The ordinary field required by `Covariant`, for actual reached framed occurrences. -/
theorem ordinary_covariant (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms atoms' : List Nat) (raw : frameAtoms? mol node = some atoms)
    (raw' : frameAtoms? mol (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some atoms') :
    OrdinaryRel (relabelOf input (e : Equiv.Perm input.Atom)) atoms atoms'
      (ordinary input mol [] (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node))
      (ordinary input mol [] node) := by
  have wf := admissible.1.1
  have uq := admissible.1.2
  have rs := raw_single mol input agreement wf uq supported single
  rcases frame_atoms_perm_neighbors mol wf rs node reached atoms raw with
    ⟨four, _⟩ | ⟨three, _⟩
  · obtain ⟨setup⟩ := setup_exists input mol agreement admissible supported single e sym
      node reached atoms atoms' raw raw' four
    exact ordinaryRel_of_setup input mol single e sym node atoms atoms' raw raw' setup
  · have imageReached := reached_map sym wf uq rs node reached
    have imageThree : (mol.canonicalIncidentNeighbors
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node).atom).length = 3 := by
      have h := (neighbors_map sym wf uq node.atom).length_eq
      simpa only [List.length_map, three, mapNode_atom] using h
    rw [ordinary_none_of_three input mol agreement admissible supported single node reached atoms raw three,
      ordinary_none_of_three input mol agreement admissible supported single _ imageReached atoms' raw' imageThree]
    trivial

end TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance.partition_eq_of_frame_keys
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance.ordinaryRel_of_setup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance.ordinary_none_of_three
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance.ordinary_covariant
