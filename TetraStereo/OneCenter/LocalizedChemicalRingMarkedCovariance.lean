import TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport
import TetraStereo.OneCenter.LocalizedChemicalRingFrameSetup
import TetraStereo.OneCenter.LocalizedChemicalRingOrderingTransport
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedOperations
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Covariance of the actual marked callback, including strict-ranking readback. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedRetainedPromotedOperations LocalizedMarkedCarrierLookup
open LocalizedMarkedFramePositionBridge LocalizedChemicalRingPromotedTransport
open LocalizedChemicalRingStateTransport LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRelabel LocalizedChemicalRingFrameComparison
open LocalizedChemicalRingFrameReadback LocalizedChemicalRingFrameSetup
open LocalizedChemicalRingOrderingTransport
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedCertifiedTerminalRefusal
open LocalizedGenericMarkedRecalculation (frameAtoms? rankedAtoms? strict atomsAt?)

namespace Ranking
export LocalizedMarkedRetainedPromotedRanking
  (before partition? refinedKey RefinedKey refined_compare_lt_iff refined_compare_eq_iff
   before_eq_refined)
end Ranking

noncomputable section
open scoped Classical
variable (input : CertifiedLocalizedCIPInput)

theorem before_transport {mol : RawMolecule}
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)) (center : input.TetrahedralCenter)
    (frames : input.ActualFrameSlotTransport single e target center)
    (reference : input.Atom) (W D : Nat) (left right : Fin 4) :
    Ranking.before input state' (input.transportOccurrence single e target)
      ((e : Equiv.Perm input.Atom) reference) W D frames.imageFrame
      (frames.slotPerm left) (frames.slotPerm right) =
    Ranking.before input state target reference W D frames.sourceFrame left right := by
  unfold LocalizedMarkedRetainedPromotedRanking.before
  rw [rawStateView_eq_molecularView, rawStateView_eq_molecularView,
    rawStateDescriptorMap_transport input e sym state state' perm unique]
  simp only [frames.cursorAt_eq]
  exact compareAt_transport input single e (rawStateDescriptorMap input state)
    (rawStateDescriptorMap_tetrahedral input state) target reference W D _ _
    (frame_child input target frames.sourceFrame frames.sourceComputed left)
    (frame_child input target frames.sourceFrame frames.sourceComputed right)

/-- Erases the promotion counter and exposes the actual strict priority atom list. -/
theorem ranked_eq (mol : RawMolecule) (W D : Nat) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (computed : input.localizedNoDoubleFourLigandFrameExec? target = some frame)
    (read : Readback input atoms frame) (reference : input.Atom)
    (key : Fin 4 → Ranking.RefinedKey)
    (callback : ∀ a b, Ranking.before input state target reference W D frame a b =
      some (compare (key a) (key b)))
    (ordinaryTotal : ∀ a b, ∃ order, rawStateBefore input state target frame a b = some order) :
    (markedWithLayout? input mol W D state node reference.val).bind (rankedAtoms? atoms) =
      if strict (adjacentBy (fun a b => some (compare (key a) (key b)))
          (keyOrder key (List.finRange 4))) then
        (keyOrder key (List.finRange 4)).mapM (atomAt input frame) else none := by
  let sorted := keyOrder key (List.finRange 4)
  let adjacent := adjacentBy (fun a b => some (compare (key a) (key b))) sorted
  have callbackEq := funext fun a => funext fun b => callback a b
  have partition : Ranking.partition? input state target reference W D = some (sorted, adjacent) := by
    unfold LocalizedMarkedRetainedPromotedRanking.partition?
    rw [computed]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [callbackEq, sortBy?_key compare Ranking.refined_compare_lt_iff]
    rfl
  obtain ⟨count, counted⟩ := adjacentPromotionCount?_exists
    (rawStateBefore input state target frame)
    (Ranking.before input state target reference W D frame) ordinaryTotal
    (fun a b => ⟨_, callback a b⟩) sorted
  simp only [markedWithLayout?, dif_pos reference.isLt, found, raw, computed, partition,
    read.positions, counted, Option.bind_eq_bind, Option.bind_some]
  change (if strict adjacent then atomsAt? atoms (sorted.map read.index) else none) = _
  rw [read.atoms]

private theorem mapM_transport {α β : Type} (σ : Nat → Nat) (p : α → β)
    (left : α → Option Nat) (right : β → Option Nat)
    (same : ∀ a, right (p a) = (left a).map σ) :
    ∀ xs : List α, (xs.map p).mapM right = (xs.mapM left).map (List.map σ)
  | [] => rfl
  | a :: xs => by
      simp only [List.map_cons, List.mapM_cons, same, mapM_transport σ p left right same xs]
      cases left a <;> cases xs.mapM left <;> rfl

/-- Actual paired frames suffice for callback covariance; ordering is derived from transported
comparisons using a pullback of the source refined key, not equality of chosen windows. -/
theorem marked_with_setup (mol : RawMolecule)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (node : RawMolecule.CanonicalBranchNode) (atoms atoms' : List Nat)
    (raw : frameAtoms? mol node = some atoms)
    (raw' : frameAtoms? mol (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some atoms')
    (setup : Setup input single e node atoms atoms')
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup) (reference : input.Atom) (W D : Nat) :
    (markedWithLayout? input mol W D state'
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
      (relabelOf input (e : Equiv.Perm input.Atom) reference.val)).bind (rankedAtoms? atoms') =
    ((markedWithLayout? input mol W D state node reference.val).bind (rankedAtoms? atoms)).map
      (List.map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit setup.target.1, setup.detected⟩
  let execution := rawStateFrames input single state setup.target setup.real unit rfl
  have frameEq : execution.frame = setup.frames.sourceFrame := by
    have h := execution.frameComputed
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?,
      setup.frames.sourceComputed] at h
    exact (Option.some.inj h).symm
  let key := Ranking.refinedKey input single state setup.target setup.real unit rfl reference W D
  let key' := fun slot => key (setup.frames.slotPerm.symm slot)
  have callback : ∀ a b, Ranking.before input state setup.target reference W D
      setup.frames.sourceFrame a b = some (compare (key a) (key b)) := by
    intro a b
    rw [← frameEq]
    exact Ranking.before_eq_refined input single state setup.target setup.real unit rfl reference W D a b
  have callback' : ∀ a b, Ranking.before input state' (input.transportOccurrence single e setup.target)
      ((e : Equiv.Perm input.Atom) reference) W D setup.frames.imageFrame a b =
        some (compare (key' a) (key' b)) := by
    intro a b
    have h := before_transport input single e sym state state' perm unique setup.target setup.center
      setup.frames reference W D (setup.frames.slotPerm.symm a) (setup.frames.slotPerm.symm b)
    simpa only [Equiv.apply_symm_apply, callback] using h
  have ordinaryTotal : ∀ a b, ∃ order,
      rawStateBefore input state setup.target setup.frames.sourceFrame a b = some order := by
    intro a b
    rw [← frameEq]
    exact ⟨_, rawStateBefore_eq_keys input single state setup.target setup.real unit rfl a b⟩
  have ordinaryTotal' : ∀ a b, ∃ order,
      rawStateBefore input state' (input.transportOccurrence single e setup.target)
        setup.frames.imageFrame a b = some order := by
    intro a b
    obtain ⟨order, h⟩ := ordinaryTotal (setup.frames.slotPerm.symm a) (setup.frames.slotPerm.symm b)
    refine ⟨order, ?_⟩
    have h' := rawStateBefore_transport input single e sym state state' perm unique setup.target
      setup.center setup.frames (setup.frames.slotPerm.symm a) (setup.frames.slotPerm.symm b)
    simpa only [Equiv.apply_symm_apply, h] using h'
  rw [relabelOf_val, ranked_eq input mol W D state' _ _ setup.imageFound atoms' raw'
    setup.frames.imageFrame
    (by rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?];
        exact setup.frames.imageComputed)
    setup.imageRead _ key' callback' ordinaryTotal',
    ranked_eq input mol W D state node setup.target setup.found atoms raw setup.frames.sourceFrame
    (by rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?];
        exact setup.frames.sourceComputed)
    setup.sourceRead reference key callback ordinaryTotal]
  have population := setup.frames.slotPerm.map_finRange_perm.symm
  have preserved : ∀ slot ∈ List.finRange 4, key' (setup.frames.slotPerm slot) = key slot := by
    intro slot _
    simp only [key', Equiv.symm_apply_apply]
  have columns := mapped_keys_perm setup.frames.slotPerm key key' (List.finRange 4)
    (List.finRange 4) population preserved
  have adjacent := adjacent_sorted_eq compare key key' (List.finRange 4) (List.finRange 4) columns
  rw [adjacent]
  split
  · rename_i strictSource
    have sorted := keyOrder_transport_of_strict compare Ranking.refined_compare_lt_iff
      Ranking.refined_compare_eq_iff setup.frames.slotPerm key key' (List.finRange 4)
      (List.finRange 4) (List.nodup_finRange 4) population preserved strictSource
    rw [sorted]
    exact mapM_transport _ setup.frames.slotPerm (atomAt input setup.frames.sourceFrame)
      (atomAt input setup.frames.imageFrame)
      (atomAt_transport input single e setup.target setup.center setup.frames) _
  · rfl

theorem marked_none_of_three (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (three : (mol.canonicalIncidentNeighbors node.atom).length = 3)
    (state : OccurrenceAuxState) (mark W D : Nat) :
    markedWithLayout? input mol W D state node mark = none := by
  unfold markedWithLayout?
  split
  · cases found : lookup? input node with
    | none => rfl
    | some target =>
        simp only [Option.bind_eq_bind, Option.bind_some, raw,
          noFrame_of_three input mol agreement admissible supported single node reached atoms
            raw three target found, Option.bind_none]
  · rfl

/-- The actual retained marked callback transports at every reached raw frame. Unique state
keys suffice; three-coordinate frames and out-of-range marks are refused on both sides. -/
theorem marked_covariant (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms atoms' : List Nat) (raw : frameAtoms? mol node = some atoms)
    (raw' : frameAtoms? mol (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some atoms')
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup) (r : Nat) :
    (marked? input mol state' (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
      (relabelOf input (e : Equiv.Perm input.Atom) r)).bind (rankedAtoms? atoms') =
    ((marked? input mol state node r).bind (rankedAtoms? atoms)).map
      (List.map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  unfold marked?
  by_cases bound : r < input.certified.input.molecule.atomCount
  · have wf := admissible.1.1
    have uq := admissible.1.2
    have rs := raw_single mol input agreement wf uq supported single
    rcases frame_atoms_perm_neighbors mol wf rs node reached atoms raw with ⟨four, _⟩ | ⟨three, _⟩
    · obtain ⟨setup⟩ := setup_exists input mol agreement admissible supported single e sym
        node reached atoms atoms' raw raw' four
      exact marked_with_setup input mol single e sym node atoms atoms' raw raw' setup state state'
        perm unique ⟨r, bound⟩ _ _
    · have imageReached := reached_map sym wf uq rs node reached
      have imageThree : (mol.canonicalIncidentNeighbors
          (relabelOf input (e : Equiv.Perm input.Atom) node.atom)).length = 3 := by
        simpa [three] using (neighbors_map sym wf uq node.atom).length_eq
      rw [marked_none_of_three input mol agreement admissible supported single node reached
        atoms raw three,
        marked_none_of_three input mol agreement admissible supported single _ imageReached
          atoms' raw' imageThree]
      rfl
  · have outside := Nat.le_of_not_gt bound
    rw [relabelOf_outside input (e : Equiv.Perm input.Atom) r outside,
      markedWithLayout?_invalid input mol _ _ state node r outside,
      markedWithLayout?_invalid input mol _ _ state' _ r outside]
    rfl

end
end TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance.before_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance.ranked_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance.marked_with_setup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance.marked_covariant
