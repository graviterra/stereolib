import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking
import TetraStereo.OneCenter.LocalizedChemicalRingOrdinaryCovariance
import TetraStereo.OneCenter.LocalizedChemicalRingMultiMarkRecursion
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Actual joint-operation transport for accumulated mark contexts

The concrete `jointOperations` record of `LocalizedChemicalRingJointMarkerOperations` is shown
to be an actual instance of the multi-mark covariance contracts. For an arbitrary molecular
symmetry, an arbitrary reached occurrence with a real detected four-ligand frame, and arbitrary
auxiliary states whose keys are unique:

* the context order transports as an `OrdinaryRel` relation for the entire accumulated mark
  list, mapped by the same atom permutation, with the eligible reference population preserved
  only up to permutation;
* the joint marked ranking bound to `rankedAtoms?` transports exactly, and the actual
  `markedReadingJoint?` reading is the pulled-back-geometry reading;
* reached three-coordinate frames are refused by both callbacks.

The joint slot key is the accepted lawful key `refinedKey` of
`LocalizedChemicalRingJointMarkerRanking` (ordinary key followed by the actually built joint
marker); no callback equality, sorting success, generated-state permutation or literal tied
sorted-list equality is assumed. Empty and repeated mark contexts are supported because
`referenceAtoms?` is decoded from the literal list.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical Rule4aTableBridge
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedOperations
open LocalizedMarkedRetainedPromotedOperations
open LocalizedMarkedCarrierLookup
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedCertifiedTerminalRefusal
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingFrameComparison
open LocalizedChemicalRingFrameSetup LocalizedChemicalRingFrameReadback
open LocalizedChemicalRingOrderingTransport
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointMarkerOperations
open LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingJointMarkerCovariance
open LocalizedChemicalRingMultiMarkRecursion
open LocalizedChemicalRingOrdinaryCovariance
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? atomsAt? rankedAtoms?
  strict atomsAt eligibleOf)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-! ## The accumulated reference context -/

/-- A context cons at an in-range mark exposes the decoded head. -/
private theorem referenceAtoms?_cons_some (input : CertifiedLocalizedCIPInput) {mark : Nat}
    (bound : mark < input.certified.input.molecule.atomCount) (rest : List Nat) :
    referenceAtoms? input (mark :: rest) =
      (referenceAtoms? input rest).map (List.cons ⟨mark, bound⟩) := by
  unfold referenceAtoms?
  rw [List.mapM_cons]
  simp only [dif_pos bound, Option.bind_eq_bind, Option.bind_some]
  cases hrest : List.mapM
      (fun mark => if bound : mark < input.certified.input.molecule.atomCount then
        some (⟨mark, bound⟩ : input.Atom) else none) rest <;> rfl

/-- A context cons at an out-of-range mark is refused, whatever the tail is. -/
private theorem referenceAtoms?_cons_none (input : CertifiedLocalizedCIPInput) {mark : Nat}
    (outside : ¬ mark < input.certified.input.molecule.atomCount) (rest : List Nat) :
    referenceAtoms? input (mark :: rest) = none := by
  unfold referenceAtoms?
  rw [List.mapM_cons]
  simp [dif_neg outside]

/-- Decoding the accumulated context commutes with the atom permutation: in-range marks are
relabelled, out-of-range marks are fixed and refused on both sides. -/
theorem referenceAtoms?_map (e : Equiv.Perm input.Atom) (L : List Nat) :
    referenceAtoms? input (L.map (relabelOf input e)) =
      (referenceAtoms? input L).map (List.map (e : Equiv.Perm input.Atom)) := by
  induction L with
  | nil => rfl
  | cons mark rest ih =>
      rw [List.map_cons]
      by_cases bound : mark < input.certified.input.molecule.atomCount
      · have head : relabelOf input e mark = (e ⟨mark, bound⟩).val :=
          relabelOf_val input e ⟨mark, bound⟩
        rw [head, referenceAtoms?_cons_some input (e ⟨mark, bound⟩).isLt,
          referenceAtoms?_cons_some input bound, ih]
        cases referenceAtoms? input rest <;> rfl
      · rw [relabelOf_outside input e mark (Nat.le_of_not_gt bound),
          referenceAtoms?_cons_none input bound, referenceAtoms?_cons_none input bound]
        rfl

/-- A successful context decoding is exactly the literal list of reference atoms. In
particular empty and repeated marks are admitted, and no separate well-formedness of the
context is needed. -/
theorem eq_map_val_of_referenceAtoms? {M : List Nat} {references : List input.Atom}
    (h : referenceAtoms? input M = some references) : M = references.map Fin.val := by
  induction M generalizing references with
  | nil =>
      cases references with
      | nil => rfl
      | cons reference rest => simp [referenceAtoms?] at h
  | cons mark rest ih =>
      by_cases bound : mark < input.certified.input.molecule.atomCount
      · rw [referenceAtoms?_cons_some input bound] at h
        cases hrest : referenceAtoms? input rest with
        | none => simp [hrest] at h
        | some tail =>
            simp only [hrest, Option.map_some, Option.some.injEq] at h
            rw [ih hrest, ← h]
            rfl
      · rw [referenceAtoms?_cons_none input bound] at h
        cases h

/-- Once the joint ranking bind has transported, the actual reading of a ranked list
transports under the pulled-back geometry, including refusal on both sides. -/
theorem readback_bind_transport {α : Type} (σ : Nat → Nat) (geom : Geometry)
    (source image : Option α) (sourceRanked imageRanked : α → Option (List Nat))
    (h : image.bind imageRanked = (source.bind sourceRanked).map (List.map σ)) :
    image.bind (fun a => (imageRanked a).bind fun ranked => readback? geom ranked) =
      source.bind (fun a => (sourceRanked a).bind fun ranked =>
        readback? (pullback σ geom) ranked) := by
  cases source with
  | none =>
      cases image with
      | none => rfl
      | some a =>
          have : imageRanked a = none := by
            have hh := h
            simp only [Option.bind_none, Option.map_none] at hh
            simpa using hh
          simp [this]
  | some a =>
      cases hf : sourceRanked a with
      | none =>
          have : image.bind imageRanked = none := by
            simpa only [Option.bind_some, hf, Option.map_none] using h
          cases image with
          | none => simp [hf]
          | some b =>
              have hb : imageRanked b = none := by
                simpa [Option.bind_some] using this
              simp [hb, hf]
      | some ranked =>
          have : image.bind imageRanked = some (ranked.map σ) := by
            simpa only [Option.bind_some, hf, Option.map_some] using h
          cases image with
          | none => simp at this
          | some b =>
              have hb : imageRanked b = some (ranked.map σ) := by
                simpa [Option.bind_some] using this
              simp only [hb, hf, Option.bind_some]
              exact readback_map σ geom ranked

/-! ## The actual joint partition at a concrete frame -/

/-- The joint partition determined by an actual frame is the lawful joint key order, the key
comparison column and the accepted promotion count. Only the count is existential: the order
and the adjacent flags are what the consumers use. -/
theorem jointPartition?_eq_partition (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (computed : input.localizedNoDoubleFourLigandFrameExec? target = some frame)
    (read : Readback input atoms frame) (references : List input.Atom) (W D : Nat)
    (key : Fin 4 → RefinedKey)
    (callback : ∀ a b, jointBefore input state target frame references W D a b =
      some (compare (key a) (key b)))
    (ordinaryTotal : ∀ a b, ∃ order, rawStateBefore input state target frame a b = some order) :
    ∃ count,
      jointPartition? input mol state node references W D =
        some ((keyOrder key (List.finRange 4)).map read.index,
          adjacentBy (fun a b => some (compare (key a) (key b)))
            (keyOrder key (List.finRange 4)), count) := by
  let sorted := keyOrder key (List.finRange 4)
  obtain ⟨count, counted⟩ :=
    LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount?_exists
      (rawStateBefore input state target frame)
      (jointBefore input state target frame references W D) ordinaryTotal
      (fun a b => ⟨_, callback a b⟩) sorted
  have callbackEq : jointBefore input state target frame references W D =
      fun a b => some (compare (key a) (key b)) :=
    funext fun a => funext fun b => callback a b
  refine ⟨count, ?_⟩
  unfold jointPartition? jointFrame? partitionBy?
  rw [found, raw]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [computed]
  simp only [Option.bind_some]
  rw [callbackEq, sortBy?_key compare refined_compare_lt_iff]
  simp only [Option.bind_some]
  rw [callbackEq] at counted
  change LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount? _ _ sorted = _ at counted
  rw [counted]
  simp only [Option.bind_some, read.positions]

/-- The actual marked ranking bound to `rankedAtoms?`: in the strict joint order it reads the
frame atoms along the sorted slots, and otherwise it refuses. This is the joint analogue of the
accepted retained `ranked_eq`. -/
theorem markedJoint?_eq_ranked (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (computed : input.localizedNoDoubleFourLigandFrameExec? target = some frame)
    (read : Readback input atoms frame) (references : List input.Atom)
    (key : Fin 4 → RefinedKey)
    (callback : ∀ a b, jointBefore input state target frame references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) a b =
        some (compare (key a) (key b)))
    (ordinaryTotal : ∀ a b, ∃ order, rawStateBefore input state target frame a b = some order)
    (L : List Nat) (hrefs : referenceAtoms? input L = some references) (mark : Nat) :
    (markedJoint? input mol state node L mark).bind (rankedAtoms? atoms) =
      if strict (adjacentBy (fun a b => some (compare (key a) (key b)))
          (keyOrder key (List.finRange 4))) then
        (keyOrder key (List.finRange 4)).mapM (atomAt input frame) else none := by
  let sorted := keyOrder key (List.finRange 4)
  let adjacent := adjacentBy (fun a b => some (compare (key a) (key b))) sorted
  obtain ⟨count, part⟩ := jointPartition?_eq_partition input mol state node target found atoms raw
    frame computed read references (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) key callback ordinaryTotal
  have selection : markedJoint? input mol state node L mark =
      some { positions := sorted.map read.index
             unique := strict adjacent
             pseudoComparisons := count } := by
    simp [markedJoint?, hrefs, part, sorted, adjacent]
  rw [selection]
  simp only [Option.bind_some, rankedAtoms?]
  change (if strict adjacent then atomsAt? atoms (sorted.map read.index) else none) = _
  rw [read.atoms]

/-! ## Structural refusals at reached three-coordinate frames -/

theorem contextOrder?_none_of_three (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (three : (mol.canonicalIncidentNeighbors node.atom).length = 3)
    (state : OccurrenceAuxState) (M : List Nat) :
    contextOrder? input mol state node M = none := by
  cases hrefs : referenceAtoms? input M with
  | none => simp [contextOrder?, hrefs]
  | some references =>
      cases found : lookup? input node with
      | none => simp [contextOrder?, hrefs, jointPartition?, jointFrame?, found]
      | some target =>
          have refused := noFrame_of_three input mol agreement admissible supported single
            node reached atoms raw three target found
          simp [contextOrder?, hrefs, jointPartition?, jointFrame?, found, raw, refused]

theorem markedJoint?_none_of_three (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (atoms : List Nat) (raw : frameAtoms? mol node = some atoms)
    (three : (mol.canonicalIncidentNeighbors node.atom).length = 3)
    (state : OccurrenceAuxState) (M : List Nat) (mark : Nat) :
    markedJoint? input mol state node M mark = none := by
  cases hrefs : referenceAtoms? input M with
  | none => simp [markedJoint?, hrefs]
  | some references =>
      cases found : lookup? input node with
      | none => simp [markedJoint?, hrefs, jointPartition?, jointFrame?, found]
      | some target =>
          have refused := noFrame_of_three input mol agreement admissible supported single
            node reached atoms raw three target found
          simp [markedJoint?, hrefs, jointPartition?, jointFrame?, found, raw, refused]

/-! ## The context order at a paired actual frame -/

theorem contextOrder?_ordinaryRel_of_setup (mol : RawMolecule)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (node : RawMolecule.CanonicalBranchNode) (atoms atoms' : List Nat)
    (raw : frameAtoms? mol node = some atoms)
    (raw' : frameAtoms? mol (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) = some atoms')
    (setup : Setup input single e node atoms atoms')
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup)
    (L : List Nat) (references : List input.Atom)
    (hrefs : referenceAtoms? input L = some references) :
    OrdinaryRel (relabelOf input (e : Equiv.Perm input.Atom)) atoms atoms'
      (contextOrder? input mol state'
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
        (L.map (relabelOf input (e : Equiv.Perm input.Atom))))
      (contextOrder? input mol state node L) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit setup.target.1, setup.detected⟩
  let W := retainedCarrierFuel input
  let D := 2 * (retainedCarrierFuel input + 1)
  obtain ⟨key, key_eq⟩ : ∃ key : Fin 4 → RefinedKey,
      refinedKey input single state setup.target setup.real unit rfl references W D = key :=
    ⟨_, rfl⟩
  let imageKey := fun slot : Fin 4 => key (setup.frames.slotPerm.symm slot)
  let sourceOrder := keyOrder key (List.finRange 4)
  let imageOrder := keyOrder imageKey (List.finRange 4)
  let sourceBefore := fun a b => some (compare (key a) (key b))
  let imageBefore := fun a b => some (compare (imageKey a) (imageKey b))
  have frameEq : (rawStateFrames input single state setup.target setup.real unit rfl).frame =
      setup.frames.sourceFrame := by
    have h := (rawStateFrames input single state setup.target setup.real unit rfl).frameComputed
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?,
      setup.frames.sourceComputed] at h
    exact (Option.some.inj h).symm
  have sourceCallback : ∀ a b, jointBefore input state setup.target setup.frames.sourceFrame
      references W D a b = sourceBefore a b := by
    intro a b
    have h := jointBefore_eq_refined input single state setup.target setup.real unit rfl
      references W D a b
    rw [frameEq, key_eq] at h
    exact h
  have sourceTotal : ∀ a b, ∃ order,
      rawStateBefore input state setup.target setup.frames.sourceFrame a b = some order := by
    intro a b
    rw [← frameEq]
    exact ⟨_, rawStateBefore_eq_keys input single state setup.target setup.real unit rfl a b⟩
  have imageCallback : ∀ a b, jointBefore input state'
      (input.transportOccurrence single e setup.target) setup.frames.imageFrame
      (references.map e) W D a b = some (compare (imageKey a) (imageKey b)) := by
    intro a b
    have h := jointBefore_transport input single e sym state state' perm unique setup.target
      setup.center setup.frames references W D (setup.frames.slotPerm.symm a)
      (setup.frames.slotPerm.symm b)
    simpa only [Equiv.apply_symm_apply, sourceCallback] using h
  have imageTotal : ∀ a b, ∃ order, rawStateBefore input state'
      (input.transportOccurrence single e setup.target) setup.frames.imageFrame a b = some order := by
    intro a b
    obtain ⟨order, h⟩ := sourceTotal (setup.frames.slotPerm.symm a) (setup.frames.slotPerm.symm b)
    refine ⟨order, ?_⟩
    have h' := rawStateBefore_transport input single e sym state state' perm unique setup.target
      setup.center setup.frames (setup.frames.slotPerm.symm a) (setup.frames.slotPerm.symm b)
    simpa only [Equiv.apply_symm_apply, h] using h'
  have imageHrefs : referenceAtoms? input
      (L.map (relabelOf input (e : Equiv.Perm input.Atom))) = some (references.map e) := by
    rw [referenceAtoms?_map input (e : Equiv.Perm input.Atom) L, hrefs]
    rfl
  have sourceOrd : contextOrder? input mol state node L =
      some (sourceOrder.map setup.sourceRead.index, adjacentBy sourceBefore sourceOrder) := by
    obtain ⟨count, part⟩ := jointPartition?_eq_partition input mol state node setup.target
      setup.found atoms raw setup.frames.sourceFrame
      (by rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?];
          exact setup.frames.sourceComputed)
      setup.sourceRead references W D key sourceCallback sourceTotal
    dsimp only [W, D] at part
    rw [contextOrder?, hrefs]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [part]
    rfl
  have imageOrd : contextOrder? input mol state'
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
      (L.map (relabelOf input (e : Equiv.Perm input.Atom))) =
      some (imageOrder.map setup.imageRead.index, adjacentBy imageBefore imageOrder) := by
    obtain ⟨count, part⟩ := jointPartition?_eq_partition input mol state'
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
      (input.transportOccurrence single e setup.target) setup.imageFound atoms' raw'
      setup.frames.imageFrame
      (by rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?];
          exact setup.frames.imageComputed)
      setup.imageRead (references.map e) W D imageKey (by
        intro a b
        exact imageCallback a b) imageTotal
    dsimp only [W, D] at part
    rw [contextOrder?, imageHrefs]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [part]
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
    have orderEq := keyOrder_transport_of_strict compare refined_compare_lt_iff
      refined_compare_eq_iff setup.frames.slotPerm key imageKey (List.finRange 4)
      (List.finRange 4) (List.nodup_finRange 4) population preserved strict
    rw [setup.imageRead.atoms, setup.sourceRead.atoms]
    change imageOrder.mapM (atomAt input setup.frames.imageFrame) = _
    rw [show imageOrder = sourceOrder.map setup.frames.slotPerm from orderEq]
    exact mapM_atoms_transport input single e setup.target setup.center setup.frames sourceOrder
  · have ties := tied_sorted_transport compare refined_compare_eq_iff
      setup.frames.slotPerm setup.frames.slotPerm.injective key imageKey
      (List.finRange 4) (List.finRange 4) (List.nodup_finRange 4) population preserved
    rw [eligibleOf_tiedEntries, eligibleOf_tiedEntries]
    simp only [setup.imageRead.atom, setup.sourceRead.atom]
    exact (ties.filterMap (atomAt input setup.frames.imageFrame)).trans
      (List.Perm.of_eq (filter_atoms_transport input single e setup.target setup.center setup.frames _))

/-! ## The general contracts at reached occurrences -/

/-- The context order transports for arbitrary unique auxiliary states and the whole accumulated
mark list, mapped by the same atom permutation, at every reached occurrence. -/
theorem contextOrder?_ordinaryRel (mol : RawMolecule)
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
    (unique : (state.map (·.key)).Nodup) (L : List Nat) :
    OrdinaryRel (relabelOf input (e : Equiv.Perm input.Atom)) atoms atoms'
      (contextOrder? input mol state'
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
        (L.map (relabelOf input (e : Equiv.Perm input.Atom))))
      (contextOrder? input mol state node L) := by
  have wf := admissible.1.1
  have uq := admissible.1.2
  have rs := raw_single mol input agreement wf uq supported single
  rcases frame_atoms_perm_neighbors mol wf rs node reached atoms raw with ⟨four, _⟩ | ⟨three, _⟩
  · cases hrefs : referenceAtoms? input L with
    | none =>
        have imageHrefs : referenceAtoms? input
            (L.map (relabelOf input (e : Equiv.Perm input.Atom))) = none := by
          rw [referenceAtoms?_map input (e : Equiv.Perm input.Atom) L, hrefs]
          rfl
        have sourceNone : contextOrder? input mol state node L = none := by
          simp [contextOrder?, hrefs]
        have imageNone : contextOrder? input mol state'
            (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
            (L.map (relabelOf input (e : Equiv.Perm input.Atom))) = none := by
          simp [contextOrder?, imageHrefs]
        rw [sourceNone, imageNone]
        trivial
    | some references =>
        obtain ⟨setup⟩ := setup_exists input mol agreement admissible supported single e sym
          node reached atoms atoms' raw raw' four
        exact contextOrder?_ordinaryRel_of_setup input mol single e sym node atoms atoms'
          raw raw' setup state state' perm unique L references hrefs
  · have imageReached := reached_map sym wf uq rs node reached
    have imageThree : (mol.canonicalIncidentNeighbors
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node).atom).length = 3 := by
      simpa [three] using (neighbors_map sym wf uq node.atom).length_eq
    have sourceNone : contextOrder? input mol state node L = none :=
      contextOrder?_none_of_three input mol agreement admissible supported single node reached
        atoms raw three state L
    have imageNone : contextOrder? input mol state'
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
        (L.map (relabelOf input (e : Equiv.Perm input.Atom))) = none :=
      contextOrder?_none_of_three input mol agreement admissible supported single
        (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node) imageReached atoms' raw'
        imageThree state' (L.map (relabelOf input (e : Equiv.Perm input.Atom)))
    rw [sourceNone, imageNone]
    trivial

/-- Both callbacks use the same actual partition, so extracting the strict atom order
from the marked callback is exactly extracting it from the context callback. -/
theorem markedJoint_bind_eq_context (mol : RawMolecule) (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (L : List Nat) (mark : Nat) (atoms : List Nat) :
    (markedJoint? input mol state node L mark).bind (rankedAtoms? atoms) =
      (contextOrder? input mol state node L).bind (fun result =>
        if strict result.2 then atomsAt? atoms result.1 else none) := by
  unfold markedJoint? contextOrder?
  cases refs : referenceAtoms? input L with
  | none => rfl
  | some references =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases part : jointPartition? input mol state node references
          (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) with
      | none => rfl
      | some result =>
          obtain ⟨positions, adjacent, count⟩ := result
          rfl

private theorem ranked_context_transport (σ : Nat → Nat) (atoms atoms' : List Nat)
    (image source : Option (List Nat × List (Option Ordering)))
    (rel : OrdinaryRel σ atoms atoms' image source) :
    image.bind (fun result => if strict result.2 then atomsAt? atoms' result.1 else none) =
      (source.bind (fun result => if strict result.2 then atomsAt? atoms result.1 else none)).map
        (List.map σ) := by
  cases image with
  | none =>
      cases source with
      | none => rfl
      | some result => rw [ordinaryRel_none_some] at rel; exact rel.elim
  | some imageResult =>
      obtain ⟨sorted', adjacent'⟩ := imageResult
      cases source with
      | none => rw [ordinaryRel_some_none] at rel; exact rel.elim
      | some sourceResult =>
          obtain ⟨sorted, adjacent⟩ := sourceResult
          rw [ordinaryRel_some_some] at rel
          simp only [Option.bind_some, rel.2.1]
          by_cases h : strict adjacent = true
          · simp only [h, ↓reduceIte]
            exact rel.2.2.1 h
          · simp [h]

/-- The joint ranking bound to `rankedAtoms?` transports for arbitrary unique states and the
whole accumulated mark list, with the reference mark relabelled. -/
theorem markedJoint?_bind_transport (mol : RawMolecule)
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
    (unique : (state.map (·.key)).Nodup) (L : List Nat) (r : Nat) :
    (markedJoint? input mol state'
      (mapNode (relabelOf input (e : Equiv.Perm input.Atom)) node)
      (L.map (relabelOf input (e : Equiv.Perm input.Atom)))
      (relabelOf input (e : Equiv.Perm input.Atom) r)).bind (rankedAtoms? atoms') =
    ((markedJoint? input mol state node L r).bind (rankedAtoms? atoms)).map
      (List.map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  rw [markedJoint_bind_eq_context, markedJoint_bind_eq_context]
  exact ranked_context_transport _ _ _ _ _
    (contextOrder?_ordinaryRel input mol agreement admissible supported single e sym
      node reached atoms atoms' raw raw' state state' perm unique L)

/-- Concrete operations instance for the checked prepared-recursion transport theorem. -/
theorem jointOperations_preparedCovariant (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom))) :
    LocalizedChemicalRingJointPreparedCovariance.PreparedCovariant mol
      (jointOperations input mol) (relabelOf input (e : Equiv.Perm input.Atom)) where
  contextOrder node reached atoms atoms' raw raw' M state state' perm unique :=
    contextOrder?_ordinaryRel input mol agreement admissible supported single e sym
      node reached atoms atoms' raw raw' state state' perm unique M
  markedJoint node reached atoms atoms' raw raw' L state state' perm unique mark :=
    markedJoint?_bind_transport input mol agreement admissible supported single e sym
      node reached atoms atoms' raw raw' state state' perm unique L mark

end

end TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.referenceAtoms?_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.eq_map_val_of_referenceAtoms?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.readback_bind_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.jointPartition?_eq_partition
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.markedJoint?_eq_ranked
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.contextOrder?_none_of_three
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.markedJoint?_none_of_three
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.contextOrder?_ordinaryRel_of_setup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.contextOrder?_ordinaryRel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.markedJoint?_bind_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.jointOperations_preparedCovariant

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointOperationTransport.markedJoint_bind_eq_context
