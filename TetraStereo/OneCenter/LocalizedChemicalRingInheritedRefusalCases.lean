import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts
import TetraStereo.OneCenter.LocalizedChemicalRingMarkedCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000











namespace TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingFrameReadback
open LocalizedChemicalRingOrderingTransport
open LocalizedChemicalRingCompletenessStrict (rootKeys mapM_eq_some_map consistent_of_gt_or_eq)
open LocalizedChemicalRingCompletenessMarked
  (enumeration slotPerm keyOrder_eq_slots filterMap_eq_map_of strict_iff_injective
   caseFromMirror?_eq_none_iff)
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedOperations LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedPromotedOperations
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedCertifiedTerminalRefusal
open LocalizedMarkedDetectedOrdinaryExecution LocalizedMarkedDetectedFrames
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations sparseOperations_eq)
open LocalizedMarkedOperationEvaluator (markedReading? underWith)
open LocalizedGenericMarkedRecalculation
  (Geometry frameAtoms? frameAtomsOf readback? atomsAt? rankedAtoms? consistent strict
   caseFromMirror? mirror readback_mirror eligibleOf consensus appendFacts?)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open RawLocalizedChildNodeTransport
open scoped Classical

abbrev Node := RawMolecule.CanonicalBranchNode

section Data
variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center)

structure OccurrenceData (node : Node) where
  target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)
  found : lookup? input node = some target
  real : target.1.node.provenance = .realAtom
  detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom
  atoms : List Nat
  rawFrame : frameAtoms? mol node = some atoms
  nodup : atoms.Nodup
  frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)
  frameExec : input.localizedNoDoubleFourLigandFrameExec? target = some frame
  read : Readback input atoms frame
  /-- Frame slot to ligand index of the detected multi-centre molecule. -/
  ligandOf : Equiv.Perm (Fin 4)
  atomAt_eq : ∀ slot, atomAt input frame slot =
    some (input.detectedMultiCenterMolecule.ligandAtomAt c (ligandOf slot)).val

include agreement admissible supported single in
theorem occurrenceData_exists (node : Node) (reached : Reached mol node)
    (rawReal : node.provenance = .realAtom) (current : node.atom = c.1.val) :
    Nonempty (OccurrenceData input mol c node) := by
  classical
  have wf := admissible.1.1
  have uq := admissible.1.2
  have rs := raw_single mol input agreement wf uq supported single
  obtain ⟨root, valid, path⟩ := reached
  have reached : Reached mol node := ⟨root, valid, path⟩
  obtain ⟨target, found, _, corresponds⟩ := lookup?_exists_of_reachedFrom mol input agreement wf uq
    supported rs root valid node path
  have real := lookup?_real input _ target found rawReal
  have detected := lookup_detected_of_physical_center mol input agreement admissible supported
    single c node current target found
  let unit : DetectedOccurrence input.moleculeGraph := ⟨input.molecularFrameUnit target.1, detected⟩
  let execution := rawStateFrames input single [] target real unit rfl
  have computed : input.localizedOccurrenceFourLigandFrame? target = some execution.frame := by
    have h := execution.frameComputed
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?] at h
    exact h
  have rawFrame := detected_frame mol input agreement admissible supported single c node
    reached rawReal current
  have degree := detected_raw_degree mol input agreement wf uq supported c
  have perm : (frameAtomsOf (occurrenceLigandCursors mol node)).Perm
      (mol.canonicalIncidentNeighbors node.atom) := by
    rcases frame_atoms_perm_neighbors mol wf rs _ reached _ rawFrame with ⟨_, perm⟩ | ⟨three, _⟩
    · exact perm
    · have three' : (mol.canonicalIncidentNeighbors node.atom).length = 3 := three
      rw [current, degree] at three'
      cases three'
  have nodup : (frameAtomsOf (occurrenceLigandCursors mol node)).Nodup :=
    perm.nodup_iff.mpr (mol.canonicalIncidentNeighbors_nodup _ uq)
  obtain ⟨read⟩ := readback_exists input mol agreement admissible supported single _ reached target
    found real detected _ rawFrame execution.frame computed
  have meaning := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    execution.center).mp execution.centerComputed
  obtain ⟨frame', ligand, computed', frameCurrent⟩ :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv single
      (Nat.le_succ _) target execution.center meaning
  have frameEq : frame' = execution.frame := Option.some.inj (computed'.symm.trans computed)
  subst frameEq
  have centerEq : execution.center.1 = c.1 := by
    have h := corresponds.current
    rw [meaning.2] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact Fin.ext (h.trans current)
  have hc := (input.moleculeGraph.mem_tetrahedralCenterSet c.1).mp c.2
  let β : Fin 4 → Fin 4 := fun slot =>
    (input.moleculeGraph.ligandEquivOfIsTetrahedralCenter c.1 hc).symm
      ⟨(ligand slot).1, by rw [← centerEq]; exact (ligand slot).2⟩
  have βinj : Function.Injective β := by
    intro a b eq
    have := (input.moleculeGraph.ligandEquivOfIsTetrahedralCenter c.1 hc).symm.injective eq
    have vals : (ligand a).1 = (ligand b).1 := by
      have h := congrArg Subtype.val this
      exact h
    exact ligand.injective (Subtype.ext vals)
  refine ⟨⟨target, found, real, detected, _, rawFrame, nodup, execution.frame, execution.frameComputed,
    read, Equiv.ofBijective β (Finite.injective_iff_bijective.mp βinj), ?_⟩⟩
  intro slot
  simp only [atomAt, frameCurrent slot, Option.map_some, Equiv.ofBijective_apply]
  show some (ligand slot).1.val =
    some ((input.moleculeGraph.ligandEquivOfIsTetrahedralCenter c.1 hc (β slot)).1).val
  simp only [β, Equiv.apply_symm_apply]

end Data

section Occurrence
variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : Node)
  (data : OccurrenceData input mol c node)

noncomputable abbrev ordinaryKeys := rootKeys input single data.target data.real data.detected

noncomputable abbrev order := keyOrder (ordinaryKeys input mol single c node data) (List.finRange 4)

noncomputable abbrev adjacent := adjacentBy
  (fun a b => some (compare (ordinaryKeys input mol single c node data a)
    (ordinaryKeys input mol single c node data b))) (order input mol single c node data)

noncomputable def rank {K : Type} [LinearOrder K] (keys : Fin 4 → K) : Equiv.Perm (Fin 4) :=
  (slotPerm keys).trans data.ligandOf

theorem ranked_eq {K : Type} [LinearOrder K] (keys : Fin 4 → K) :
    atomsAt? data.atoms ((keyOrder keys (List.finRange 4)).map data.read.index) =
      some (enumeration input c (rank input mol c node data keys)) := by
  rw [data.read.atoms, mapM_eq_some_map _
    (fun slot => (input.detectedMultiCenterMolecule.ligandAtomAt c (data.ligandOf slot)).val) _
    (fun slot _ => data.atomAt_eq slot), keyOrder_eq_slots]
  rfl

theorem ordinary_eq :
    (sparseOperations input mol).ordinary [] node =
      some ((order input mol single c node data).map data.read.index,
        adjacent input mol single c node data) := by
  change LocalizedMarkedRetainedOperations.ordinary input mol [] node = _
  unfold LocalizedMarkedRetainedOperations.ordinary
  rw [data.found, data.rawFrame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [data.frameExec]
  simp only [Option.bind_some]
  rw [ordinaryPartition?_eq input single [] data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl]
  simp only [Option.bind_some]
  rw [data.read.positions]
  rfl

theorem consistent_eq : consistent (adjacent input mol single c node data) = true :=
  consistent_of_gt_or_eq _ (adjacentBy_key_consistent compare
    completeLigandRule5Key_compare_lt_iff completeLigandRule5Key_compare_eq_iff _ _
    (keyOrder_pairwise _ _))

noncomputable def markedKeys (temp : OccurrenceAuxState) (reference : input.Atom) :
    Fin 4 → RefinedKey :=
  refinedKey input single temp data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))

/-- The actual marked reading at an arbitrary reached occurrence, with no assumed sort. -/
theorem marked_reading_eq (geom : Geometry) (temp : OccurrenceAuxState) (reference : input.Atom) :
    markedReading? mol (sparseOperations input mol) geom temp node reference.val =
      if Function.Injective (markedKeys input mol single c node data temp reference) then
        readback? geom (enumeration input c
          (rank input mol c node data (markedKeys input mol single c node data temp reference)))
      else none := by
  have frameEq : (rawStateFrames input single temp data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame = data.frame := by
    have h := (rawStateFrames input single temp data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frameComputed
    rw [data.frameExec] at h
    exact (Option.some.inj h).symm
  have callback : ∀ a b, LocalizedMarkedRetainedPromotedRanking.before input temp data.target
      reference (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) data.frame a b =
      some (compare (markedKeys input mol single c node data temp reference a)
        (markedKeys input mol single c node data temp reference b)) := by
    intro a b
    have h := before_eq_refined input single temp data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) a b
    rw [frameEq] at h
    exact h
  have ordinaryTotal : ∀ a b, ∃ decision, rawStateBefore input temp data.target data.frame a b =
      some decision := by
    intro a b
    have h := rawStateBefore_eq_keys input single temp data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl a b
    rw [frameEq] at h
    exact ⟨_, h⟩
  have ranked := LocalizedChemicalRingMarkedCovariance.ranked_eq input mol
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) temp node data.target
    data.found data.atoms data.rawFrame data.frame data.frameExec data.read reference
    (markedKeys input mol single c node data temp reference) callback ordinaryTotal
  rw [sparseOperations_eq]
  unfold markedReading?
  rw [data.rawFrame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  change ((markedWithLayout? input mol (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) temp node reference.val).bind fun ranking =>
      (rankedAtoms? data.atoms ranking).bind (readback? geom)) = _
  rw [← Option.bind_assoc, ranked]
  have atoms := ranked_eq input mol c node data
    (markedKeys input mol single c node data temp reference)
  rw [data.read.atoms] at atoms
  by_cases injective : Function.Injective (markedKeys input mol single c node data temp reference)
  · rw [if_pos ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mpr injective), atoms, Option.bind_some, if_pos injective]
  · rw [if_neg (fun h => injective ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mp h)), Option.bind_none, if_neg injective]

/-- Actual eligible references, indexed by their certified occurrence-frame slots. -/
noncomputable def eligibleSlots : List (Fin 4) :=
  tiedEntries false (order input mol single c node data) (adjacent input mol single c node data)

noncomputable def referenceAt (slot : Fin 4) : input.Atom :=
  input.detectedMultiCenterMolecule.ligandAtomAt c (data.ligandOf slot)

theorem eligible_eq :
    eligibleOf data.atoms ((order input mol single c node data).map data.read.index)
        (adjacent input mol single c node data) =
      (eligibleSlots input mol single c node data).map
        (fun i => (referenceAt input mol c node data i).val) := by
  rw [eligibleOf_tiedEntries]
  apply filterMap_eq_map_of
  intro slot _
  simp only [data.read.atom slot, data.atomAt_eq slot, referenceAt]

theorem eligible_ne_nil (notInj : ¬ Function.Injective (ordinaryKeys input mol single c node data)) :
    eligibleSlots input mol single c node data ≠ [] := by
  intro empty
  apply notInj
  intro a b equal
  by_contra ne
  have member : b ∈ eligibleSlots input mol single c node data := by
    apply (tiedEntries_mem compare completeLigandRule5Key_compare_eq_iff _ _
      ((keyOrder_perm _ _).nodup_iff.mpr (List.nodup_finRange 4))
      (keyOrder_pairwise _ _) b).mpr
    exact ⟨(keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange b), a,
      (keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange a), ne, equal⟩
  rw [empty] at member
  simp at member

noncomputable def reading (geom : Geometry) (under : Nat → OccurrenceAuxState) (slot : Fin 4) :
    Option RS :=
  LocalizedPhysicalMarkedDistantReference.inheritedRead? mol (sparseOperations input mol)
    geom [] node under (referenceAt input mol c node data slot).val

/-- Removes every ordinary-stage structural refusal using the actual compiled keys. -/
theorem noContext_eq (geom : Geometry) (under : Nat → OccurrenceAuxState) :
    LocalizedPhysicalMarkedDistantReference.rawStep? mol (sparseOperations input mol)
        geom [] none node under =
      if Function.Injective (ordinaryKeys input mol single c node data) then
        readback? geom (enumeration input c
          (rank input mol c node data (ordinaryKeys input mol single c node data)))
      else consensus ((eligibleSlots input mol single c node data).map
        (reading input mol c node data geom under)) := by
  unfold LocalizedPhysicalMarkedDistantReference.rawStep?
  rw [data.rawFrame, ordinary_eq input mol single c node data]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have good : ¬ (¬ data.atoms.Nodup ∨ consistent (adjacent input mol single c node data) = false) := by
    rw [consistent_eq input mol single c node data]
    simp [data.nodup]
  rw [if_neg good]
  by_cases inj : Function.Injective (ordinaryKeys input mol single c node data)
  · rw [if_pos ((strict_iff_injective compare completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff _).mpr inj), ranked_eq input mol c node data,
      Option.bind_some, if_pos inj]
  · rw [if_neg (fun h => inj ((strict_iff_injective compare completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff _).mp h)), if_neg inj]
    change consensus _ = _
    rw [eligible_eq input mol single c node data, List.map_map]
    rfl

end Occurrence

private theorem consensus_none_iff {α : Type} (xs : List α) (f : α → Option RS)
    (nonempty : xs ≠ []) :
    consensus (xs.map f) = none ↔
      (∃ a ∈ xs, f a = none) ∨
      ∃ a ∈ xs, ∃ b ∈ xs, ∃ va vb, f a = some va ∧ f b = some vb ∧ va ≠ vb := by
  constructor
  · intro refused
    by_cases missing : ∃ a ∈ xs, f a = none
    · exact Or.inl missing
    · right
      have success : ∀ a ∈ xs, ∃ v, f a = some v := by
        intro a ha
        cases h : f a with
        | none => exact False.elim (missing ⟨a, ha, h⟩)
        | some v => exact ⟨v, rfl⟩
      cases xs with
      | nil => exact False.elim (nonempty rfl)
      | cons a rest =>
          obtain ⟨va, ha⟩ := success a List.mem_cons_self
          by_contra noDisagreement
          have all : ∀ b ∈ a :: rest, f b = some va := by
            intro b hb
            obtain ⟨vb, hbb⟩ := success b hb
            by_cases eq : va = vb
            · simpa only [eq] using hbb
            · exact False.elim (noDisagreement ⟨a, List.mem_cons_self, b, hb, va, vb, ha, hbb, eq⟩)
          have someValue : consensus ((a :: rest).map f) = some va := by
            rw [consensus_eq_some_iff]
            refine ⟨by simp, ?_⟩
            intro value member
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp member
            exact all b hb
          rw [refused] at someValue
          cases someValue
  · rintro (⟨a, ha, none⟩ | ⟨a, ha, b, hb, va, vb, fa, fb, ne⟩)
    · exact LocalizedChemicalRingCompletenessMarked.consensus_map_none xs f a ha none
    · exact LocalizedChemicalRingCompletenessMarked.consensus_map_disagree xs f a b ha hb va vb fa fb ne

private theorem candidate_none_iff (mol : RawMolecule)
    (ops : LocalizedMarkedOperationEvaluator.Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) :
    LocalizedChemicalRingInheritedFallback.rawStep? mol ops geom state ctx node under = none ↔
      LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under = none ∧
      LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under = none := by
  constructor
  · intro refused
    have first : LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under = none := by
      cases found : LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state ctx node under with
      | none => rfl
      | some value =>
          have actual := LocalizedChemicalRingInheritedFallback.rawStep_preserves_some
            mol ops geom state ctx node under value found
          rw [refused] at actual
          cases actual
    refine ⟨first, ?_⟩
    cases found : LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under with
    | none => rfl
    | some value =>
        have actual := (LocalizedChemicalRingInheritedFallback.rawStep_eq_some_iff
          mol ops geom state ctx node under value).mpr (Or.inr ⟨first, found⟩)
        rw [refused] at actual
        cases actual
  · rintro ⟨first, fallback⟩
    cases actual : LocalizedChemicalRingInheritedFallback.rawStep? mol ops geom state ctx node under with
    | none => rfl
    | some value =>
        rcases (LocalizedChemicalRingInheritedFallback.rawStep_eq_some_iff
          mol ops geom state ctx node under value).mp actual with inherited | added
        · rw [first] at inherited
          cases inherited
        · rw [fallback] at added
          cases added.2


section Generated
variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
  (node : Node) (data : OccurrenceData input mol c node)

def observedGeometry (reflected : Bool) : Geometry :=
  if reflected then mirror (inputGeometry input) else inputGeometry input

include calibrated in
theorem readback_some (reflected : Bool) (π : Equiv.Perm (Fin 4)) :
    ∃ value, readback? (observedGeometry input reflected) (enumeration input c π) = some value := by
  have h := LocalizedChemicalRingCompletenessMarked.readback_enum input cfg c calibrated π
  cases reflected
  · exact ⟨_, h⟩
  · change ∃ value, readback? (mirror (inputGeometry input)) (enumeration input c π) = some value
    rw [readback_mirror, h]
    exact ⟨_, rfl⟩

/-- The actual candidate forest for this call, retaining its depth and full occurrence history. -/
noncomputable def generated (depth : Nat) (reflected : Bool) (mark : Nat) : OccurrenceAuxState :=
  underWith mol (sparseOperations input mol) (observedGeometry input reflected) [] node
    (factsWith LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol) depth) mark

noncomputable def generatedReading (depth : Nat) (reflected : Bool) (slot : Fin 4) : Option RS :=
  reading input mol c node data (observedGeometry input reflected)
    (generated input mol node depth reflected) slot

include calibrated in
/-- A missing eligible reading is exactly a tie of actual default-layout marked keys.
Generated facts pass insertion and a strict marked order always has calibrated readback. -/
theorem generatedReading_none_iff
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (depth : Nat) (reflected : Bool) (slot : Fin 4) :
    generatedReading input mol c node data depth reflected slot = none ↔
      ∃ left right : Fin 4, left ≠ right ∧
        markedKeys input mol single c node data
          (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
          (referenceAt input mol c node data slot) left =
        markedKeys input mol single c node data
          (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
          (referenceAt input mol c node data slot) right := by
  have extension := LocalizedChemicalRingCompletenessGeneratedFacts.extension_succeeds
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
    admissible.1.1 (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 depth (observedGeometry input reflected) node
    (referenceAt input mol c node data slot).val
  change appendFacts? [] (generated input mol node depth reflected
    (referenceAt input mol c node data slot).val) =
      some (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
    at extension
  unfold generatedReading reading LocalizedPhysicalMarkedDistantReference.inheritedRead?
  change ((appendFacts? [] (generated input mol node depth reflected
    (referenceAt input mol c node data slot).val)).bind fun temp =>
      markedReading? mol (sparseOperations input mol) (observedGeometry input reflected) temp node
        (referenceAt input mol c node data slot).val) = none ↔ _
  rw [extension, Option.bind_some, marked_reading_eq input mol single c node data]
  let keys := markedKeys input mol single c node data
    (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
    (referenceAt input mol c node data slot)
  change (if Function.Injective keys then readback? (observedGeometry input reflected)
    (enumeration input c (rank input mol c node data keys)) else none) = none ↔ _
  by_cases inj : Function.Injective keys
  · obtain ⟨value, success⟩ := readback_some input cfg c calibrated reflected
      (rank input mol c node data keys)
    rw [if_pos inj, success]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨a, b, ne, eq⟩
      exact False.elim (ne (inj eq))
  · rw [if_neg inj]
    constructor
    · intro _
      obtain ⟨a, b, eq, ne⟩ := Function.not_injective_iff.mp inj
      exact ⟨a, b, ne, eq⟩
    · intro _; rfl

/-- The two actual remaining failure modes on the generated forest for one geometry. -/
def ReadingFailure (depth : Nat) (reflected : Bool) : Prop :=
  (∃ slot ∈ eligibleSlots input mol single c node data,
    ∃ left right : Fin 4, left ≠ right ∧
      markedKeys input mol single c node data
        (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
        (referenceAt input mol c node data slot) left =
      markedKeys input mol single c node data
        (generated input mol node depth reflected (referenceAt input mol c node data slot).val)
        (referenceAt input mol c node data slot) right) ∨
  ∃ first ∈ eligibleSlots input mol single c node data,
    ∃ second ∈ eligibleSlots input mol single c node data, ∃ a b,
      generatedReading input mol c node data depth reflected first = some a ∧
      generatedReading input mol c node data depth reflected second = some b ∧ a ≠ b


def SideFailure (depth : Nat) (ctx : Option Nat) (reflected : Bool) : Prop :=
  LocalizedPhysicalMarkedDistantReference.rawStep? mol (sparseOperations input mol)
    (observedGeometry input reflected) [] ctx node
    (generated input mol node depth reflected) = none ∧
  ReadingFailure input mol single c node data depth reflected

include calibrated in
theorem noContext_none_iff
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (depth : Nat) (reflected : Bool) :
    LocalizedPhysicalMarkedDistantReference.rawStep? mol (sparseOperations input mol)
        (observedGeometry input reflected) [] none node
        (generated input mol node depth reflected) = none ↔
      ¬ Function.Injective (ordinaryKeys input mol single c node data) ∧
        ReadingFailure input mol single c node data depth reflected := by
  rw [noContext_eq input mol single c node data]
  by_cases inj : Function.Injective (ordinaryKeys input mol single c node data)
  · obtain ⟨value, success⟩ := readback_some input cfg c calibrated reflected
      (rank input mol c node data (ordinaryKeys input mol single c node data))
    rw [if_pos inj, success]
    constructor
    · intro impossible; cases impossible
    · rintro ⟨notInj, _⟩
      exact False.elim (notInj inj)
  · rw [if_neg inj]
    have classify := consensus_none_iff (eligibleSlots input mol single c node data)
      (generatedReading input mol c node data depth reflected)
      (eligible_ne_nil input mol single c node data inj)
    change consensus ((eligibleSlots input mol single c node data).map
      (generatedReading input mol c node data depth reflected)) = none ↔ _
    rw [classify]
    simp only [inj, not_false_eq_true, true_and]
    unfold ReadingFailure
    apply or_congr
    · apply exists_congr
      intro slot
      apply and_congr_right
      intro _
      exact generatedReading_none_iff input mol single cfg c calibrated node data
        agreement admissible supported depth reflected slot
    · rfl

include calibrated in
/-- Exact actual-step refusal; all structural and geometric failures have been discharged. -/
theorem step_none_iff
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (depth : Nat) (ctx : Option Nat) (reflected : Bool) :
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
        (observedGeometry input reflected) [] ctx node
        (generated input mol node depth reflected) = none ↔
      ¬ Function.Injective (ordinaryKeys input mol single c node data) ∧
        SideFailure input mol single c node data depth ctx reflected := by
  rw [candidate_none_iff, noContext_none_iff input mol single cfg c calibrated node data
    agreement admissible supported depth reflected]
  exact ⟨fun ⟨inherited, tied, cases⟩ => ⟨tied, inherited, cases⟩,
    fun ⟨tied, inherited, cases⟩ => ⟨inherited, tied, cases⟩⟩

include calibrated in
/-- Exact descriptor refusal at the retained call depth and inherited context, under the
original or mirrored geometry. No successful comparison, selected label or symmetry is assumed. -/
theorem descriptor_none_iff
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (depth : Nat) (ctx : Option Nat) :
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
        depth (inputGeometry input) [] ctx node = none ↔
      ¬ Function.Injective (ordinaryKeys input mol single c node data) ∧
        (SideFailure input mol single c node data depth ctx false ∨
         SideFailure input mol single c node data depth ctx true) := by
  unfold LocalizedChemicalRingInheritedFallback.descriptor? descriptorWith
  rw [caseFromMirror?_eq_none_iff]
  change (LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input false) [] ctx node (generated input mol node depth false) = none ∨
    LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
      (observedGeometry input true) [] ctx node (generated input mol node depth true) = none) ↔ _
  rw [step_none_iff input mol single cfg c calibrated node data agreement admissible supported
      depth ctx false,
    step_none_iff input mol single cfg c calibrated node data agreement admissible supported
      depth ctx true]
  exact ⟨fun h => h.elim (fun ⟨t, f⟩ => ⟨t, Or.inl f⟩) (fun ⟨t, f⟩ => ⟨t, Or.inr f⟩),
    fun ⟨t, f⟩ => f.elim (fun f => Or.inl ⟨t, f⟩) (fun f => Or.inr ⟨t, f⟩)⟩

include calibrated in
/-- Input-facing refusal classification. The occurrence data and every operational success
fact used above are constructed from the actual reached, real, detected occurrence. -/
theorem reached_descriptor_refusal
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (reached : Reached mol node) (real : node.provenance = .realAtom)
    (current : node.atom = c.1.val) (depth : Nat) (ctx : Option Nat)
    (refused : LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
      depth (inputGeometry input) [] ctx node = none) :
    ∃ data : OccurrenceData input mol c node,
      ¬ Function.Injective (ordinaryKeys input mol single c node data) ∧
        (SideFailure input mol single c node data depth ctx false ∨
         SideFailure input mol single c node data depth ctx true) := by
  obtain ⟨actual⟩ := occurrenceData_exists input mol agreement admissible supported single c node
    reached real current
  exact ⟨actual, (descriptor_none_iff input mol single cfg c calibrated node actual
    agreement admissible supported depth ctx).mp refused⟩

end Generated
end TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.occurrenceData_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.ranked_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.ordinary_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.consistent_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.marked_reading_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.eligible_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.eligible_ne_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.noContext_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.readback_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.generatedReading_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.noContext_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.step_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.descriptor_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases.reached_descriptor_refusal
