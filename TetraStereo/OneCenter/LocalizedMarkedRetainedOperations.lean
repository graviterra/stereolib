import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.OneCenter.LocalizedMarkedUncappedOperations
import TetraStereo.OneCenter.LocalizedMarkedCarrierLookup
import TetraStereo.OneCenter.LocalizedMarkedFramePositionBridge
import TetraStereo.KernelOnly

set_option autoImplicit false



























namespace TetraStereo.OneCenter.LocalizedMarkedRetainedOperations

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedOperationEvaluator (Operations)
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedCertifiedTerminalRefusal LocalizedMarkedFramePositionBridge
open LocalizedMarkedCarrierLookup RawLocalizedChildNodeTransport
open LocalizedGenericMarkedRecalculation (frameAtoms?)

abbrev Node := RawMolecule.CanonicalBranchNode

variable (input : CertifiedLocalizedCIPInput)

/-- A real raw node is looked up as a real carrier occurrence. -/
theorem lookup?_real (node : Node)
    (occurrence : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some occurrence)
    (rawReal : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  have matched := (rawProvenance?_eq_some_iff _ _).mpr
    (lookup?_sound input node occurrence found).provenance
  rw [rawReal] at matched
  revert matched
  cases occurrence.1.node.provenance <;> simp [rawProvenance?]

/-! ## Raw frame positions of the ranked certified slots -/

/-- Raw frame index of each ranked certified slot, by its current atom. -/
def positions? (atoms : List Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)) :
    List (Fin 4) → Option (List Nat)
  | [] => some []
  | slot :: rest => do
      let atom ← (frame.cursorAt slot).occurrence.1.node.current?
      let position ← atoms.findIdx? (· == atom.val)
      let positions ← positions? atoms frame rest
      some (position :: positions)

/-- Every certified frame cursor carries a current atom that occurs in the raw frame atom list.
Discharged below from the frame-position bridge. -/
def RawFrameAligned (atoms : List Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)) : Prop :=
  ∀ slot, ∃ atom, (frame.cursorAt slot).occurrence.1.node.current? = some atom ∧ atom.val ∈ atoms

theorem positions?_some (atoms : List Nat)
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (aligned : RawFrameAligned input atoms frame) :
    ∀ sorted : List (Fin 4), ∃ positions, positions? input atoms frame sorted = some positions ∧
      positions.length = sorted.length ∧ ∀ position ∈ positions, position < atoms.length
  | [] => ⟨[], rfl, rfl, by simp⟩
  | slot :: rest => by
      obtain ⟨atom, current, member⟩ := aligned slot
      obtain ⟨positions, computed, length, bounded⟩ := positions?_some atoms frame aligned rest
      have found : (atoms.findIdx? (· == atom.val)).isSome = true := by
        rw [List.findIdx?_isSome, List.any_eq_true]
        exact ⟨atom.val, member, beq_self_eq_true _⟩
      obtain ⟨position, positionEq⟩ := Option.isSome_iff_exists.mp found
      obtain ⟨bound, _⟩ := List.findIdx?_eq_some_iff_getElem.mp positionEq
      refine ⟨position :: positions, ?_, by simp [length], ?_⟩
      · simp [positions?, current, positionEq, computed]
      · intro candidate present
        rcases List.mem_cons.mp present with rfl | tail
        · exact bound
        · exact bounded candidate tail

/-! ## The operations instance -/

/-- Ordinary partition of a raw node under a raw state through the retained ranking. -/
def ordinary (mol : RawMolecule) (state : OccurrenceAuxState) (node : Node) :
    Option (List Nat × List (Option Ordering)) := do
  let target ← lookup? input node
  let atoms ← frameAtoms? mol node
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let partition ← ordinaryPartition? input state target
  let positions ← positions? input atoms frame partition.1
  some (positions, partition.2)

/-- Marked operations with the retained ordinary stage. Provisional: the marked (Rule 6)
operation is the existing raw ranker and keeps its known raw-selector discrepancy. -/
def retainedOperations (mol : RawMolecule) : Operations where
  ordinary := ordinary input mol
  marked := LocalizedMarkedUncappedOperations.marked? mol

theorem retainedOperations_ordinary (mol : RawMolecule) :
    (retainedOperations input mol).ordinary = ordinary input mol := rfl

/-- The ordinary operation under an explicit alignment witness: adjacent decisions are the
independent retained key comparisons and positions are in-range raw frame indices. -/
theorem ordinary_eq_of_aligned (mol : RawMolecule) (singleBonded : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (node : Node)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (found : lookup? input node = some target)
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (atoms : List Nat) (rawFrame : frameAtoms? mol node = some atoms)
    (aligned : RawFrameAligned input atoms
      (rawStateFrames input singleBonded state target real unit targetUnit).frame) :
    ∃ positions, ordinary input mol state node =
        some (positions,
          adjacentBy (fun left right => some
            (compare (rawStateKeys input singleBonded state target real unit targetUnit left)
              (rawStateKeys input singleBonded state target real unit targetUnit right)))
            (keyOrder (rawStateKeys input singleBonded state target real unit targetUnit)
              (List.finRange 4))) ∧
      positions.length = 4 ∧ ∀ position ∈ positions, position < atoms.length := by
  obtain ⟨positions, computed, length, bounded⟩ := positions?_some input atoms
    (rawStateFrames input singleBonded state target real unit targetUnit).frame aligned
    (keyOrder (rawStateKeys input singleBonded state target real unit targetUnit)
      (List.finRange 4))
  refine ⟨positions, ?_, ?_, bounded⟩
  · unfold ordinary
    rw [found, rawFrame]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [(rawStateFrames input singleBonded state target real unit targetUnit).frameComputed]
    simp only [Option.bind_some]
    rw [ordinaryPartition?_eq input singleBonded state target real unit targetUnit]
    simp only [Option.bind_some, computed]
  · rw [length, keyOrder, List.length_insertionSort, List.length_finRange]

/-- **Endpoint.** At every raw node reached from an in-range center of a single-bond,
intake-agreeing admitted molecule, whose looked-up carrier occurrence sits at a detected
degree-four atom, the retained ordinary operation succeeds. Lookup, realness, raw frame, retained
compilation and the raw/certified slot permutation are all derived. -/
theorem ordinary_some_of_reached (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (state : OccurrenceAuxState) (center : Nat) (valid : center < mol.atomCount) (node : Node)
    (reached : ReachedFrom mol center node)
    (rawReal : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (detectedTarget : ∀ target, lookup? input node = some target →
      IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom) :
    ∃ (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
      (found : lookup? input node = some target)
      (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      (positions : List Nat),
      ordinary input mol state node =
        some (positions,
          adjacentBy (fun left right => some
            (compare
              (rawStateKeys input singleBonded state target real
                ⟨input.molecularFrameUnit target.1, detectedTarget target found⟩ rfl left)
              (rawStateKeys input singleBonded state target real
                ⟨input.molecularFrameUnit target.1, detectedTarget target found⟩ rfl right)))
            (keyOrder (rawStateKeys input singleBonded state target real
              ⟨input.molecularFrameUnit target.1, detectedTarget target found⟩ rfl)
              (List.finRange 4))) ∧
      positions.length = 4 ∧ ∀ position ∈ positions, position < 4 := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported singleBonded
  obtain ⟨target, found, _, corresponds⟩ := lookup?_exists_of_reachedFrom mol input agreement
    wellFormed unique supported rawSingle center valid node reached
  have real := lookup?_real input node target found rawReal
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit target.1, detectedTarget target found⟩
  obtain ⟨atoms, length, reindex, rawFrame, _nodup, readback⟩ :=
    exists_frame_position_permutation mol input agreement admissible supported singleBonded
      (rawStateDescriptorMap input state) target
      (rawStateFrames input singleBonded state target real unit rfl) node ⟨center, valid, reached⟩
      corresponds
  have aligned : RawFrameAligned input atoms
      (rawStateFrames input singleBonded state target real unit rfl).frame := by
    intro slot
    have read := readback (reindex.symm slot)
    rw [Equiv.apply_symm_apply] at read
    obtain ⟨atom, current, valueEq⟩ := Option.map_eq_some_iff.mp read
    refine ⟨atom, current, ?_⟩
    rw [valueEq]
    exact List.get_mem atoms _
  obtain ⟨positions, computed, lengthFour, bounded⟩ := ordinary_eq_of_aligned input mol
    singleBonded state node target found real unit rfl atoms rawFrame aligned
  refine ⟨target, found, real, positions, computed, lengthFour, ?_⟩
  intro position present
  have bound := bounded position present
  rw [length] at bound
  exact bound

end TetraStereo.OneCenter.LocalizedMarkedRetainedOperations

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOperations.lookup?_real
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOperations.positions?_some
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOperations.retainedOperations
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOperations.ordinary_eq_of_aligned
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedOperations.ordinary_some_of_reached
