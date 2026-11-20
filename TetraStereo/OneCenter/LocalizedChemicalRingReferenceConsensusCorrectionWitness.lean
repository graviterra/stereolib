import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusReflection
import TetraStereo.OneCenter.LocalizedChemicalRingCorrectedWitnessRefusal
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
**A correction witness read on the original geometry, from an actual tie on either geometry.**

An actual marked-key tie on the reflected state gives a matched symmetry for that state. Reflection
acts entrywise on facts, so its label equalities are label equalities of the original state; only
those are consumed here. The witness also carries an injective refinement of its deletion rank.

`step` is the ordinary correction step for this witness: a correction fixing the boundary, the low
ranks and the reference leaves either all source signs proper, or a highest negative center whose
actual descriptor refuses under the same reference. No current-center sign or successful label is
assumed; higher-rank properness remains an induction invariant. This does not construct the next
correction.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingShiftedReferenceWitness LocalizedChemicalRingRankedCorrectionTransport
open LocalizedChemicalRingRankedReconstruction LocalizedChemicalRingRelabel
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingWitnessRawDescent
open LocalizedChemicalRingMovedSlotEligibility (matched_child_selected)
open LocalizedChemicalRingSelectedFactCompleteness (candidate_absence_refusal)
open LocalizedChemicalRingReferenceConsensusReflection
open LocalizedChemicalRingOrientationReadback (flipDescriptorBy flipDescriptorBy_some_eq)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut actual_covariant)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedTerminalReferenceScope (Descends)
open LocalizedMarkedOperationEvaluator (tiedChildren)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedGenericMarkedRecalculation (structuralDepth mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

/-! ## Labels under reflection -/

private def labelMirror : LocalizedAuxiliaryLabel → LocalizedAuxiliaryLabel
  | .chiral d => .chiral d.swap
  | .pseudoasymmetric x => .pseudoasymmetric x

private theorem labelMirror_injective : Function.Injective labelMirror := by
  rintro (d | x) (d' | x') same
  · have letters : d.swap = d'.swap := LocalizedTetrahedralRSPseudoDescriptor.chiral.inj same
    cases d <;> cases d' <;> first | rfl | cases letters
  · cases same
  · cases same
  · exact same

private theorem factLabel_mirror (fact : OccurrenceAuxFact) :
    factLabel (mirrorFact fact) = labelMirror (factLabel fact) := by
  rcases fact with ⟨key, atom, descriptor, uppercase, positions⟩
  cases uppercase <;> cases descriptor <;> rfl

private theorem factAt_mirror (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode) :
    OccurrenceAuxState.factAt? (state.map mirrorFact) node = (state.factAt? node).map mirrorFact := by
  unfold OccurrenceAuxState.factAt?
  rw [List.find?_map]
  congr 1
  apply congrArg (fun p => List.find? p state)
  funext fact
  simp only [Function.comp, mirrorFact_key]

/-- Equal actual labels in a reflected state are equal labels in the original state. -/
theorem labels_of_mirror (state : OccurrenceAuxState) (x y : RawMolecule.CanonicalBranchNode)
    (same : (OccurrenceAuxState.factAt? (state.map mirrorFact) x).map factLabel =
      (OccurrenceAuxState.factAt? (state.map mirrorFact) y).map factLabel) :
    (state.factAt? x).map factLabel = (state.factAt? y).map factLabel := by
  rw [factAt_mirror, factAt_mirror] at same
  cases first : state.factAt? x <;> cases second : state.factAt? y <;>
    simp only [first, second, Option.map_none, Option.map_some, Option.some.injEq,
      reduceCtorEq, factLabel_mirror] at same ⊢
  exact labelMirror_injective same

/-! ## An injective refinement of a deletion rank -/

section Refine

variable {V : Type*} [Fintype V]

/-- A rank refined by a tie-breaking index. Strict comparisons of the original rank are kept. -/
def refineRank (rank : V → Nat) (x : V) : Nat :=
  rank x * (Fintype.card V + 1) + (Fintype.equivFin V x).val

theorem refineRank_lt (rank : V → Nat) {x y : V} (lower : rank x < rank y) :
    refineRank rank x < refineRank rank y := by
  unfold refineRank
  have bound : (Fintype.equivFin V x).val < Fintype.card V + 1 :=
    Nat.lt_succ_of_lt (Fintype.equivFin V x).isLt
  have step : (rank x + 1) * (Fintype.card V + 1) ≤ rank y * (Fintype.card V + 1) :=
    Nat.mul_le_mul_right _ lower
  rw [Nat.add_mul, Nat.one_mul] at step
  omega

theorem refineRank_injective (rank : V → Nat) : Function.Injective (refineRank rank) := by
  intro x y same
  rcases lt_trichotomy (rank x) (rank y) with lower | equal | higher
  · exact absurd same (Nat.ne_of_lt (refineRank_lt rank lower))
  · unfold refineRank at same
    rw [equal] at same
    exact (Fintype.equivFin V).injective (Fin.ext (Nat.add_left_cancel same))
  · exact absurd same.symm (Nat.ne_of_lt (refineRank_lt rank higher))

end Refine

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (reference : input.Atom)

/-- The original-geometry generated state under one reference. -/
abbrev originalState : OccurrenceAuxState :=
  snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? input mol
    (structuralDepth mol node) (inputGeometry input) node reference.val

/-- What a correction consumes from one actual tie: one symmetry, an injective rank, the actual
descent of its witness paths, and label equalities in the original-geometry state. -/
structure CorrectionWitness (a b : input.Atom) where
  symmetry : input.detectedMultiCenterMolecule.Aut
  rank : input.Atom → Nat
  rankInjective : Function.Injective rank
  fixedHistory : ∀ atom ∈ data.target.1.node.history, (symmetry : Equiv.Perm input.Atom) atom = atom
  entry : (symmetry : Equiv.Perm input.Atom) a = b
  fixedReference : (symmetry : Equiv.Perm input.Atom) reference = reference
  execution : ∀ (p : List input.Atom),
    ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p →
    ∃ child ∈ tiedChildren mol (sparseOperations input mol) [] node,
      Descends mol child (rawPathNode data.target.1.root (boundaryPath data.target p)) ∧
      (rawPathNode data.target.1.root (boundaryPath data.target p)).history.length ≤
        structuralDepth mol node + node.history.length
  matched : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
    ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p},
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      ((originalState input mol node reference).factAt?
          (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel =
        ((originalState input mol node reference).factAt?
          (rawPathNode data.target.1.root
            (boundaryPath data.target (p.1.map (symmetry : Equiv.Perm input.Atom))))).map factLabel ∧
      (∀ y ∈ p.1.dropLast, rank y < rank d.1) ∧
      ∀ y, InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast) d.1 y →
        y ≠ d.1 → rank d.1 < rank y

/-- The generated state of either geometry side, at the structural depth. -/
abbrev sideState (reflected : Bool) : OccurrenceAuxState :=
  generated input mol node (structuralDepth mol node) reflected reference.val

theorem sideState_true :
    sideState input mol node reference true = (originalState input mol node reference).map mirrorFact :=
  underWith_mirror LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations input mol)
    (structuralDepth mol node) (inputGeometry input) [] node reference.val

private theorem side_labels (reflected : Bool) (x y : RawMolecule.CanonicalBranchNode)
    (same : ((sideState input mol node reference reflected).factAt? x).map factLabel =
      ((sideState input mol node reference reflected).factAt? y).map factLabel) :
    ((originalState input mol node reference).factAt? x).map factLabel =
      ((originalState input mol node reference).factAt? y).map factLabel := by
  cases reflected with
  | false => exact same
  | true =>
      rw [sideState_true] at same
      exact labels_of_mirror _ x y same

include agreement admissible supported reached in
/-- Reading a matched symmetry of either side as a correction witness. -/
theorem exists_correctionWitness (single : input.moleculeGraph.SimpleBonded) (reflected : Bool)
    (left right : Fin 4) (a b : input.Atom) (distinct : a ≠ b)
    (w : MatchedSymmetry input single (sideState input mol node reference reflected) data.target
      data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference left right a b) :
    ∃ W : CorrectionWitness input mol c node data reference a b,
      (W.symmetry : Equiv.Perm input.Atom) = w.symmetry := by
  refine ⟨{
    symmetry := w.symmetry
    rank := refineRank w.rank
    rankInjective := refineRank_injective w.rank
    fixedHistory := w.fixedHistory
    entry := w.entry
    fixedReference := w.fixedReference
    execution := ?_
    matched := ?_ }, rfl⟩
  · intro p valid
    have fresh : a ∉ data.target.1.node.history := by
      intro present
      exact distinct ((w.fixedHistory a present).symm.trans w.entry)
    obtain ⟨child, actualChild, atChild, _, descent⟩ :=
      actual_fresh_boundary_path_descent input mol agreement admissible supported single node reached
        _ data.target data.found data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
        left a w.leftCurrent w.leftReal fresh p valid
    have selected := matched_child_selected input mol agreement admissible supported single c node
      data reached _ reference left right a b distinct w child actualChild atChild
    exact ⟨child, selected, descent,
      boundary_query_adequate input mol agreement single data.target data.real a p valid node⟩
  · intro d member
    obtain ⟨p, terminal, _, labels, lower, higher⟩ := w.matched d member
    exact ⟨p, terminal, side_labels input mol node reference reflected _ _ labels,
      fun y present => refineRank_lt w.rank (lower y present),
      fun y residual different => refineRank_lt w.rank (higher y residual different)⟩

variable {reference} {a b : input.Atom}
  (W : CorrectionWitness input mol c node data reference a b)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (correction : input.detectedMultiCenterMolecule.Aut) (bound : Nat)
  (boundaryFixed : ∀ atom ∈ data.target.1.node.history,
    (correction : Equiv.Perm input.Atom) atom = atom)
  (lowFixed : ∀ atom, W.rank atom ≤ bound → (correction : Equiv.Perm input.Atom) atom = atom)
  (higherProper : ∀ d : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
    bound < W.rank d.1 →
    relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d = 1)
  (referenceFixed : (correction : Equiv.Perm input.Atom) reference = reference)

include agreement admissible supported single reached calibrated boundaryFixed lowFixed higherProper
  referenceFixed in
/-- **One correction step.** All source signs are proper, or the highest negative center has an
actual descriptor refusal under the same reference, on its witness path. -/
theorem step :
    (∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d = 1) ∨
    ∃ (d : input.detectedMultiCenterMolecule.Center)
      (p : {p : List input.Atom //
        ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p}),
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 ∧
      pathTerminal p.1 p.2.nonempty = d.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d = -1 ∧
      W.rank d.1 ≤ bound ∧
      (∀ y ∈ p.1.dropLast, W.rank y < W.rank d.1) ∧
      (∀ y, InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
        d.1 y → y ≠ d.1 → W.rank d.1 < W.rank y) ∧
      (∀ other : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph data.target.1.node.history.reverse a other.1 →
        W.rank d.1 < W.rank other.1 →
        relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) other = 1) ∧
      LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations input mol)
        (structuralDepth mol node + node.history.length -
          (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length)
        (inputGeometry input) [] (some reference.val)
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)) = none := by
  let action := W.symmetry * correction
  by_cases allProper : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
      relativeSign input.detectedMultiCenterMolecule cfg action d = 1
  · exact Or.inl allProper
  right
  let bad := Finset.univ.filter fun d : input.detectedMultiCenterMolecule.Center =>
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 ∧
      relativeSign input.detectedMultiCenterMolecule cfg action d ≠ 1
  have nonempty : bad.Nonempty := by
    push_neg at allProper
    obtain ⟨d, member, negative⟩ := allProper
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, member, negative⟩⟩
  obtain ⟨d, badD, maximal⟩ := bad.exists_max_image (fun d => W.rank d.1) nonempty
  obtain ⟨member, notProper⟩ := (Finset.mem_filter.mp badD).2
  obtain ⟨p, terminal, matched, prefixLower, higher⟩ := W.matched d member
  have pending : W.rank d.1 ≤ bound := by
    by_contra later
    exact notProper (higherProper d member (Nat.lt_of_not_ge later))
  have samePath : p.1.map (action : Equiv.Perm input.Atom) =
      p.1.map (W.symmetry : Equiv.Perm input.Atom) :=
    pending_witness_image W.rank bound W.symmetry correction lowFixed p.1 p.2.nonempty
      d.1 terminal prefixLower pending
  have maximalProper : ∀ other : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse a other.1 →
      W.rank d.1 < W.rank other.1 →
      relativeSign input.detectedMultiCenterMolecule cfg action other = 1 := by
    intro other inSource later
    by_contra negative
    have upper := maximal other (Finset.mem_filter.mpr ⟨Finset.mem_univ other, inSource, negative⟩)
    omega
  have proper : ∀ other : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
        d.1 other.1 → other.1 ≠ d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg action other = 1 := by
    intro other residual different
    have weakened := component_weaken
      (show data.target.1.node.history.reverse ⊆
        data.target.1.node.history.reverse ++ p.1.dropLast from
        fun _ h => List.mem_append_left _ h) residual
    exact maximalProper other ⟨member.1, member.2.trans weakened.2⟩ (higher other.1 residual different)
  have negative : relativeSign input.detectedMultiCenterMolecule cfg action d = -1 :=
    (relativeSign_eq_one_or_neg_one _ cfg action d).resolve_left notProper
  refine ⟨d, p, member, terminal, negative, pending, prefixLower, higher, maximalProper, ?_⟩
  cases observed : ((originalState input mol node reference).factAt?
      (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel with
  | none =>
      obtain ⟨child, selected, descent, adequate⟩ := W.execution p.1 p.2
      exact candidate_absence_refusal input mol (structuralDepth mol node) (inputGeometry input)
        node child _ reference.val selected descent adequate observed
  | some label =>
      exfalso
      have fixed : ∀ atom ∈ data.target.1.node.history.reverse,
          (action : Equiv.Perm input.Atom) atom = atom := by
        intro atom present
        change (W.symmetry : Equiv.Perm input.Atom)
          ((correction : Equiv.Perm input.Atom) atom) = atom
        rw [boundaryFixed atom (List.mem_reverse.mp present),
          W.fixedHistory atom (List.mem_reverse.mp present)]
      have matchedAfter : ((originalState input mol node reference).factAt?
            (rawPathNode data.target.1.root (boundaryPath data.target p.1))).map factLabel =
        ((originalState input mol node reference).factAt?
            (rawPathNode data.target.1.root
              (boundaryPath data.target (p.1.map (action : Equiv.Perm input.Atom))))).map factLabel := by
        rw [samePath]
        exact matched
      have sym := structuralSymmetry_of_aut input mol agreement admissible supported action
      have cov := actual_covariant input mol agreement admissible supported single action
      have rawSingle := raw_single mol input agreement admissible.1.1 admissible.1.2 supported single
      have mapped := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1
        admissible.1.2 rawSingle cov
      obtain ⟨original, shifted⟩ := shifted_descriptor_of_snapshot_match input mol agreement admissible
        supported single action cfg calibrated LocalizedChemicalRingInheritedFallback.rawStep? mapped
        (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations input mol))
        (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations input mol))
        data.target reference a fixed p.1 p.2 d terminal (structuralDepth mol node) node reached
        matchedAfter label observed proper
      have inverse : ((action : Equiv.Perm input.Atom).symm reference) = reference :=
        inverse_reference_two_port W.symmetry correction reference reference
          W.fixedReference referenceFixed
      rw [negative, inverse, original] at shifted
      have impossible := flipDescriptorBy_some_eq (-1) (Or.inr rfl) label shifted.symm
      norm_num at impossible

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness.labels_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness.refineRank_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness.refineRank_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness.exists_correctionWitness
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionWitness.step
