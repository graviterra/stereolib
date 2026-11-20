import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMarked
import TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Physical symmetry meets the generated-state meaning: lowercase existence and separation soundness

`LocalizedChemicalRingCompletenessMarked.assignCenter_eq` expresses the actual output through the
independent marked orders on the actually generated facts for the original and the reflected
geometry. The accepted sense transport (`LocalizedChemicalRingSenseTransport.root_mirror_invariant`,
`root_evaluate`) relates those two sides at a centre with a calibrated transposition symmetry. The
combination removes the reflected-geometry premise of `assignCenter_of_separated` in the two
physically symmetric situations, for both recursions:

* `assignCenter_pseudo_of_mirror` / `distant_assignCenter_pseudo_of_mirror`: at a centre fixed by
  an involutive molecular automorphism exchanging two of its ligands with mirror sense at every
  framed descendant, separation of the eligible references by the facts generated under the
  ORIGINAL geometry alone yields the lowercase letter `pseudoRSOfRS (letterOfSign (sign * h))`.
  The accepted theorem excluded uppercase; this one produces the lowercase descriptor.
* `not_separated_of_proper` / `distant_not_separated_of_proper`: at a centre with a calibrated
  proper transposition symmetry the generated facts can never separate the eligible references
  (the exchanged reference reads the complementary letter). `Separated` is therefore a sound
  certificate of the absence of such a symmetry, and the accepted refusal there is forced by the
  generated state itself, not a shortfall of it.

Hypotheses are those of the accepted physical endpoints plus `RootData`. No desired label or
sorting success is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingActualCovariance
open LocalizedChemicalRingActualPhysicalSense (actual_covariant)
open LocalizedChemicalRingCompletenessStrict LocalizedChemicalRingCompletenessMarked
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (markedReading? underWith)
open LocalizedMarkedReachableConfigurations (reached_root)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single raw_atom_bound)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? readback? consensus appendFacts?
  mirror caseFromMirror? caseFromMirror?_eq_same structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (e : input.detectedMultiCenterMolecule.Aut)
  (involutive : ∀ a, (e : Equiv.Perm input.Atom) ((e : Equiv.Perm input.Atom) a) = a)
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)
  (c : input.detectedMultiCenterMolecule.Center)
  (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
  {i j : Fin 4} (ne : i ≠ j)
  (swapEq : input.detectedMultiCenterMolecule.ligandPermAt e c = Equiv.swap i j)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

/-- The evaluator's own reference evaluation at the root from child facts `under`. -/
noncomputable def evaluateWith (geom : Geometry) (under : Nat → OccurrenceAuxState) (r : Nat) :
    Option RS :=
  (appendFacts? [] (under r)).bind fun temp =>
    markedReading? mol (sparseOperations input mol) geom temp (canonicalCenterRoot c.1.val) r

/-- One eligible reading is the evaluator's own reference evaluation. -/
theorem readingOf_eq_evaluate (data : RootData input mol c) (geom : Geometry)
    (under : Nat → OccurrenceAuxState) (k : Fin 4) :
    readingOf input mol single c data geom under k =
      evaluateWith input mol c geom under (input.detectedMultiCenterMolecule.ligandAtomAt c k).val := by
  unfold readingOf evaluateWith
  congr 1
  funext temp
  exact (markedReading_root input mol single c data geom temp _
    (input.detectedMultiCenterMolecule.ligandAtomAt c k).isLt).symm

include fixed swapEq in
/-- The relabelling moves the reference ligand `k` to the ligand `swap i j k`. -/
theorem relabel_ligand (k : Fin 4) :
    relabelOf input (e : Equiv.Perm input.Atom)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val =
      (input.detectedMultiCenterMolecule.ligandAtomAt c (Equiv.swap i j k)).val := by
  rw [relabelOf_val, ← MultiCenterMolecule.ligandAtomAt_ligandPermAt, fixed, swapEq]

include agreement admissible supported single involutive atomsPres fixed swapEq in
/-- Eligible references are closed under the exchange. -/
theorem swap_mem_tiedLigands (data : RootData input mol c) (k : Fin 4)
    (mem : k ∈ tiedLigands input mol single c data) :
    Equiv.swap i j k ∈ tiedLigands input mol single c data := by
  have cov := actual_covariant input mol agreement admissible supported single e involutive atomsPres
  have rootFixed : mapNode (relabelOf input (e : Equiv.Perm input.Atom))
      (canonicalCenterRoot c.1.val) = canonicalCenterRoot c.1.val := by
    rw [mapNode_canonicalCenterRoot, relabelOf_val]
    exact congrArg (fun a : input.Atom => canonicalCenterRoot a.val)
      ((RootedTetrahedralBranchSymmetry.centerPerm_eq_iff _ e c).mp fixed)
  have rel := cov.ordinary (canonicalCenterRoot c.1.val)
    (reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)) data.atoms data.atoms
    data.rawFrame (by rw [rootFixed]; exact data.rawFrame)
  have ord : (sparseOperations input mol).ordinary [] (canonicalCenterRoot c.1.val) = _ :=
    ordinary_root input mol single c data
  rw [rootFixed, ord, ordinaryRel_some_some] at rel
  obtain ⟨_, _, _, eligiblePerm⟩ := rel
  rw [eligible_root input mol single c data] at eligiblePerm
  have memAtom : (input.detectedMultiCenterMolecule.ligandAtomAt c (Equiv.swap i j k)).val ∈
      (tiedLigands input mol single c data).map
        (fun l => (input.detectedMultiCenterMolecule.ligandAtomAt c l).val) := by
    rw [eligiblePerm.mem_iff, List.map_map]
    refine List.mem_map.mpr ⟨k, mem, ?_⟩
    simp only [Function.comp_apply]
    exact relabel_ligand input e c fixed swapEq k
  obtain ⟨m, hm, eq⟩ := List.mem_map.mp memAtom
  have same : m = Equiv.swap i j k :=
    input.detectedMultiCenterMolecule.ligandAtomAt_injective c (Fin.ext eq)
  rw [← same]
  exact hm

/-! ## Proper transposition: complementary readings, no separation -/

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- **Complementary readings under a proper transposition** (immediate-frame facts). -/
theorem evaluate_proper_complement
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (r : Nat) :
    evaluateWith input mol c (inputGeometry input) (generated input mol c (inputGeometry input))
        (relabelOf input (e : Equiv.Perm input.Atom) r) =
      (evaluateWith input mol c (inputGeometry input) (generated input mol c (inputGeometry input))
        r).map RS.swap := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have sym := symmetry_of_aut mol input agreement admissible supported e involutive atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e involutive atomsPres
  have centre := exchangedCentre mol input agreement admissible supported single e c fixed i j ne swapEq
  have agree := agreeOn_of_proper mol input agreement wellFormed unique supported single cfg e
    c.1.val (raw_atom_bound mol input agreement c.1) calibrated proper
  have h := root_evaluate LocalizedMarkedOperationEvaluator.rawStep? sym wellFormed unique
    (raw_single mol input agreement wellFormed unique supported single) cov
    (rawStep_map sym wellFormed unique
      (raw_single mol input agreement wellFormed unique supported single) cov)
    rawStep_congr_geom centre (inputGeometry input) (inputGeometry input) agree
    (structuralDepth mol (canonicalCenterRoot c.1.val)) r
  rw [← facts_eq_factsWith] at h
  exact h

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- Complementary readings under a proper transposition (distant-reference facts). -/
theorem distant_evaluate_proper_complement
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (r : Nat) :
    evaluateWith input mol c (inputGeometry input)
        (distantGenerated input mol c (inputGeometry input))
        (relabelOf input (e : Equiv.Perm input.Atom) r) =
      (evaluateWith input mol c (inputGeometry input)
        (distantGenerated input mol c (inputGeometry input)) r).map RS.swap := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have sym := symmetry_of_aut mol input agreement admissible supported e involutive atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e involutive atomsPres
  have centre := exchangedCentre mol input agreement admissible supported single e c fixed i j ne swapEq
  have agree := agreeOn_of_proper mol input agreement wellFormed unique supported single cfg e
    c.1.val (raw_atom_bound mol input agreement c.1) calibrated proper
  have h := root_evaluate LocalizedPhysicalMarkedDistantReference.rawStep? sym wellFormed unique
    (raw_single mol input agreement wellFormed unique supported single) cov
    (distantStep_map sym wellFormed unique
      (raw_single mol input agreement wellFormed unique supported single) cov)
    distantStep_congr_geom centre (inputGeometry input) (inputGeometry input) agree
    (structuralDepth mol (canonicalCenterRoot c.1.val)) r
  rw [← distant_facts_eq_factsWith] at h
  exact h

include agreement admissible supported single involutive atomsPres fixed swapEq calibrated in
/-- Separation is impossible when the exchanged reference reads the complementary letter. -/
theorem not_separated_of_complement (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (under : Nat → OccurrenceAuxState)
    (complement : ∀ r, evaluateWith input mol c (inputGeometry input) under
        (relabelOf input (e : Equiv.Perm input.Atom) r) =
      (evaluateWith input mol c (inputGeometry input) under r).map RS.swap)
    (h : ℝ) (sep : Separated input mol single c data under h) : False := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  obtain ⟨k, mk⟩ := List.exists_mem_of_ne_nil _ ne'
  have mτ := swap_mem_tiedLigands input mol agreement admissible supported single e involutive
    atomsPres c fixed swapEq data k mk
  have readK := readingOf_eq_of_separated input mol single cfg c (calibrated c) data under h sep k mk
  have readτ := readingOf_eq_of_separated input mol single cfg c (calibrated c) data under h sep _ mτ
  have comp := complement (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
  rw [relabel_ligand input e c fixed swapEq k, ← readingOf_eq_evaluate input mol single c data,
    ← readingOf_eq_evaluate input mol single c data, readK, readτ, Option.map_some,
    Option.some.injEq] at comp
  exact swap_ne _ comp.symm

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- **Separation is impossible under a calibrated proper transposition symmetry.** -/
theorem not_separated_of_proper (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (h : ℝ)
    (sep : Separated input mol single c data (generated input mol c (inputGeometry input)) h) :
    False :=
  not_separated_of_complement input mol agreement admissible supported single cfg e involutive
    atomsPres c fixed swapEq calibrated data notInj _
    (evaluate_proper_complement input mol agreement admissible supported single cfg e involutive
      atomsPres c fixed ne swapEq calibrated proper) h sep

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- The distant-reference recursion cannot separate under a proper transposition either. -/
theorem distant_not_separated_of_proper (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (h : ℝ)
    (sep : Separated input mol single c data
      (distantGenerated input mol c (inputGeometry input)) h) :
    False :=
  not_separated_of_complement input mol agreement admissible supported single cfg e involutive
    atomsPres c fixed swapEq calibrated data notInj _
    (distant_evaluate_proper_complement input mol agreement admissible supported single cfg e
      involutive atomsPres c fixed ne swapEq calibrated proper) h sep

/-! ## Mirror transposition: reading invariance, lowercase existence -/

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- **Reading invariance under a calibrated mirror transposition**, immediate-frame facts. -/
theorem raw_mirror_eq
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1) :
    LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol) (inputGeometry input)
        [] none (canonicalCenterRoot c.1.val) (generated input mol c (inputGeometry input)) =
      LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol)
        (mirror (inputGeometry input)) [] none (canonicalCenterRoot c.1.val)
        (generated input mol c (mirror (inputGeometry input))) := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have sym := symmetry_of_aut mol input agreement admissible supported e involutive atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e involutive atomsPres
  have centre := exchangedCentre mol input agreement admissible supported single e c fixed i j ne swapEq
  have agree := agreeOn_of_mirror mol input agreement wellFormed unique supported single cfg e
    c.1.val (raw_atom_bound mol input agreement c.1) calibrated mirrorSense
  have h := root_mirror_invariant LocalizedMarkedOperationEvaluator.rawStep? sym wellFormed unique
    (raw_single mol input agreement wellFormed unique supported single) cov
    (rawStep_map sym wellFormed unique
      (raw_single mol input agreement wellFormed unique supported single) cov)
    rawStep_congr_geom centre (inputGeometry input) agree (fun _ _ => rfl)
    (structuralDepth mol (canonicalCenterRoot c.1.val))
  rw [← facts_eq_factsWith] at h
  exact h

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- Reading invariance under a calibrated mirror transposition, distant-reference facts. -/
theorem distant_raw_mirror_eq
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1) :
    LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol) (inputGeometry input)
        [] none (canonicalCenterRoot c.1.val) (distantGenerated input mol c (inputGeometry input)) =
      LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol)
        (mirror (inputGeometry input)) [] none (canonicalCenterRoot c.1.val)
        (distantGenerated input mol c (mirror (inputGeometry input))) := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have sym := symmetry_of_aut mol input agreement admissible supported e involutive atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e involutive atomsPres
  have centre := exchangedCentre mol input agreement admissible supported single e c fixed i j ne swapEq
  have agree := agreeOn_of_mirror mol input agreement wellFormed unique supported single cfg e
    c.1.val (raw_atom_bound mol input agreement c.1) calibrated mirrorSense
  have h := root_mirror_invariant LocalizedPhysicalMarkedDistantReference.rawStep? sym wellFormed
    unique (raw_single mol input agreement wellFormed unique supported single) cov
    (distantStep_map sym wellFormed unique
      (raw_single mol input agreement wellFormed unique supported single) cov)
    distantStep_congr_geom centre (inputGeometry input) agree
    (fun g under => LocalizedPhysicalMarkedDistantReference.rawStep_none mol _ g [] _ under)
    (structuralDepth mol (canonicalCenterRoot c.1.val))
  rw [← distant_facts_eq_factsWith, LocalizedPhysicalMarkedDistantReference.rawStep_none,
    LocalizedPhysicalMarkedDistantReference.rawStep_none] at h
  exact h

include calibrated in
/-- Lowercase from reading invariance and separation of the original geometry. -/
theorem case_pseudo_of_raw_eq (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (under under' : Nat → OccurrenceAuxState)
    (rawEq : LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol)
        (inputGeometry input) [] none (canonicalCenterRoot c.1.val) under =
      LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol)
        (mirror (inputGeometry input)) [] none (canonicalCenterRoot c.1.val) under')
    (h : ℝ) (sep : Separated input mol single c data under h) :
    caseFromMirror?
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (inputGeometry input) under)))
        (consensus ((tiedLigands input mol single c data).map
          (readingOf input mol single c data (mirror (inputGeometry input)) under'))) =
      some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  have e1 := rawStep_root input mol single c data (inputGeometry input) under
  have e2 := rawStep_root input mol single c data (mirror (inputGeometry input)) under'
  rw [if_neg notInj] at e1 e2
  have cons : consensus ((tiedLigands input mol single c data).map
      (readingOf input mol single c data (mirror (inputGeometry input)) under')) =
      consensus ((tiedLigands input mol single c data).map
        (readingOf input mol single c data (inputGeometry input) under)) := by
    rw [← e1, ← e2]
    exact rawEq.symm
  rw [cons, consensus_map_const _ ne' _ _
      (fun k mk => readingOf_eq_of_separated input mol single cfg c (calibrated c) data under h sep k mk),
    caseFromMirror?_eq_same]

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- **Lowercase existence under a calibrated mirror transposition.** Separation by the facts
generated under the original geometry alone yields the pseudoasymmetric descriptor. -/
theorem assignCenter_pseudo_of_mirror (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (h : ℝ)
    (sep : Separated input mol single c data (generated input mol c (inputGeometry input)) h) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  rw [assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj]
  exact case_pseudo_of_raw_eq input mol single cfg c calibrated data notInj _ _
    (raw_mirror_eq input mol agreement admissible supported single cfg e involutive atomsPres c
      fixed ne swapEq calibrated mirrorSense) h sep

include agreement admissible supported single involutive atomsPres fixed ne swapEq calibrated in
/-- Lowercase existence under a calibrated mirror transposition, distant-reference recursion. -/
theorem distant_assignCenter_pseudo_of_mirror (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center,
        d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (h : ℝ)
    (sep : Separated input mol single c data
      (distantGenerated input mol c (inputGeometry input)) h) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  rw [distant_assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj]
  exact case_pseudo_of_raw_eq input mol single cfg c calibrated data notInj _ _
    (distant_raw_mirror_eq input mol agreement admissible supported single cfg e involutive
      atomsPres c fixed ne swapEq calibrated mirrorSense) h sep

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.readingOf_eq_evaluate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.relabel_ligand
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.swap_mem_tiedLigands
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.evaluate_proper_complement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.distant_evaluate_proper_complement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.not_separated_of_complement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.not_separated_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.distant_not_separated_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.raw_mirror_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.distant_raw_mirror_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.case_pseudo_of_raw_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.assignCenter_pseudo_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror.distant_assignCenter_pseudo_of_mirror
