import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneratedFacts
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Actual refusal under a proper symmetry fixing an eligible reference

`LocalizedChemicalRingCompletenessRefusal` derives refusal from an ODD proper molecular symmetry
of the centre. Here the ligand permutation `τ = ligandPermAt e c` may be EVEN (a 3-cycle), provided
the symmetry fixes one eligible reference ligand `k` and moves some ligand. Then the actual
generated facts for reference `k` are invariant under the relabelling (`generated_fixed_perm`),
the actual marked ranked list for `k` equals its own relabelling (`rankedList_fixed`), and a strict
marked order would force `τ = 1` — so the actual marked keys for `k` tie
(`not_injective_fixed`), the reading of `k` is a refusal (`readingOf_fixed_none`), and the actual
output is `none` for both recursions (`assignCenter_none_of_proper_fixing_reference`,
`distant_assignCenter_none_of_proper_fixing_reference`).

The accepted `LocalizedChemicalRingDefaultMarkerLayout.actual_root_default_tie_reference_fixed_aut`
produces, from an actual tie, a graph automorphism fixing centre and reference; it does not supply
the proper-sense premise used here, so the two results are not yet converse halves of one physical
criterion. The theorems below apply exactly when a molecular automorphism with proper sense at all
framed descendants fixes the centre and an eligible reference and moves some ligand. A potential
application is an `A₄` cage, provided its reference-fixing three-cycles also preserve physical sense
at all framed descendants; the graph action alone does not imply that sense, and no such witness is
constructed here.
No separation, successful reading or desired output is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingCompletenessStrict
open LocalizedChemicalRingCompletenessMarked LocalizedChemicalRingCompletenessMirror
open LocalizedChemicalRingCompletenessOrbit LocalizedChemicalRingCompletenessRefusal
open LocalizedChemicalRingCompletenessGeneratedFacts
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (underWith)
open LocalizedMarkedReachableConfigurations (reached_root)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single raw_atom_bound)
open LocalizedGenericMarkedRecalculation (Geometry rankedAtoms? consensus appendFacts? structuralDepth)
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
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)
  (c : input.detectedMultiCenterMolecule.Center)
  (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
  (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
    ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
      ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
        relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
  (k : Fin 4) (fixedRef : input.detectedMultiCenterMolecule.ligandPermAt e c k = k)

/-! ## Generated facts and keys -/

include agreement admissible supported single in
/-- The actual generated facts have duplicate-free keys. -/
theorem generated_keys_nodup (geom : Geometry) (mark : Nat) :
    ((generated input mol c geom mark).map (·.key)).Nodup := by
  unfold generated
  rw [facts_eq_factsWith]
  exact underWith_keys_nodup _ mol (sparseOperations input mol) admissible.1.1
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 _ geom [] _ mark

include agreement admissible supported single in
theorem distant_generated_keys_nodup (geom : Geometry) (mark : Nat) :
    ((distantGenerated input mol c geom mark).map (·.key)).Nodup := by
  unfold distantGenerated
  rw [distant_facts_eq_factsWith]
  exact underWith_keys_nodup _ mol (sparseOperations input mol) admissible.1.1
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported single)
    admissible.1.2 _ geom [] _ mark

include agreement admissible supported single atomsPres fixed calibrated proper fixedRef in
/-- A proper symmetry fixing the reference leaves the generated facts invariant up to order. -/
theorem generated_fixed_perm :
    (generated input mol c (inputGeometry input)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).Perm
      ((generated input mol c (inputGeometry input)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map
          (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))) := by
  have agree := agreeOn_of_proper mol input agreement admissible.1.1 admissible.1.2 supported single
    cfg e c.1.val (raw_atom_bound mol input agreement c.1) calibrated proper
  have h := generated_perm input mol agreement admissible supported single e atomsPres c fixed
    (inputGeometry input) agree (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
  rw [relabel_ligand_perm input e c fixed k, fixedRef] at h
  exact h

include agreement admissible supported single atomsPres fixed calibrated proper fixedRef in
theorem distant_generated_fixed_perm :
    (distantGenerated input mol c (inputGeometry input)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).Perm
      ((distantGenerated input mol c (inputGeometry input)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map
          (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))) := by
  have agree := agreeOn_of_proper mol input agreement admissible.1.1 admissible.1.2 supported single
    cfg e c.1.val (raw_atom_bound mol input agreement c.1) calibrated proper
  have h := distant_generated_perm input mol agreement admissible supported single e atomsPres c
    fixed (inputGeometry input) agree (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
  rw [relabel_ligand_perm input e c fixed k, fixedRef] at h
  exact h

include agreement admissible supported single atomsPres fixed fixedRef in
/-- For an invariant state, the actual marked ranked list of the fixed reference equals its own
relabelling. -/
theorem rankedList_fixed (data : RootData input mol c) (state : OccurrenceAuxState)
    (perm : state.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (nodup : (state.map (·.key)).Nodup) :
    ((sparseOperations input mol).marked state (canonicalCenterRoot c.1.val)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).bind (rankedAtoms? data.atoms) =
      (((sparseOperations input mol).marked state (canonicalCenterRoot c.1.val)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).bind (rankedAtoms? data.atoms)).map
          (List.map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have h := cov.marked (canonicalCenterRoot c.1.val)
    (reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)) data.atoms data.atoms
    data.rawFrame (by rw [root_fixed input e c fixed]; exact data.rawFrame) state state perm nodup
    (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
  rw [root_fixed input e c fixed, relabel_ligand_perm input e c fixed k, fixedRef] at h
  exact h

include fixed in
/-- An enumeration equal to its own relabelling forces the ligand permutation to be trivial. -/
theorem perm_eq_one_of_enumeration_fixed (ρ : Equiv.Perm (Fin 4))
    (same : enumeration input c ρ =
      (enumeration input c ρ).map (relabelOf input (e : Equiv.Perm input.Atom))) :
    input.detectedMultiCenterMolecule.ligandPermAt e c = 1 := by
  have me := map_enumeration input e c ρ
  rw [fixed] at me
  have eq : enumeration input c ρ =
      enumeration input c (input.detectedMultiCenterMolecule.ligandPermAt e c * ρ) := same.trans me
  unfold enumeration at eq
  simp only [List.cons.injEq, and_true] at eq
  obtain ⟨e0, e1, e2, e3⟩ := eq
  have inj := input.detectedMultiCenterMolecule.ligandAtomAt_injective c
  have pointwise : ∀ p : Fin 4,
      input.detectedMultiCenterMolecule.ligandPermAt e c (ρ p) = ρ p := by
    intro p
    fin_cases p
    · exact (inj (Fin.ext e0)).symm
    · exact (inj (Fin.ext e1)).symm
    · exact (inj (Fin.ext e2)).symm
    · exact (inj (Fin.ext e3)).symm
  apply Equiv.ext
  intro i
  obtain ⟨p, hp⟩ := ρ.surjective i
  rw [← hp, Equiv.Perm.one_apply]
  exact pointwise p

include agreement admissible supported single atomsPres fixed fixedRef in
/-- **The actual marked keys of the fixed reference tie** whenever the symmetry moves a ligand. -/
theorem not_injective_fixed (data : RootData input mol c) (state : OccurrenceAuxState)
    (perm : state.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (nodup : (state.map (·.key)).Nodup)
    (moves : input.detectedMultiCenterMolecule.ligandPermAt e c ≠ 1) :
    ¬ Function.Injective (markedKeys input mol single c data state
      ⟨(input.detectedMultiCenterMolecule.ligandAtomAt c k).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).isLt⟩) := by
  intro inj
  have h := rankedList_fixed input mol agreement admissible supported single e atomsPres c fixed k
    fixedRef data state perm nodup
  rw [rankedList_root input mol single c data state _
    (input.detectedMultiCenterMolecule.ligandAtomAt c k).isLt, if_pos inj, Option.map_some,
    Option.some.injEq] at h
  exact moves (perm_eq_one_of_enumeration_fixed input e c fixed _ h)

/-! ## Readings and output -/

include agreement admissible supported single atomsPres fixed calibrated proper fixedRef in
theorem readingOf_fixed_none (data : RootData input mol c)
    (moves : input.detectedMultiCenterMolecule.ligandPermAt e c ≠ 1) :
    readingOf input mol single c data (inputGeometry input)
      (generated input mol c (inputGeometry input)) k = none := by
  rw [readingOf_eq_evaluate]
  unfold evaluateWith
  rw [generated_extension_succeeds input mol agreement admissible supported single c, Option.bind_some,
    markedReading_root input mol single c data, if_neg]
  exact not_injective_fixed input mol agreement admissible supported single e atomsPres c fixed k
    fixedRef data _
    (generated_fixed_perm input mol agreement admissible supported single cfg e atomsPres c fixed
      calibrated proper k fixedRef)
    (generated_keys_nodup input mol agreement admissible supported single c _ _) moves

include agreement admissible supported single atomsPres fixed calibrated proper fixedRef in
theorem distant_readingOf_fixed_none (data : RootData input mol c)
    (moves : input.detectedMultiCenterMolecule.ligandPermAt e c ≠ 1) :
    readingOf input mol single c data (inputGeometry input)
      (distantGenerated input mol c (inputGeometry input)) k = none := by
  rw [readingOf_eq_evaluate]
  unfold evaluateWith
  rw [distant_generated_extension_succeeds input mol agreement admissible supported single c,
    Option.bind_some, markedReading_root input mol single c data, if_neg]
  exact not_injective_fixed input mol agreement admissible supported single e atomsPres c fixed k
    fixedRef data _
    (distant_generated_fixed_perm input mol agreement admissible supported single cfg e atomsPres c
      fixed calibrated proper k fixedRef)
    (distant_generated_keys_nodup input mol agreement admissible supported single c _ _) moves

include agreement admissible supported single atomsPres fixed calibrated proper fixedRef in
/-- **Refusal under a proper symmetry fixing an eligible reference and moving a ligand**
(immediate-frame recursion). The symmetry may be even. -/
theorem assignCenter_none_of_proper_fixing_reference (data : RootData input mol c)
    (mem : k ∈ tiedLigands input mol single c data)
    (moves : input.detectedMultiCenterMolecule.ligandPermAt e c ≠ 1) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val = none := by
  have notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected) :=
    fun inj => moves (strict_keys_fix_ligands input mol agreement admissible supported single e
      atomsPres c fixed data inj)
  exact assignCenter_none_of_reading_none input mol single cfg c (calibrated c) data notInj k mem
    (readingOf_fixed_none input mol agreement admissible supported single cfg e atomsPres c fixed
      calibrated proper k fixedRef data moves)

include agreement admissible supported single atomsPres fixed calibrated proper fixedRef in
/-- The distant-reference recursion refuses as well. -/
theorem distant_assignCenter_none_of_proper_fixing_reference (data : RootData input mol c)
    (mem : k ∈ tiedLigands input mol single c data)
    (moves : input.detectedMultiCenterMolecule.ligandPermAt e c ≠ 1) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val = none := by
  have notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected) :=
    fun inj => moves (strict_keys_fix_ligands input mol agreement admissible supported single e
      atomsPres c fixed data inj)
  rw [distant_assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj]
  have refused : consensus ((tiedLigands input mol single c data).map
      (readingOf input mol single c data (inputGeometry input)
        (distantGenerated input mol c (inputGeometry input)))) = none :=
    consensus_map_none _ _ k mem
      (distant_readingOf_fixed_none input mol agreement admissible supported single cfg e atomsPres
        c fixed calibrated proper k fixedRef data moves)
  rw [refused]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.generated_keys_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.generated_fixed_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.rankedList_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.perm_eq_one_of_enumeration_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.not_injective_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.readingOf_fixed_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.distant_readingOf_fixed_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.assignCenter_none_of_proper_fixing_reference
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessFixedReference.distant_assignCenter_none_of_proper_fixing_reference
