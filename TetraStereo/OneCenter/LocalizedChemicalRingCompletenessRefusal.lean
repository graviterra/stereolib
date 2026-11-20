import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Actual refusal under any odd proper molecular symmetry

The symmetry can be a transposition or a four-cycle. Strict ordinary keys would fix every
ligand, so the root necessarily enters the marked path. A proper odd symmetry pairs each
eligible reading with its opposite, including refusal. Consequently consensus cannot produce
a letter. Neither successful readings nor `Separated` are assumptions. This proves a physical
refusal implication for both immediate and distant-reference recursion; its converse is open.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal
open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingCompletenessStrict
open LocalizedChemicalRingCompletenessMarked LocalizedChemicalRingCompletenessOrbit
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (reached_root)
open LocalizedMarkedCertifiedTerminalRefusal (raw_atom_bound)
open LocalizedGenericMarkedRecalculation (consensus mirror caseFromMirror? caseFromMirror?_none_left)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- A reference population closed under a reading-complementing map cannot reach consensus. -/
theorem consensus_none_of_swapped {α : Type*} (xs : List α) (nonempty : xs ≠ [])
    (τ : α → α) (read : α → Option RS)
    (closed : ∀ k ∈ xs, τ k ∈ xs)
    (swapped : ∀ k ∈ xs, read (τ k) = (read k).map RS.swap) :
    consensus (xs.map read) = none := by
  cases result : consensus (xs.map read) with
  | none => rfl
  | some v =>
      have all := ((consensus_eq_some_iff _ _).mp result).2
      obtain ⟨k, member⟩ := List.exists_mem_of_ne_nil xs nonempty
      have rk := all (read k) (List.mem_map.mpr ⟨k, member, rfl⟩)
      have rτ := all (read (τ k)) (List.mem_map.mpr ⟨τ k, closed k member, rfl⟩)
      have opposite := swapped k member
      rw [rk, rτ, Option.map_some, Option.some.injEq] at opposite
      exact False.elim (swap_ne v opposite.symm)

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

include agreement admissible supported single atomsPres fixed in
/-- Injective actual root keys force any centre-fixing molecular automorphism to fix each ligand. -/
theorem strict_keys_fix_ligands (data : RootData input mol c)
    (strictKeys : Function.Injective (rootKeys input single data.target data.real data.detected)) :
    input.detectedMultiCenterMolecule.ligandPermAt e c = 1 := by
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
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
  obtain ⟨_, _, atomsAtEq, _⟩ := rel
  have fixedList := atomsAtEq (strict_root input mol single c data strictKeys)
  rw [ranked_eq input mol single c data, Option.map_some, Option.some.injEq] at fixedList
  have fixes := map_eq_self_fixes _ _ fixedList.symm
  apply Equiv.ext
  intro i
  have surj := (priorityPerm input mol single c data).surjective i
  obtain ⟨p, hp⟩ := surj
  have member : (input.detectedMultiCenterMolecule.ligandAtomAt c i).val ∈
      [(input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 0)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 1)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 2)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 3)).val] := by
    rw [← hp]
    fin_cases p <;> simp
  have atomFixed := fixes _ member
  rw [relabelOf_val] at atomFixed
  have ligandFixed : (e : Equiv.Perm input.Atom) (input.detectedMultiCenterMolecule.ligandAtomAt c i) =
      input.detectedMultiCenterMolecule.ligandAtomAt c i := Fin.ext atomFixed
  have transported := input.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt e c i
  rw [fixed, ligandFixed] at transported
  exact input.detectedMultiCenterMolecule.ligandAtomAt_injective c transported


include agreement admissible supported single atomsPres fixed in
theorem not_injective_of_odd (data : RootData input mol c)
    (odd : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1) :
    ¬ Function.Injective (rootKeys input single data.target data.real data.detected) := by
  intro inj
  have trivial := strict_keys_fix_ligands input mol agreement admissible supported single e
    atomsPres c fixed data inj
  rw [trivial] at odd
  norm_num [permHandedness] at odd

variable
  (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
    ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
      ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
        relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
  (odd : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1)

include agreement admissible supported single atomsPres fixed calibrated proper odd in
/-- Proper odd molecular symmetry forces actual refusal, without a reference-separation premise. -/
theorem assignCenter_none_of_proper_odd :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val = none := by
  obtain ⟨data⟩ := rootData_exists input mol agreement admissible supported single c
  have notInj := not_injective_of_odd input mol agreement admissible supported single e
    atomsPres c fixed data odd
  rw [assignCenter_none_iff input mol single cfg c (calibrated c) data notInj]
  apply Or.inl
  apply consensus_none_of_swapped _ (tiedLigands_ne_nil input mol single c data notInj)
    (input.detectedMultiCenterMolecule.ligandPermAt e c)
  · exact perm_mem_tiedLigands input mol agreement admissible supported single e atomsPres c fixed data
  · intro k _
    rw [readingOf_proper input mol agreement admissible supported single cfg e atomsPres c fixed
      calibrated data proper k, if_neg (by rw [odd]; norm_num)]

include agreement admissible supported single atomsPres fixed calibrated proper odd in
/-- The distant-reference evaluator has the same physical refusal consequence. -/
theorem distant_assignCenter_none_of_proper_odd :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
      (inputGeometry input) c.1.val = none := by
  obtain ⟨data⟩ := rootData_exists input mol agreement admissible supported single c
  have notInj := not_injective_of_odd input mol agreement admissible supported single e
    atomsPres c fixed data odd
  rw [distant_assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj]
  have refused : consensus ((tiedLigands input mol single c data).map
      (readingOf input mol single c data (inputGeometry input)
        (distantGenerated input mol c (inputGeometry input)))) = none := by
    apply consensus_none_of_swapped _ (tiedLigands_ne_nil input mol single c data notInj)
      (input.detectedMultiCenterMolecule.ligandPermAt e c)
    · exact perm_mem_tiedLigands input mol agreement admissible supported single e atomsPres c fixed data
    · intro k _
      rw [distant_readingOf_proper input mol agreement admissible supported single cfg e atomsPres c
        fixed calibrated data proper k, if_neg (by rw [odd]; norm_num)]
  rw [refused, caseFromMirror?_none_left]

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal.consensus_none_of_swapped
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal.strict_keys_fix_ligands
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal.not_injective_of_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal.assignCenter_none_of_proper_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessRefusal.distant_assignCenter_none_of_proper_odd
