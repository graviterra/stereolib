import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessMirror
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessGeneralPhysical
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Parity of a centre-fixing symmetry and the readings of the eligible references

The accepted physical endpoints and `LocalizedChemicalRingCompletenessMirror` concern a
transposition of two ligands. Here the ligand permutation `τ = ligandPermAt e c` of a
molecular automorphism `e` fixing the centre is arbitrary, including 3-cycles and 4-cycles,
and the uniform sense at the framed descendants is proper or mirror. The
accepted relabel covariance (`underWith_map`, `factsWith_congr`, `Covariant.marked`) transports
the actual generated facts and the actual marked stage, and `readback_relabel` reads the
relabelled priority list; at a fixed centre `relativeSign e c = permHandedness τ`
(`relativeSign_fixed`). Result (`readingOf_relabel`, `readingOf_proper`,
`readingOf_mirror_symmetry`): the reading of the eligible reference `τ k` is the reading of `k`
(proper, even `τ`), its complement (proper, odd `τ`), the complement of the reflected-geometry
reading of `k` (mirror, even `τ`) or that reflected reading itself (mirror, odd `τ`).

Consequences for the actual output, with separation of the eligible references by the facts
generated under the ORIGINAL geometry only:

* `not_separated_of_proper_odd`: separation is impossible under a proper odd symmetry;
* `readingOf_eq_of_proper_even`: readings agree within an orbit of a proper even symmetry;
* `assignCenter_chiral_of_mirror_even`: a mirror even symmetry (two enantiomorphic pairs
  exchanged) makes the actual evaluator return the UPPERCASE physical letter;
* `assignCenter_pseudo_of_mirror_odd`: a mirror odd symmetry yields the LOWERCASE letter.

These are implications for arbitrary centre-fixing symmetries. The mirror conclusions require
`Separated`; equal readings on one orbit do not imply successful readings or agreement across
orbits. No converse from refusal or lowercase output to a symmetry is proved.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingActualCovariance
open LocalizedChemicalRingCompletenessGeneralPhysical (actual_covariant structuralSymmetry_of_aut)
open LocalizedChemicalRingCompletenessStrict LocalizedChemicalRingCompletenessMarked
open LocalizedChemicalRingCompletenessMirror
open LocalizedMarkedRetainedPromotedRanking (refined_compare_lt_iff refined_compare_eq_iff)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (markedReading? underWith mem_tiedChildren_actual)
open LocalizedMarkedReachableConfigurations (reached_root)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single raw_atom_bound)
open LocalizedGenericMarkedRecalculation (Geometry readback? rankedAtoms? consensus appendFacts?
  mirror caseFromMirror? caseFromMirror?_eq_same caseFromMirror?_eq_swap structuralDepth
  flatMap_congr_mem)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign transportedSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open scoped Classical

theorem map_swap_swap (x : Option RS) : (x.map RS.swap).map RS.swap = x := by
  cases x with
  | none => rfl
  | some v => rw [Option.map_some, Option.map_some, swap_swap]

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

include fixed in
/-- At a fixed centre the relative sign is the handedness of the ligand permutation. -/
theorem relativeSign_fixed :
    relativeSign input.detectedMultiCenterMolecule cfg e c =
      permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) := by
  unfold relativeSign transportedSign
  rw [fixed]
  rcases configurationSign_unit input cfg c with hc | hc <;> rw [hc] <;> ring

include fixed in
theorem relabel_ligand_perm (k : Fin 4) :
    relabelOf input (e : Equiv.Perm input.Atom)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val =
      (input.detectedMultiCenterMolecule.ligandAtomAt c
        (input.detectedMultiCenterMolecule.ligandPermAt e c k)).val := by
  rw [relabelOf_val, ← MultiCenterMolecule.ligandAtomAt_ligandPermAt, fixed]

include fixed in
theorem root_fixed :
    mapNode (relabelOf input (e : Equiv.Perm input.Atom)) (canonicalCenterRoot c.1.val) =
      canonicalCenterRoot c.1.val := by
  rw [mapNode_canonicalCenterRoot, relabelOf_val]
  exact congrArg (fun a : input.Atom => canonicalCenterRoot a.val)
    ((RootedTetrahedralBranchSymmetry.centerPerm_eq_iff _ e c).mp fixed)

include agreement admissible supported single atomsPres fixed in
/-- Eligible references are closed under the ligand permutation of the symmetry. -/
theorem perm_mem_tiedLigands (data : RootData input mol c) (k : Fin 4)
    (mem : k ∈ tiedLigands input mol single c data) :
    input.detectedMultiCenterMolecule.ligandPermAt e c k ∈ tiedLigands input mol single c data := by
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have rel := cov.ordinary (canonicalCenterRoot c.1.val)
    (reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)) data.atoms data.atoms
    data.rawFrame (by rw [root_fixed input e c fixed]; exact data.rawFrame)
  have ord : (sparseOperations input mol).ordinary [] (canonicalCenterRoot c.1.val) = _ :=
    ordinary_root input mol single c data
  rw [root_fixed input e c fixed, ord, ordinaryRel_some_some] at rel
  obtain ⟨_, _, _, eligiblePerm⟩ := rel
  rw [eligible_root input mol single c data] at eligiblePerm
  have memAtom : (input.detectedMultiCenterMolecule.ligandAtomAt c
      (input.detectedMultiCenterMolecule.ligandPermAt e c k)).val ∈
      (tiedLigands input mol single c data).map
        (fun l => (input.detectedMultiCenterMolecule.ligandAtomAt c l).val) := by
    rw [eligiblePerm.mem_iff, List.map_map]
    refine List.mem_map.mpr ⟨k, mem, ?_⟩
    simp only [Function.comp_apply]
    exact relabel_ligand_perm input e c fixed k
  obtain ⟨m, hm, eq⟩ := List.mem_map.mp memAtom
  have same : m = input.detectedMultiCenterMolecule.ligandPermAt e c k :=
    input.detectedMultiCenterMolecule.ligandAtomAt_injective c (Fin.ext eq)
  rw [← same]
  exact hm

/-! ## The actual marked stage under the relabelling -/

theorem rankedList_root (data : RootData input mol c) (temp : OccurrenceAuxState) (mark : Nat)
    (bound : mark < input.certified.input.molecule.atomCount) :
    ((sparseOperations input mol).marked temp (canonicalCenterRoot c.1.val) mark).bind
        (rankedAtoms? data.atoms) =
      if Function.Injective (markedKeys input mol single c data temp ⟨mark, bound⟩) then
        some (enumeration input c
          (rankPerm input mol c data (markedKeys input mol single c data temp ⟨mark, bound⟩)))
      else none := by
  obtain ⟨count, h⟩ := marked_root input mol single c data temp mark bound
  rw [h, Option.bind_some, rankedAtoms?_mk]
  by_cases inj : Function.Injective (markedKeys input mol single c data temp ⟨mark, bound⟩)
  · rw [if_pos ((strict_iff_injective compare refined_compare_lt_iff refined_compare_eq_iff _).mpr
      inj), ranked_eq_rank input mol c data, if_pos inj]
  · rw [if_neg (fun h => inj ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mp h)), if_neg inj]

theorem markedReading_eq_bind (data : RootData input mol c) (geom : Geometry)
    (temp : OccurrenceAuxState) (mark : Nat) :
    markedReading? mol (sparseOperations input mol) geom temp (canonicalCenterRoot c.1.val) mark =
      (((sparseOperations input mol).marked temp (canonicalCenterRoot c.1.val) mark).bind
        (rankedAtoms? data.atoms)).bind (readback? geom) := by
  unfold markedReading?
  rw [data.rawFrame]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_assoc]

include fixed calibrated in
theorem readback_enum_relabel (π : Equiv.Perm (Fin 4)) :
    readback? (inputGeometry input)
        ((enumeration input c π).map (relabelOf input (e : Equiv.Perm input.Atom))) =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        readback? (inputGeometry input) (enumeration input c π)
      else (readback? (inputGeometry input) (enumeration input c π)).map RS.swap := by
  have calibrated' : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg
      (input.detectedMultiCenterMolecule.centerPerm e c) := by
    rw [fixed]
    exact calibrated c
  exact readback_relabel input cfg e c (calibrated c) calibrated' π

include agreement admissible supported single atomsPres fixed calibrated in
/-- The actual marked reading at the root under the relabelled state and reference. -/
theorem markedReading_relabel (data : RootData input mol c) (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (nodup : (state.map (·.key)).Nodup) (k : Fin 4) :
    markedReading? mol (sparseOperations input mol) (inputGeometry input) state'
        (canonicalCenterRoot c.1.val)
        (relabelOf input (e : Equiv.Perm input.Atom)
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val) =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        markedReading? mol (sparseOperations input mol) (inputGeometry input) state
          (canonicalCenterRoot c.1.val) (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
      else (markedReading? mol (sparseOperations input mol) (inputGeometry input) state
          (canonicalCenterRoot c.1.val)
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map RS.swap := by
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have h := cov.marked (canonicalCenterRoot c.1.val)
    (reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)) data.atoms data.atoms
    data.rawFrame (by rw [root_fixed input e c fixed]; exact data.rawFrame) state state' perm nodup
    (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
  rw [root_fixed input e c fixed] at h
  rw [markedReading_eq_bind input mol c data, markedReading_eq_bind input mol c data, h,
    rankedList_root input mol single c data state _
      (input.detectedMultiCenterMolecule.ligandAtomAt c k).isLt]
  by_cases inj : Function.Injective (markedKeys input mol single c data state
      ⟨(input.detectedMultiCenterMolecule.ligandAtomAt c k).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).isLt⟩)
  · rw [if_pos inj, Option.map_some, Option.bind_some, Option.bind_some,
      readback_enum_relabel input cfg e c fixed calibrated]
  · rw [if_neg inj, Option.map_none, Option.bind_none]
    split_ifs <;> rfl

/-! ## The generated facts under the relabelling -/

include agreement admissible supported single atomsPres fixed in
/-- The facts generated under the relabelled reference are the relabelled facts generated under
any geometry agreeing with the pulled-back geometry below the centre. -/
theorem generated_perm (g' : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot c.1.val)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) g')
    (r : Nat) :
    (generated input mol c (inputGeometry input) (relabelOf input (e : Equiv.Perm input.Atom) r)).Perm
      ((generated input mol c g' r).map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))) := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have transport := underWith_map LocalizedMarkedOperationEvaluator.rawStep? sym wellFormed unique
    rawSingle cov (rawStep_map sym wellFormed unique rawSingle cov)
    (structuralDepth mol (canonicalCenterRoot c.1.val)) (inputGeometry input)
    (canonicalCenterRoot c.1.val) (reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)) r
  rw [root_fixed input e c fixed, ← facts_eq_factsWith] at transport
  refine transport.trans (List.Perm.of_eq ?_)
  congr 1
  unfold generated underWith
  apply flatMap_congr_mem
  intro child member
  rw [facts_eq_factsWith]
  exact factsWith_congr LocalizedMarkedOperationEvaluator.rawStep? (Below mol (canonicalCenterRoot c.1.val))
    (below_child (canonicalCenterRoot c.1.val)) rawStep_congr_geom _ _ _ agree [] (some r) child
    (below_of_child (canonicalCenterRoot c.1.val) child
      (mem_tiedChildren_actual mol _ [] _ child member))

include agreement admissible supported single atomsPres fixed calibrated in
/-- **The reference evaluation under the relabelled reference** (actual generated facts). -/
theorem evaluate_relabel (data : RootData input mol c) (g' : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot c.1.val)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) g')
    (k : Fin 4) :
    evaluateWith input mol c (inputGeometry input) (generated input mol c (inputGeometry input))
        (relabelOf input (e : Equiv.Perm input.Atom)
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val) =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        evaluateWith input mol c (inputGeometry input) (generated input mol c g')
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
      else (evaluateWith input mol c (inputGeometry input) (generated input mol c g')
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map RS.swap := by
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have perm := generated_perm input mol agreement admissible supported single e atomsPres
    c fixed g' agree (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
  unfold evaluateWith
  rw [appendFacts_nil_eq, appendFacts_nil_eq]
  by_cases nodup : ((generated input mol c g'
      (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map (·.key)).Nodup
  · rw [if_pos ((keys_nodup_iff sym perm).mpr nodup), if_pos nodup, Option.bind_some,
      Option.bind_some]
    exact markedReading_relabel input mol agreement admissible supported single cfg e
      atomsPres c fixed calibrated data _ _ perm nodup k
  · rw [if_neg (fun h => nodup ((keys_nodup_iff sym perm).mp h)), if_neg nodup, Option.bind_none]
    split_ifs <;> rfl

include agreement admissible supported single atomsPres fixed calibrated in
/-- The reading of the permuted eligible reference. -/
theorem readingOf_relabel (data : RootData input mol c) (g' : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot c.1.val)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) g')
    (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input) (generated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        readingOf input mol single c data (inputGeometry input) (generated input mol c g') k
      else (readingOf input mol single c data (inputGeometry input) (generated input mol c g') k).map
        RS.swap := by
  rw [readingOf_eq_evaluate, readingOf_eq_evaluate, ← relabel_ligand_perm input e c fixed]
  exact evaluate_relabel input mol agreement admissible supported single cfg e atomsPres
    c fixed calibrated data g' agree k

/-! ## Proper sense -/

include agreement admissible supported single atomsPres fixed calibrated in
/-- **Proper symmetry**: the reading of `τ k` is the reading of `k` or its complement according
to the parity of `τ`. -/
theorem readingOf_proper (data : RootData input mol c)
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input) (generated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      if permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1 then
        readingOf input mol single c data (inputGeometry input)
          (generated input mol c (inputGeometry input)) k
      else (readingOf input mol single c data (inputGeometry input)
          (generated input mol c (inputGeometry input)) k).map RS.swap := by
  have agree := agreeOn_of_proper mol input agreement admissible.1.1 admissible.1.2 supported single
    cfg e c.1.val (raw_atom_bound mol input agreement c.1) calibrated proper
  rw [← relativeSign_fixed input cfg e c fixed]
  exact readingOf_relabel input mol agreement admissible supported single cfg e atomsPres
    c fixed calibrated data (inputGeometry input) agree k

include agreement admissible supported single atomsPres fixed calibrated in
/-- A proper EVEN symmetry never obstructs the consensus: equal readings along its orbits. -/
theorem readingOf_eq_of_proper_even (data : RootData input mol c)
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (even : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1) (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input) (generated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      readingOf input mol single c data (inputGeometry input)
        (generated input mol c (inputGeometry input)) k := by
  rw [readingOf_proper input mol agreement admissible supported single cfg e atomsPres c
    fixed calibrated data proper k, if_pos even]

include agreement admissible supported single atomsPres fixed calibrated in
/-- **Separation is impossible under a proper ODD symmetry.** -/
theorem not_separated_of_proper_odd (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (odd : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1) (h : ℝ)
    (sep : Separated input mol single c data (generated input mol c (inputGeometry input)) h) :
    False := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  obtain ⟨k, mk⟩ := List.exists_mem_of_ne_nil _ ne'
  have mτ := perm_mem_tiedLigands input mol agreement admissible supported single e
    atomsPres c fixed data k mk
  have readK := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep k mk
  have readτ := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep _ mτ
  have rel := readingOf_proper input mol agreement admissible supported single cfg e
    atomsPres c fixed calibrated data proper k
  rw [if_neg (by rw [odd]; norm_num), readK, readτ, Option.map_some, Option.some.injEq] at rel
  exact swap_ne _ rel.symm

/-! ## Mirror sense -/

include agreement admissible supported single atomsPres fixed calibrated in
/-- **Mirror symmetry**: the reading of `τ k` is the complement of the reflected-geometry reading
of `k` (even `τ`) or that reflected reading itself (odd `τ`). -/
theorem readingOf_mirror_symmetry (data : RootData input mol c)
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input) (generated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      if permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1 then
        (readingOf input mol single c data (mirror (inputGeometry input))
          (generated input mol c (mirror (inputGeometry input))) k).map RS.swap
      else readingOf input mol single c data (mirror (inputGeometry input))
        (generated input mol c (mirror (inputGeometry input))) k := by
  have agree := agreeOn_of_mirror mol input agreement admissible.1.1 admissible.1.2 supported single
    cfg e c.1.val (raw_atom_bound mol input agreement c.1) calibrated mirrorSense
  have h := readingOf_relabel input mol agreement admissible supported single cfg e
    atomsPres c fixed calibrated data (mirror (inputGeometry input)) agree k
  rw [relativeSign_fixed input cfg e c fixed] at h
  rw [h, readingOf_mirror input mol single c data]
  split_ifs
  · rw [map_swap_swap]
  · rfl

include agreement admissible supported single atomsPres fixed calibrated in
/-- **Uppercase under a mirror EVEN symmetry** (two enantiomorphic ligand pairs exchanged):
separation of the eligible references by the facts generated under the original geometry yields
the uppercase physical letter in the marked order. -/
theorem assignCenter_chiral_of_mirror_even (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (even : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1) (h : ℝ)
    (sep : Separated input mol single c data (generated input mol c (inputGeometry input)) h) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      some (.chiral (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h))) := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  have mirrorRead : ∀ k ∈ tiedLigands input mol single c data,
      readingOf input mol single c data (mirror (inputGeometry input))
        (generated input mol c (mirror (inputGeometry input))) k =
      some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)).swap := by
    intro k mk
    have mτ := perm_mem_tiedLigands input mol agreement admissible supported single e
      atomsPres c fixed data k mk
    have readτ := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep _ mτ
    have rel := readingOf_mirror_symmetry input mol agreement admissible supported single cfg e
      atomsPres c fixed calibrated data mirrorSense k
    rw [if_pos even, readτ] at rel
    have := congrArg (Option.map RS.swap) rel
    rw [map_swap_swap, Option.map_some] at this
    exact this.symm
  rw [assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj,
    consensus_map_const _ ne' _ _
      (fun k mk => readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep k mk),
    consensus_map_const _ ne' _ _ mirrorRead, caseFromMirror?_eq_swap]

include agreement admissible supported single atomsPres fixed calibrated in
/-- **Lowercase under a mirror ODD symmetry**, in parity form. -/
theorem assignCenter_pseudo_of_mirror_odd (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (odd : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1) (h : ℝ)
    (sep : Separated input mol single c data (generated input mol c (inputGeometry input)) h) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  have mirrorRead : ∀ k ∈ tiedLigands input mol single c data,
      readingOf input mol single c data (mirror (inputGeometry input))
        (generated input mol c (mirror (inputGeometry input))) k =
      some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)) := by
    intro k mk
    have mτ := perm_mem_tiedLigands input mol agreement admissible supported single e
      atomsPres c fixed data k mk
    have readτ := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep _ mτ
    have rel := readingOf_mirror_symmetry input mol agreement admissible supported single cfg e
      atomsPres c fixed calibrated data mirrorSense k
    rw [if_neg (by rw [odd]; norm_num), readτ] at rel
    exact rel.symm
  rw [assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj,
    consensus_map_const _ ne' _ _
      (fun k mk => readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep k mk),
    consensus_map_const _ ne' _ _ mirrorRead, caseFromMirror?_eq_same]

/-! ## Distant-reference recursion -/

include agreement admissible supported single atomsPres fixed calibrated in
/-- The reference evaluation under the relabelled reference, for any child facts related by the
relabelling. -/
theorem evaluate_relabel_of_perm (data : RootData input mol c)
    (under under' : Nat → OccurrenceAuxState) (k : Fin 4)
    (perm : (under (relabelOf input (e : Equiv.Perm input.Atom)
        (input.detectedMultiCenterMolecule.ligandAtomAt c k).val)).Perm
      ((under' (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map
        (mapFact (relabelOf input (e : Equiv.Perm input.Atom))))) :
    evaluateWith input mol c (inputGeometry input) under
        (relabelOf input (e : Equiv.Perm input.Atom)
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val) =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        evaluateWith input mol c (inputGeometry input) under'
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val
      else (evaluateWith input mol c (inputGeometry input) under'
          (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map RS.swap := by
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  unfold evaluateWith
  rw [appendFacts_nil_eq, appendFacts_nil_eq]
  by_cases nodup : ((under' (input.detectedMultiCenterMolecule.ligandAtomAt c k).val).map
      (·.key)).Nodup
  · rw [if_pos ((keys_nodup_iff sym perm).mpr nodup), if_pos nodup, Option.bind_some,
      Option.bind_some]
    exact markedReading_relabel input mol agreement admissible supported single cfg e
      atomsPres c fixed calibrated data _ _ perm nodup k
  · rw [if_neg (fun h => nodup ((keys_nodup_iff sym perm).mp h)), if_neg nodup, Option.bind_none]
    split_ifs <;> rfl

include agreement admissible supported single atomsPres fixed in
/-- Distant-reference facts under the relabelled reference. -/
theorem distant_generated_perm (g' : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot c.1.val)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) g')
    (r : Nat) :
    (distantGenerated input mol c (inputGeometry input)
        (relabelOf input (e : Equiv.Perm input.Atom) r)).Perm
      ((distantGenerated input mol c g' r).map
        (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))) := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have sym := structuralSymmetry_of_aut input mol agreement admissible supported e atomsPres
  have cov := actual_covariant input mol agreement admissible supported single e atomsPres
  have transport := underWith_map LocalizedPhysicalMarkedDistantReference.rawStep? sym wellFormed
    unique rawSingle cov (distantStep_map sym wellFormed unique rawSingle cov)
    (structuralDepth mol (canonicalCenterRoot c.1.val)) (inputGeometry input)
    (canonicalCenterRoot c.1.val) (reached_root mol c.1.val (raw_atom_bound mol input agreement c.1)) r
  rw [root_fixed input e c fixed, ← distant_facts_eq_factsWith] at transport
  refine transport.trans (List.Perm.of_eq ?_)
  congr 1
  unfold distantGenerated underWith
  apply flatMap_congr_mem
  intro child member
  rw [distant_facts_eq_factsWith]
  exact factsWith_congr LocalizedPhysicalMarkedDistantReference.rawStep?
    (Below mol (canonicalCenterRoot c.1.val)) (below_child (canonicalCenterRoot c.1.val))
    distantStep_congr_geom _ _ _ agree [] (some r) child
    (below_of_child (canonicalCenterRoot c.1.val) child
      (mem_tiedChildren_actual mol _ [] _ child member))

include agreement admissible supported single atomsPres fixed calibrated in
theorem distant_readingOf_relabel (data : RootData input mol c) (g' : Geometry)
    (agree : AgreeOn (Below mol (canonicalCenterRoot c.1.val)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) g')
    (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input)
        (distantGenerated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        readingOf input mol single c data (inputGeometry input) (distantGenerated input mol c g') k
      else (readingOf input mol single c data (inputGeometry input)
        (distantGenerated input mol c g') k).map RS.swap := by
  rw [readingOf_eq_evaluate, readingOf_eq_evaluate, ← relabel_ligand_perm input e c fixed]
  exact evaluate_relabel_of_perm input mol agreement admissible supported single cfg e
    atomsPres c fixed calibrated data _ _ k
    (distant_generated_perm input mol agreement admissible supported single e atomsPres
      c fixed g' agree _)

include agreement admissible supported single atomsPres fixed calibrated in
theorem distant_readingOf_proper (data : RootData input mol c)
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input)
        (distantGenerated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      if permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1 then
        readingOf input mol single c data (inputGeometry input)
          (distantGenerated input mol c (inputGeometry input)) k
      else (readingOf input mol single c data (inputGeometry input)
          (distantGenerated input mol c (inputGeometry input)) k).map RS.swap := by
  have agree := agreeOn_of_proper mol input agreement admissible.1.1 admissible.1.2 supported single
    cfg e c.1.val (raw_atom_bound mol input agreement c.1) calibrated proper
  rw [← relativeSign_fixed input cfg e c fixed]
  exact distant_readingOf_relabel input mol agreement admissible supported single cfg e
    atomsPres c fixed calibrated data (inputGeometry input) agree k

include agreement admissible supported single atomsPres fixed calibrated in
theorem distant_not_separated_of_proper_odd (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = 1)
    (odd : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1) (h : ℝ)
    (sep : Separated input mol single c data
      (distantGenerated input mol c (inputGeometry input)) h) :
    False := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  obtain ⟨k, mk⟩ := List.exists_mem_of_ne_nil _ ne'
  have mτ := perm_mem_tiedLigands input mol agreement admissible supported single e
    atomsPres c fixed data k mk
  have readK := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep k mk
  have readτ := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep _ mτ
  have rel := distant_readingOf_proper input mol agreement admissible supported single cfg e
    atomsPres c fixed calibrated data proper k
  rw [if_neg (by rw [odd]; norm_num), readK, readτ, Option.map_some, Option.some.injEq] at rel
  exact swap_ne _ rel.symm

include agreement admissible supported single atomsPres fixed calibrated in
theorem distant_readingOf_mirror_symmetry (data : RootData input mol c)
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (k : Fin 4) :
    readingOf input mol single c data (inputGeometry input)
        (distantGenerated input mol c (inputGeometry input))
        (input.detectedMultiCenterMolecule.ligandPermAt e c k) =
      if permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1 then
        (readingOf input mol single c data (mirror (inputGeometry input))
          (distantGenerated input mol c (mirror (inputGeometry input))) k).map RS.swap
      else readingOf input mol single c data (mirror (inputGeometry input))
        (distantGenerated input mol c (mirror (inputGeometry input))) k := by
  have agree := agreeOn_of_mirror mol input agreement admissible.1.1 admissible.1.2 supported single
    cfg e c.1.val (raw_atom_bound mol input agreement c.1) calibrated mirrorSense
  have h := distant_readingOf_relabel input mol agreement admissible supported single cfg e
    atomsPres c fixed calibrated data (mirror (inputGeometry input)) agree k
  rw [relativeSign_fixed input cfg e c fixed] at h
  rw [h, readingOf_mirror input mol single c data]
  split_ifs
  · rw [map_swap_swap]
  · rfl

include agreement admissible supported single atomsPres fixed calibrated in
theorem distant_assignCenter_chiral_of_mirror_even (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (even : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1) (h : ℝ)
    (sep : Separated input mol single c data
      (distantGenerated input mol c (inputGeometry input)) h) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      some (.chiral (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h))) := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  have mirrorRead : ∀ k ∈ tiedLigands input mol single c data,
      readingOf input mol single c data (mirror (inputGeometry input))
        (distantGenerated input mol c (mirror (inputGeometry input))) k =
      some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)).swap := by
    intro k mk
    have mτ := perm_mem_tiedLigands input mol agreement admissible supported single e
      atomsPres c fixed data k mk
    have readτ := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep _ mτ
    have rel := distant_readingOf_mirror_symmetry input mol agreement admissible supported single
      cfg e atomsPres c fixed calibrated data mirrorSense k
    rw [if_pos even, readτ] at rel
    have := congrArg (Option.map RS.swap) rel
    rw [map_swap_swap, Option.map_some] at this
    exact this.symm
  rw [distant_assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj,
    consensus_map_const _ ne' _ _
      (fun k mk => readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep k mk),
    consensus_map_const _ ne' _ _ mirrorRead, caseFromMirror?_eq_swap]

include agreement admissible supported single atomsPres fixed calibrated in
theorem distant_assignCenter_pseudo_of_mirror_odd (data : RootData input mol c)
    (notInj : ¬ Function.Injective (rootKeys input single data.target data.real data.detected))
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, LocalizedGenericMarkedRecalculation.frameAtoms? mol node = some atoms →
        ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom →
          relativeSign input.detectedMultiCenterMolecule cfg e d = -1)
    (odd : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = -1) (h : ℝ)
    (sep : Separated input mol single c data
      (distantGenerated input mol c (inputGeometry input)) h) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
        (inputGeometry input) c.1.val =
      some (.pseudoasymmetric (pseudoRSOfRS
        (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)))) := by
  have ne' := tiedLigands_ne_nil input mol single c data notInj
  have mirrorRead : ∀ k ∈ tiedLigands input mol single c data,
      readingOf input mol single c data (mirror (inputGeometry input))
        (distantGenerated input mol c (mirror (inputGeometry input))) k =
      some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * h)) := by
    intro k mk
    have mτ := perm_mem_tiedLigands input mol agreement admissible supported single e
      atomsPres c fixed data k mk
    have readτ := readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep _ mτ
    have rel := distant_readingOf_mirror_symmetry input mol agreement admissible supported single
      cfg e atomsPres c fixed calibrated data mirrorSense k
    rw [if_neg (by rw [odd]; norm_num), readτ] at rel
    exact rel.symm
  rw [distant_assignCenter_eq input mol single cfg c (calibrated c) data, if_neg notInj,
    consensus_map_const _ ne' _ _
      (fun k mk => readingOf_eq_of_separated input mol single cfg c (calibrated c) data _ h sep k mk),
    consensus_map_const _ ne' _ _ mirrorRead, caseFromMirror?_eq_same]

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.evaluate_relabel_of_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.distant_generated_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.distant_readingOf_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.distant_readingOf_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.distant_not_separated_of_proper_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.distant_readingOf_mirror_symmetry
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.distant_assignCenter_chiral_of_mirror_even
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.distant_assignCenter_pseudo_of_mirror_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.relativeSign_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.perm_mem_tiedLigands
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.rankedList_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.markedReading_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.generated_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.evaluate_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.readingOf_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.readingOf_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.readingOf_eq_of_proper_even
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.not_separated_of_proper_odd
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.readingOf_mirror_symmetry
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.assignCenter_chiral_of_mirror_even
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit.assignCenter_pseudo_of_mirror_odd
