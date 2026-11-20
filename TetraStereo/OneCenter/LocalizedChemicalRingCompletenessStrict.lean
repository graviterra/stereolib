import TetraStereo.OneCenter.LocalizedChemicalRingActualPhysicalSense
import TetraStereo.OneCenter.LocalizedChemicalRingFrameSetup
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Completeness at constitutionally strict centres of the actual ring evaluator

The symmetry theorems of `LocalizedChemicalRingActualPhysicalSense` only say what the actual
evaluator cannot emit. This module gives the first positive direction on the ring domain: at a
detected centre whose four arms have pairwise distinct independent empty-state retained
Rules-1–5 keys (`rootKeys`, the declarative constitutional CIP keys evaluated on the actual
compiled arm graphs, ring duplicates included), the actual sparse evaluator emits an uppercase
letter, and that letter is the physical configuration sign of the centre read in the strictly
decreasing independent key order (`assignCenter_chiral_of_strict`, and the distant-reference
twin). The frame-slot-to-ligand bijection and the priority permutation are derived, not supplied.

The companion `ligandPermAt_eq_one_of_strict` shows such a centre admits no involutive molecular
symmetry moving any of its ligands: the covariance contract forces a strict order to be fixed
pointwise. Hence the strict case is coherent with the accepted transposition-refusal theorem.

Explicit hypotheses: intake agreement, admission, localized single bonds, simple-bonded graph,
calibrated coordinates at the centre, and strictness of the independent keys at the looked-up
root occurrence. No desired label, sorting success, acyclicity or rigidity is assumed. Tied
centres (Rules 4–6 with generated auxiliary descriptors) are not covered here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingRelabel LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingSenseTransport LocalizedChemicalRingFrameReadback
open LocalizedChemicalRingActualCovariance
open LocalizedChemicalRingActualPhysicalSense (actual_covariant)
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedOperations LocalizedMarkedRetainedStateReader
open LocalizedMarkedCarrierLookup LocalizedMarkedReachableConfigurations
open LocalizedMarkedReachedFrameNeighbors LocalizedMarkedCertifiedTerminalRefusal
open LocalizedMarkedDetectedOrdinaryExecution LocalizedMarkedDetectedFrames
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (Operations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? frameAtomsOf readback? atomsAt?
  consistent strict caseFromMirror? mirror readback_mirror)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open RawLocalizedChildNodeTransport

abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## List helpers -/

theorem mapM_eq_some_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.mapM_cons, h x List.mem_cons_self,
        mapM_eq_some_map f g xs (fun y hy => h y (List.mem_cons_of_mem x hy))]
      rfl

theorem list_four_eq {α : Type} (l : List α) (four : l.length = 4) :
    l = [l[0]'(by omega), l[1]'(by omega), l[2]'(by omega), l[3]'(by omega)] := by
  match l, four with
  | [_, _, _, _], _ => rfl

theorem all_gt_of_strict (adjacent : List (Option Ordering)) (h : strict adjacent = true) :
    ∀ decision ∈ adjacent, decision = some Ordering.gt := by
  intro decision member
  have := List.all_eq_true.mp h decision member
  simpa using this

theorem strict_of_all_gt (adjacent : List (Option Ordering))
    (h : ∀ decision ∈ adjacent, decision = some Ordering.gt) : strict adjacent = true := by
  rw [strict, List.all_eq_true]
  intro decision member
  rw [h decision member]
  rfl

theorem consistent_of_gt_or_eq (adjacent : List (Option Ordering))
    (h : ∀ decision ∈ adjacent, decision = some Ordering.gt ∨ decision = some Ordering.eq) :
    consistent adjacent = true := by
  rw [consistent, List.all_eq_true]
  intro decision member
  rcases h decision member with rfl | rfl <;> rfl

theorem map_eq_self_fixes {α : Type} (f : α → α) :
    ∀ l : List α, l.map f = l → ∀ x ∈ l, f x = x
  | [], _, _, h => by simp at h
  | x :: xs, h, y, hy => by
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp hy with rfl | later
      · exact h.1
      · exact map_eq_self_fixes f xs h.2 y later

/-! ## The strict root frame -/

section Strict

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center)

/-- The independent empty-state retained keys of the four arms of a looked-up root occurrence. -/
noncomputable def rootKeys (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom) :
    Fin 4 → CompleteLigandRule5Key :=
  rawStateKeys input single [] target real ⟨input.molecularFrameUnit target.1, detected⟩ rfl

/-- Everything the strict-root argument needs about the actual root occurrence. -/
structure RootData where
  target : input.LocalizedCIPOccurrence (retainedCarrierFuel input)
  found : lookup? input (canonicalCenterRoot c.1.val) = some target
  real : target.1.node.provenance = .realAtom
  detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom
  atoms : List Nat
  rawFrame : frameAtoms? mol (canonicalCenterRoot c.1.val) = some atoms
  nodup : atoms.Nodup
  frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input)
  frameExec : input.localizedNoDoubleFourLigandFrameExec? target = some frame
  read : Readback input atoms frame
  /-- Frame slot to ligand index of the detected multi-centre molecule. -/
  ligandOf : Equiv.Perm (Fin 4)
  atomAt_eq : ∀ slot, atomAt input frame slot =
    some (input.detectedMultiCenterMolecule.ligandAtomAt c (ligandOf slot)).val

include agreement admissible supported single in
theorem rootData_exists : Nonempty (RootData input mol c) := by
  classical
  have wf := admissible.1.1
  have uq := admissible.1.2
  have rs := raw_single mol input agreement wf uq supported single
  have valid := raw_atom_bound mol input agreement c.1
  have reached := reached_root mol c.1.val valid
  obtain ⟨target, found, _, corresponds⟩ := lookup?_exists_of_reachedFrom mol input agreement wf uq
    supported rs c.1.val valid (canonicalCenterRoot c.1.val) .refl
  have real := lookup?_real input _ target found rfl
  have detected := lookup_detected_of_physical_center mol input agreement admissible supported
    single c _ rfl target found
  let unit : DetectedOccurrence input.moleculeGraph := ⟨input.molecularFrameUnit target.1, detected⟩
  let execution := rawStateFrames input single [] target real unit rfl
  have computed : input.localizedOccurrenceFourLigandFrame? target = some execution.frame := by
    have h := execution.frameComputed
    rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?] at h
    exact h
  have rawFrame := detected_root_frame mol input agreement admissible supported single c
  have degree := detected_raw_degree mol input agreement wf uq supported c
  have perm : (frameAtomsOf (occurrenceLigandCursors mol (canonicalCenterRoot c.1.val))).Perm
      (mol.canonicalIncidentNeighbors c.1.val) := by
    rcases frame_atoms_perm_neighbors mol wf rs _ reached _ rawFrame with ⟨_, perm⟩ | ⟨three, _⟩
    · exact perm
    · have three' : (mol.canonicalIncidentNeighbors c.1.val).length = 3 := three
      rw [degree] at three'
      cases three'
  have nodup : (frameAtomsOf (occurrenceLigandCursors mol (canonicalCenterRoot c.1.val))).Nodup :=
    perm.nodup_iff.mpr (mol.canonicalIncidentNeighbors_nodup _ uq)
  obtain ⟨read⟩ := readback_exists input mol agreement admissible supported single _ reached target
    found real detected _ rawFrame execution.frame computed
  have meaning := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target
    execution.center).mp execution.centerComputed
  obtain ⟨frame', ligand, computed', current⟩ :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv single
      (Nat.le_succ _) target execution.center meaning
  have frameEq : frame' = execution.frame := Option.some.inj (computed'.symm.trans computed)
  subst frameEq
  have centerEq : execution.center.1 = c.1 := by
    have h := corresponds.current
    rw [meaning.2] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact Fin.ext h
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
  simp only [atomAt, current slot, Option.map_some, Equiv.ofBijective_apply]
  show some (ligand slot).1.val =
    some ((input.moleculeGraph.ligandEquivOfIsTetrahedralCenter c.1 hc (β slot)).1).val
  simp only [β, Equiv.apply_symm_apply]

variable (data : RootData input mol c)

/-- The independent descending key order of the frame slots. -/
noncomputable abbrev sortedSlots : List (Fin 4) :=
  keyOrder (rootKeys input single data.target data.real data.detected) (List.finRange 4)

theorem sortedSlots_perm : (sortedSlots input mol single c data).Perm (List.finRange 4) :=
  keyOrder_perm _ _

theorem sortedSlots_length : (sortedSlots input mol single c data).length = 4 := by
  rw [(sortedSlots_perm input mol single c data).length_eq, List.length_finRange]

theorem sortedSlots_nodup : (sortedSlots input mol single c data).Nodup :=
  (sortedSlots_perm input mol single c data).nodup_iff.mpr (List.nodup_finRange 4)

/-- Ligand index at the `p`-th priority position. -/
noncomputable def priorityLigand (p : Fin 4) : Fin 4 :=
  data.ligandOf ((sortedSlots input mol single c data)[p.val]'(by
    rw [sortedSlots_length]; exact p.isLt))

theorem priorityLigand_injective : Function.Injective (priorityLigand input mol single c data) := by
  intro p q eq
  have := data.ligandOf.injective eq
  exact Fin.ext ((sortedSlots_nodup input mol single c data).getElem_inj_iff.mp this)

/-- The priority permutation: position `p` holds ligand `priorityPerm p`. -/
noncomputable def priorityPerm : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp
    (priorityLigand_injective input mol single c data))

theorem priorityPerm_apply (p : Fin 4) :
    priorityPerm input mol single c data p = priorityLigand input mol single c data p := rfl

/-- The ranked raw atom list is the ligand enumeration along the priority permutation. -/
theorem ranked_eq :
    atomsAt? data.atoms ((sortedSlots input mol single c data).map data.read.index) =
      some [(input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 0)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 1)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 2)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 3)).val] := by
  rw [data.read.atoms]
  rw [mapM_eq_some_map _ (fun slot =>
    (input.detectedMultiCenterMolecule.ligandAtomAt c (data.ligandOf slot)).val) _
    (fun slot _ => data.atomAt_eq slot)]
  congr 1
  rw [list_four_eq (sortedSlots input mol single c data) (sortedSlots_length input mol single c data)]
  rfl

/-- The actual ordinary stage at the root. -/
theorem ordinary_root :
    LocalizedMarkedRetainedOperations.ordinary input mol [] (canonicalCenterRoot c.1.val) =
      some ((sortedSlots input mol single c data).map data.read.index,
        adjacentBy (fun left right => some (compare
          (rootKeys input single data.target data.real data.detected left)
          (rootKeys input single data.target data.real data.detected right)))
          (sortedSlots input mol single c data)) := by
  have frameEq : (rawStateFrames input single [] data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame = data.frame := by
    have h := (rawStateFrames input single [] data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frameComputed
    rw [data.frameExec] at h
    exact (Option.some.inj h).symm
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

theorem consistent_root :
    consistent (adjacentBy (fun left right => some (compare
      (rootKeys input single data.target data.real data.detected left)
      (rootKeys input single data.target data.real data.detected right)))
      (sortedSlots input mol single c data)) = true :=
  consistent_of_gt_or_eq _ (adjacentBy_key_consistent compare completeLigandRule5Key_compare_lt_iff
    completeLigandRule5Key_compare_eq_iff _ _ (keyOrder_pairwise _ _))

theorem strict_root (strictKeys : Function.Injective
    (rootKeys input single data.target data.real data.detected)) :
    strict (adjacentBy (fun left right => some (compare
      (rootKeys input single data.target data.real data.detected left)
      (rootKeys input single data.target data.real data.detected right)))
      (sortedSlots input mol single c data)) = true := by
  apply strict_of_all_gt
  rw [adjacentBy_key_all_gt_iff compare completeLigandRule5Key_compare_lt_iff
    completeLigandRule5Key_compare_eq_iff, keyOrder_chain_iff_injective _ _ (List.nodup_finRange 4)]
  intro a _ b _ equal
  exact strictKeys equal

/-- At a strict root, every raw step reads the geometry in the independent priority order. -/
theorem rawStep_strict (strictKeys : Function.Injective
    (rootKeys input single data.target data.real data.detected))
    (geom : Geometry) (under : Nat → OccurrenceAuxState) :
    LocalizedMarkedOperationEvaluator.rawStep? mol (sparseOperations input mol) geom [] none
        (canonicalCenterRoot c.1.val) under =
      readback? geom
        [(input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 0)).val,
          (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 1)).val,
          (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 2)).val,
          (input.detectedMultiCenterMolecule.ligandAtomAt c (priorityPerm input mol single c data 3)).val] := by
  have ord : (sparseOperations input mol).ordinary [] (canonicalCenterRoot c.1.val) = _ :=
    ordinary_root input mol single c data
  unfold LocalizedMarkedOperationEvaluator.rawStep?
  rw [data.rawFrame, ord]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have good : ¬ (¬ data.atoms.Nodup ∨ consistent (adjacentBy (fun left right => some (compare
      (rootKeys input single data.target data.real data.detected left)
      (rootKeys input single data.target data.real data.detected right)))
      (sortedSlots input mol single c data)) = false) := by
    rw [consistent_root input mol single c data]
    simp [data.nodup]
  rw [if_neg good, if_pos (strict_root input mol single c data strictKeys),
    ranked_eq input mol single c data]
  rfl

/-- Strictly decreasing independent keys along the priority permutation. -/
theorem keys_decreasing (strictKeys : Function.Injective
    (rootKeys input single data.target data.real data.detected)) (p q : Fin 4) (lt : p < q) :
    rootKeys input single data.target data.real data.detected
        (data.ligandOf.symm (priorityPerm input mol single c data q)) <
      rootKeys input single data.target data.real data.detected
        (data.ligandOf.symm (priorityPerm input mol single c data p)) := by
  simp only [priorityPerm_apply, priorityLigand, Equiv.symm_apply_apply]
  have pairwise := keyOrder_pairwise (rootKeys input single data.target data.real data.detected)
    (List.finRange 4)
  rw [List.pairwise_iff_getElem] at pairwise
  have le := pairwise p.val q.val (by rw [sortedSlots_length]; exact p.isLt)
    (by rw [sortedSlots_length]; exact q.isLt) lt
  refine lt_of_le_of_ne le ?_
  intro equal
  have same := strictKeys equal
  have := (sortedSlots_nodup input mol single c data).getElem_inj_iff.mp same
  exact absurd (Fin.ext this) (ne_of_lt lt).symm

end Strict

/-! ## Chemical endpoints -/

section Endpoints

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (c : input.detectedMultiCenterMolecule.Center)
  (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)

/-- Strictness of the independent empty-state keys at the looked-up root occurrence. -/
def StrictRoot : Prop :=
  ∀ target, lookup? input (canonicalCenterRoot c.1.val) = some target →
    ∀ (real : target.1.node.provenance = .realAtom)
      (detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit target.1).atom),
      Function.Injective (rootKeys input single target real detected)

theorem swap_ne (v : RS) : v.swap ≠ v := by cases v <;> simp [RS.swap]

include agreement admissible supported single calibrated in
/-- **Strict centres receive the physical letter in the independent key order** (immediate-frame
recursion, actual sparse operations). The permutation `π` lists the ligands in strictly decreasing
independent key order through the derived slot bijection `ligandOf`. -/
theorem assignCenter_chiral_of_strict (strictRoot : StrictRoot input single c) :
    ∃ data : RootData input mol c, ∃ π : Equiv.Perm (Fin 4),
      (∀ p q : Fin 4, p < q →
        rootKeys input single data.target data.real data.detected (data.ligandOf.symm (π q)) <
          rootKeys input single data.target data.real data.detected (data.ligandOf.symm (π p))) ∧
      LocalizedMarkedOperationEvaluator.assignCenter? mol (sparseOperations input mol)
          (inputGeometry input) c.1.val =
        some (.chiral (letterOfSign
          (input.detectedMultiCenterMolecule.configurationSign cfg c * permHandedness π))) := by
  obtain ⟨data⟩ := rootData_exists input mol agreement admissible supported single c
  have strictKeys := strictRoot data.target data.found data.real data.detected
  refine ⟨data, priorityPerm input mol single c data,
    keys_decreasing input mol single c data strictKeys, ?_⟩
  have reading := readback_enumeration input cfg c calibrated (priorityPerm input mol single c data)
  unfold LocalizedMarkedOperationEvaluator.assignCenter? LocalizedMarkedOperationEvaluator.descriptor?
    LocalizedMarkedOperationEvaluator.descriptorWith? LocalizedMarkedOperationEvaluator.rawWith?
  rw [rawStep_strict input mol single c data strictKeys, rawStep_strict input mol single c data strictKeys,
    readback_mirror, reading]
  simp [caseFromMirror?, swap_ne]

include agreement admissible supported single calibrated in
/-- The distant-reference recursion emits the same letter at strict centres. -/
theorem distant_assignCenter_chiral_of_strict (strictRoot : StrictRoot input single c) :
    ∃ data : RootData input mol c, ∃ π : Equiv.Perm (Fin 4),
      (∀ p q : Fin 4, p < q →
        rootKeys input single data.target data.real data.detected (data.ligandOf.symm (π q)) <
          rootKeys input single data.target data.real data.detected (data.ligandOf.symm (π p))) ∧
      LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol (sparseOperations input mol)
          (inputGeometry input) c.1.val =
        some (.chiral (letterOfSign
          (input.detectedMultiCenterMolecule.configurationSign cfg c * permHandedness π))) := by
  obtain ⟨data⟩ := rootData_exists input mol agreement admissible supported single c
  have strictKeys := strictRoot data.target data.found data.real data.detected
  refine ⟨data, priorityPerm input mol single c data,
    keys_decreasing input mol single c data strictKeys, ?_⟩
  have reading := readback_enumeration input cfg c calibrated (priorityPerm input mol single c data)
  unfold LocalizedPhysicalMarkedDistantEvaluator.assignCenter?
    LocalizedPhysicalMarkedDistantEvaluator.descriptor?
    LocalizedPhysicalMarkedDistantEvaluator.descriptorWith?
    LocalizedPhysicalMarkedDistantEvaluator.rawWith?
  rw [LocalizedPhysicalMarkedDistantReference.rawStep_none,
    LocalizedPhysicalMarkedDistantReference.rawStep_none,
    rawStep_strict input mol single c data strictKeys, rawStep_strict input mol single c data strictKeys,
    readback_mirror, reading]
  simp [caseFromMirror?, swap_ne]

variable (e : input.detectedMultiCenterMolecule.Aut)
  (involutive : ∀ a, (e : Equiv.Perm input.Atom) ((e : Equiv.Perm input.Atom) a) = a)
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)

include agreement admissible supported single involutive atomsPres in
/-- **A strict centre has no ligand-moving involutive symmetry**: every involutive molecular
automorphism fixing the centre acts trivially on its four ligands. -/
theorem ligandPermAt_eq_one_of_strict (strictRoot : StrictRoot input single c)
    (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c) :
    input.detectedMultiCenterMolecule.ligandPermAt e c = 1 := by
  obtain ⟨data⟩ := rootData_exists input mol agreement admissible supported single c
  have strictKeys := strictRoot data.target data.found data.real data.detected
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

end Endpoints

end TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.rootData_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.ranked_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.ordinary_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.rawStep_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.keys_decreasing
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.assignCenter_chiral_of_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.distant_assignCenter_chiral_of_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingCompletenessStrict.ligandPermAt_eq_one_of_strict
