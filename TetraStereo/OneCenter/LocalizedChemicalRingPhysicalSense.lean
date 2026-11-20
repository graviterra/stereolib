import TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport
import TetraStereo.OneCenter.LocalizedPhysicalMarkedParityCompleteness
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.OneCenter.LocalizedMarkedDetectedFrames
import TetraStereo.OneCenter.LocalizedMarkedMolecularConfiguration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# From the physical sign column to the generated readings

This module joins the independent physical relation of
`LocalizedPhysicalMarkedParityCompleteness` to the symmetry transport of the generated readings
(`LocalizedChemicalRingSenseTransport`). The molecule is the certified input's detected
multi-centre molecule, its geometry is the certified input's coordinates (`inputGeometry`), and
a multi-centre automorphism `e` acts on raw atom identifiers through `relabelOf`.

* `readback_enumeration`: at a calibrated centre, the raw readback of any enumeration of the
  four ligand atoms is the configuration sign times the parity of the enumeration.
* `readback_relabel`: the readback of the relabelled enumeration is the original reading when
  `relativeSign e` is `1` at that centre and its complement when it is `-1`.
* `agreeOn_of_proper` / `agreeOn_of_mirror`: a common sense of `e` at every centre below a root
  gives the `AgreeOn` premise of the transport theorems, for the actual frames of the canonical
  expansion (lone-pair phantoms, degenerate and refused readings included).
* `assignCenter_none_of_physical_proper` and its mirror/distant twins: for a centre fixed by
  `e` whose ligand permutation is a transposition, a common proper sense below it forces refusal
  and a common mirror sense excludes an uppercase letter, for both evaluators.

Remaining explicit hypotheses: relabel covariance of the operations (`Covariant`), calibration of
every detected centre, atom-specification preservation by `e`, intake agreement and admission.
No label, ordering, sorting success or branch equivalence is supplied. Completeness (distinct
readings for physically distinguishable branches) is not addressed here.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense

open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? frameAtomsOf readback? mirror
  readback_mirror)
open LocalizedMarkedReachableConfigurations (Reached reached_root)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded frame_atoms_perm_neighbors
  reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single raw_atom_bound)
open LocalizedMarkedDetectedFrames (detected_raw_degree detected_root_frame written_perm_incident)
open LocalizedMarkedConfigurationTransport (readback_none_of_missing frame_length)
open LocalizedMarkedTerminalGaugeSwap (swapAtom readback4)
open LocalizedMarkedCyclicDiscardedReference (readback_length)
open LocalizedChemicalRingRelabel LocalizedChemicalRingSenseTransport
open LocalizedPhysicalMarkedParityCompleteness (relativeSign transportedSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open CertifiedLocalizedCIPInput

abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## Letters of signs -/

/-- The letter read from a nonzero oriented-volume sign. -/
noncomputable def letterOfSign (s : ℝ) : RS := if s < 0 then RS.R else RS.S

theorem descriptor_eq_letterOfSign (v : ℚ) (nonzero : v ≠ 0) :
    descriptorOfOrientedVolume? v = some (letterOfSign (rationalVolumeSign v)) := by
  rcases lt_trichotomy v 0 with neg | zero | pos
  · rw [rationalVolumeSign_of_neg neg]
    simp [descriptorOfOrientedVolume?, neg, letterOfSign]
  · exact absurd zero nonzero
  · rw [rationalVolumeSign_of_pos pos]
    simp [descriptorOfOrientedVolume?, not_lt.mpr pos.le, pos, letterOfSign]

theorem readback_none_of_not_good (geom : Geometry) (L : List Nat)
    (bad : ¬ (L.length = 4 ∧ L.Nodup)) : readback? geom L = none := by
  cases h : readback? geom L with
  | none => rfl
  | some v => exact absurd ⟨readback_length geom L v h, readback_nodup' geom L v h⟩ bad

theorem not_good_map (σ : Nat → Nat) (L : List Nat) (bad : ¬ (L.length = 4 ∧ L.Nodup)) :
    ¬ ((L.map σ).length = 4 ∧ (L.map σ).Nodup) := by
  rintro ⟨four, nodup⟩
  exact bad ⟨by simpa using four, List.Nodup.of_map σ nodup⟩

/-! ## The certified input's geometry and relabellings -/

section Input

variable (input : CertifiedLocalizedCIPInput)

/-- Raw geometry: the certified coordinates at in-range identifiers, nothing elsewhere. -/
def inputGeometry : Geometry := fun x =>
  if h : x < input.certified.input.molecule.atomCount then input.spatialPointAt? ⟨x, h⟩ else none

/-- The raw relabelling induced by a permutation of the certified atoms. -/
def relabelOf (e : Equiv.Perm input.Atom) (x : Nat) : Nat :=
  if h : x < input.certified.input.molecule.atomCount then (e ⟨x, h⟩).val else x

theorem inputGeometry_val (a : input.Atom) :
    inputGeometry input a.val = input.spatialPointAt? a := by
  unfold inputGeometry
  rw [dif_pos a.isLt]

theorem inputGeometry_outside (x : Nat) (h : input.certified.input.molecule.atomCount ≤ x) :
    inputGeometry input x = none := by
  unfold inputGeometry
  rw [dif_neg (Nat.not_lt.mpr h)]

theorem relabelOf_val (e : Equiv.Perm input.Atom) (a : input.Atom) :
    relabelOf input e a.val = (e a).val := by
  unfold relabelOf
  rw [dif_pos a.isLt]

theorem relabelOf_outside (e : Equiv.Perm input.Atom) (x : Nat)
    (h : input.certified.input.molecule.atomCount ≤ x) : relabelOf input e x = x := by
  unfold relabelOf
  rw [dif_neg (Nat.not_lt.mpr h)]

variable (cfg : input.detectedMultiCenterMolecule.Configuration)

theorem configurationSign_unit (c : input.detectedMultiCenterMolecule.Center) :
    input.detectedMultiCenterMolecule.configurationSign cfg c = 1 ∨ input.detectedMultiCenterMolecule.configurationSign cfg c = -1 :=
  permHandedness_eq_one_or_eq_neg_one (cfg c)

/-- **Readback of an enumerated calibrated frame**: configuration sign times enumeration
parity. -/
theorem readback_enumeration (c : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
    (π : Equiv.Perm (Fin 4)) :
    readback? (inputGeometry input)
        [(input.detectedMultiCenterMolecule.ligandAtomAt c (π 0)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 1)).val,
          (input.detectedMultiCenterMolecule.ligandAtomAt c (π 2)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 3)).val] =
      some (letterOfSign (input.detectedMultiCenterMolecule.configurationSign cfg c * permHandedness π)) := by
  obtain ⟨pointAt, points, _, signEq⟩ := calibrated
  rw [readback4, inputGeometry_val, inputGeometry_val, inputGeometry_val, inputGeometry_val,
    points, points, points, points]
  simp only [Option.bind_some]
  have calib : CartesianPoint3.orientedVolume (pointAt (π 0)) (pointAt (π 1)) (pointAt (π 2))
      (pointAt (π 3)) = RationalTetrahedralPermutation.permutedOrientedVolume (pointAt 0)
        (pointAt 1) (pointAt 2) (pointAt 3) π :=
    orientedVolume_calibrated_eq (fun p => pointAt (π p)) pointAt π (fun _ => rfl)
  have signs : rationalVolumeSign (CartesianPoint3.orientedVolume (pointAt (π 0)) (pointAt (π 1))
      (pointAt (π 2)) (pointAt (π 3))) = input.detectedMultiCenterMolecule.configurationSign cfg c * permHandedness π := by
    rw [calib, rationalVolumeSign_permutedOrientedVolume, signEq]
  have nonzero : CartesianPoint3.orientedVolume (pointAt (π 0)) (pointAt (π 1)) (pointAt (π 2))
      (pointAt (π 3)) ≠ 0 := by
    intro zero
    rw [zero] at signs
    have zeroSign : rationalVolumeSign 0 = 0 := by simp [rationalVolumeSign]
    rw [zeroSign] at signs
    rcases configurationSign_unit input cfg c with hc | hc <;>
      rcases permHandedness_eq_one_or_eq_neg_one π with hπ | hπ <;>
      rw [hc, hπ] at signs <;> norm_num at signs
  rw [descriptor_eq_letterOfSign _ nonzero, signs]

theorem map_enumeration (e : input.detectedMultiCenterMolecule.Aut) (c : input.detectedMultiCenterMolecule.Center) (π : Equiv.Perm (Fin 4)) :
    [(input.detectedMultiCenterMolecule.ligandAtomAt c (π 0)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 1)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt c (π 2)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 3)).val].map
          (relabelOf input (e : Equiv.Perm input.Atom)) =
      [(input.detectedMultiCenterMolecule.ligandAtomAt (input.detectedMultiCenterMolecule.centerPerm e c) ((input.detectedMultiCenterMolecule.ligandPermAt e c * π) 0)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt (input.detectedMultiCenterMolecule.centerPerm e c) ((input.detectedMultiCenterMolecule.ligandPermAt e c * π) 1)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt (input.detectedMultiCenterMolecule.centerPerm e c) ((input.detectedMultiCenterMolecule.ligandPermAt e c * π) 2)).val,
        (input.detectedMultiCenterMolecule.ligandAtomAt (input.detectedMultiCenterMolecule.centerPerm e c) ((input.detectedMultiCenterMolecule.ligandPermAt e c * π) 3)).val] := by
  simp only [List.map_cons, List.map_nil, relabelOf_val, Equiv.Perm.mul_apply,
    MultiCenterMolecule.ligandAtomAt_ligandPermAt]

/-- **The relabelled reading is the original or its complement according to the relative
sign** of the automorphism at that centre. -/
theorem readback_relabel (e : input.detectedMultiCenterMolecule.Aut) (c : input.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
    (calibrated' : ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg (input.detectedMultiCenterMolecule.centerPerm e c))
    (π : Equiv.Perm (Fin 4)) :
    readback? (inputGeometry input)
        ([(input.detectedMultiCenterMolecule.ligandAtomAt c (π 0)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 1)).val,
          (input.detectedMultiCenterMolecule.ligandAtomAt c (π 2)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 3)).val].map
            (relabelOf input (e : Equiv.Perm input.Atom))) =
      if relativeSign input.detectedMultiCenterMolecule cfg e c = 1 then
        readback? (inputGeometry input)
          [(input.detectedMultiCenterMolecule.ligandAtomAt c (π 0)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 1)).val,
            (input.detectedMultiCenterMolecule.ligandAtomAt c (π 2)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 3)).val]
      else
        (readback? (inputGeometry input)
          [(input.detectedMultiCenterMolecule.ligandAtomAt c (π 0)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 1)).val,
            (input.detectedMultiCenterMolecule.ligandAtomAt c (π 2)).val, (input.detectedMultiCenterMolecule.ligandAtomAt c (π 3)).val]).map
              RS.swap := by
  rw [map_enumeration, readback_enumeration input cfg _ calibrated',
    readback_enumeration input cfg c calibrated π, permHandedness_mul]
  unfold relativeSign transportedSign
  rcases configurationSign_unit input cfg c with hc | hc <;>
    rcases configurationSign_unit input cfg (input.detectedMultiCenterMolecule.centerPerm e c) with hec | hec <;>
    rcases permHandedness_eq_one_or_eq_neg_one (input.detectedMultiCenterMolecule.ligandPermAt e c) with he | he <;>
    rcases permHandedness_eq_one_or_eq_neg_one π with hπ | hπ <;>
    simp only [hc, hec, he, hπ] <;> norm_num [letterOfSign, RS.swap]

end Input

/-! ## Raw frames of detected centres -/

section Frames

variable (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)

include agreement in
theorem count : input.certified.input.molecule.atomCount = mol.atomCount :=
  mol.toSemanticMolecule?_atomCount input.certified.input.molecule agreement.1

/-- A raw in-range identifier as a certified atom. -/
def atomOf (x : Nat) (h : x < mol.atomCount) : input.Atom :=
  ⟨x, by rw [count mol input agreement]; exact h⟩

@[simp] theorem atomOf_val (x : Nat) (h : x < mol.atomCount) :
    (atomOf mol input agreement x h).val = x := rfl

include agreement wellFormed unique supported in
theorem adj_iff (u v : input.Atom) :
    input.moleculeGraph.Adj u v ↔ 0 < mol.bondOrder u.val v.val := by
  unfold MoleculeGraph.Adj
  rw [moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported]

include agreement wellFormed unique supported in
theorem mem_neighbors_iff (c : input.detectedMultiCenterMolecule.Center) (y : Nat) :
    y ∈ mol.canonicalIncidentNeighbors c.1.val ↔ ∃ i, (input.detectedMultiCenterMolecule.ligandAtomAt c i).val = y := by
  rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed]
  constructor
  · intro positive
    have bounds := mol.bondOrder_pos_endpoint_lt wellFormed positive
    have adj : input.moleculeGraph.Adj c.1 (atomOf mol input agreement y bounds.2) :=
      (adj_iff mol input agreement wellFormed unique supported _ _).mpr positive
    obtain ⟨i, hi⟩ := input.detectedMultiCenterMolecule.ligandAtomAt_surjective c _ adj
    exact ⟨i, by rw [hi]; rfl⟩
  · rintro ⟨i, rfl⟩
    exact (adj_iff mol input agreement wellFormed unique supported c.1 _).mp
      (input.detectedMultiCenterMolecule.ligandAtomAt_adj c i)

include agreement wellFormed unique supported in
/-- A raw atom with four neighbours is a detected centre. -/
theorem center_of_degree (x : Nat) (hx : x < mol.atomCount)
    (four : (mol.canonicalIncidentNeighbors x).length = 4) :
    atomOf mol input agreement x hx ∈ input.detectedMultiCenterMolecule.centers := by
  show atomOf mol input agreement x hx ∈ input.moleculeGraph.detectedMultiCenterMolecule.centers
  rw [MoleculeGraph.mem_detectedMultiCenterMolecule_centers_iff,
    MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card]
  have nodup := mol.canonicalIncidentNeighbors_nodup x unique
  have inRange : ∀ i (h : i < 4), (mol.canonicalIncidentNeighbors x)[i]'(by rw [four]; exact h) <
      mol.atomCount := by
    intro i h
    have member := List.getElem_mem (l := mol.canonicalIncidentNeighbors x) (by rw [four]; exact h)
    exact (mol.bondOrder_pos_endpoint_lt wellFormed
      ((mol.mem_canonicalIncidentNeighbors_iff x wellFormed _).mp member)).2
  refine Finset.card_eq_of_bijective
    (fun i h => atomOf mol input agreement _ (inRange i h)) ?_ ?_ ?_
  · intro y memberY
    rw [MoleculeGraph.mem_neighborFinset, adj_iff mol input agreement wellFormed unique supported,
      atomOf_val, ← mol.mem_canonicalIncidentNeighbors_iff x wellFormed,
      List.mem_iff_getElem] at memberY
    obtain ⟨i, hi, eq⟩ := memberY
    refine ⟨i, by rw [← four]; exact hi, ?_⟩
    apply Fin.ext
    simp only [atomOf_val]
    exact eq
  · intro i h
    rw [MoleculeGraph.mem_neighborFinset, adj_iff mol input agreement wellFormed unique supported,
      atomOf_val, atomOf_val, ← mol.mem_canonicalIncidentNeighbors_iff x wellFormed]
    exact List.getElem_mem _
  · intro i j hi hj eq
    have vals := congrArg Fin.val eq
    simp only [atomOf_val] at vals
    exact (nodup.getElem_inj_iff).mp vals

/-- The reference enumeration of a centre's ligand atoms (identity permutation). -/
noncomputable def baseFrame (c : input.detectedMultiCenterMolecule.Center) : List Nat :=
  [(input.detectedMultiCenterMolecule.ligandAtomAt c ((1 : Equiv.Perm (Fin 4)) 0)).val,
    (input.detectedMultiCenterMolecule.ligandAtomAt c ((1 : Equiv.Perm (Fin 4)) 1)).val,
    (input.detectedMultiCenterMolecule.ligandAtomAt c ((1 : Equiv.Perm (Fin 4)) 2)).val,
    (input.detectedMultiCenterMolecule.ligandAtomAt c ((1 : Equiv.Perm (Fin 4)) 3)).val]

theorem baseFrame_nodup (c : input.detectedMultiCenterMolecule.Center) : (baseFrame input c).Nodup := by
  have inj := input.detectedMultiCenterMolecule.ligandAtomAt_injective c
  have ne : ∀ i j : Fin 4, i ≠ j →
      (input.detectedMultiCenterMolecule.ligandAtomAt c i).val ≠
        (input.detectedMultiCenterMolecule.ligandAtomAt c j).val :=
    fun i j hij h => hij (inj (Fin.ext h))
  simp only [baseFrame, Equiv.Perm.one_apply]
  simp [List.nodup_cons, ne 0 1 (by decide), ne 0 2 (by decide), ne 0 3 (by decide),
    ne 1 2 (by decide), ne 1 3 (by decide), ne 2 3 (by decide)]

theorem baseFrame_length (c : input.detectedMultiCenterMolecule.Center) : (baseFrame input c).length = 4 := rfl

theorem mem_baseFrame (c : input.detectedMultiCenterMolecule.Center) (i : Fin 4) :
    (input.detectedMultiCenterMolecule.ligandAtomAt c i).val ∈ baseFrame input c := by
  fin_cases i <;> simp [baseFrame, Equiv.Perm.one_apply]

end Frames

/-! ## The agreement premise from a common sense below a root -/

section Agreement

variable (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (wellFormed : mol.WellFormed) (unique : mol.BondRecordsUnique)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (singleGraph : input.moleculeGraph.SimpleBonded)
  (cfg : input.detectedMultiCenterMolecule.Configuration)

theorem reached_of_below (root : Nat) (valid : root < mol.atomCount) (node : Node)
    (below : Below mol (canonicalCenterRoot root) node) : Reached mol node := by
  obtain ⟨child, edge, path⟩ := below
  exact ⟨root, valid, (Relation.ReflTransGen.single edge).trans path⟩

include agreement wellFormed unique supported singleGraph in
/-- **The sense column gives readback agreement below the root.** `sense` fixes the relative
sign of `e` at every detected centre read through a frame below the root.
Forced ring-duplicate leaves have no frame and impose no sign condition. -/
theorem agreeOn_of_sense (e : input.detectedMultiCenterMolecule.Aut) (root : Nat) (valid : root < mol.atomCount)
    (mirrorSense : Bool)
    (calibrated : ∀ c : input.detectedMultiCenterMolecule.Center, ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
    (sense : ∀ node, Below mol (canonicalCenterRoot root) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ c : input.detectedMultiCenterMolecule.Center, c.1.val = node.atom →
        relativeSign input.detectedMultiCenterMolecule cfg e c = if mirrorSense then -1 else 1) :
    AgreeOn (Below mol (canonicalCenterRoot root)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))
      (if mirrorSense then mirror (inputGeometry input) else inputGeometry input) := by
  intro node below atoms frame L sub
  have reached := reached_of_below mol root valid node below
  have single : SingleBonded mol := raw_single mol input agreement wellFormed unique supported singleGraph
  have target : ∀ L' : List Nat,
      readback? (if mirrorSense then mirror (inputGeometry input) else inputGeometry input) L' =
        if mirrorSense then (readback? (inputGeometry input) L').map RS.swap
        else readback? (inputGeometry input) L' := by
    intro L'
    cases mirrorSense <;> simp [readback_mirror]
  have bothNone : ¬ (L.length = 4 ∧ L.Nodup) →
      readback? (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input)) L =
        readback? (if mirrorSense then mirror (inputGeometry input) else inputGeometry input) L := by
    intro bad
    rw [← readback_map, target, readback_none_of_not_good _ _ (not_good_map _ L bad),
      readback_none_of_not_good _ L bad]
    cases mirrorSense <;> rfl
  have phantomNone : inputGeometry input mol.atomCount = none :=
    inputGeometry_outside input _ (by rw [count mol input agreement])
  rcases frame_atoms_perm_neighbors mol wellFormed single node reached atoms frame with
    ⟨four, perm⟩ | ⟨three, perm⟩
  · have hx := reached_atom_valid mol wellFormed node reached
    let c : input.detectedMultiCenterMolecule.Center :=
      ⟨atomOf mol input agreement node.atom hx,
        center_of_degree mol input agreement wellFormed unique supported node.atom hx four⟩
    have subBase : ∀ y ∈ L, y ∈ baseFrame input c := by
      intro y hy
      obtain ⟨i, rfl⟩ := (mem_neighbors_iff mol input agreement wellFormed unique supported c y).mp
        (perm.mem_iff.mp (sub y hy))
      exact mem_baseFrame input c i
    by_cases good : L.length = 4 ∧ L.Nodup
    · have permBase : L.Perm (baseFrame input c) :=
        (good.2.subperm subBase).perm_of_length_le (by rw [good.1, baseFrame_length])
      refine LocalizedMarkedMolecularConfiguration.readback_perm_congr (baseFrame input c) L
        (baseFrame_nodup input c) (baseFrame_length input c) permBase ?_
      have rel := sense node below atoms frame c rfl
      rw [← readback_map, target]
      unfold baseFrame
      rw [readback_relabel input cfg e c (calibrated c) (calibrated _) 1, rel]
      cases mirrorSense <;> norm_num
    · exact bothNone good
  · by_cases phantom : mol.atomCount ∈ L
    · have left : readback? (inputGeometry input)
          (L.map (relabelOf input (e : Equiv.Perm input.Atom))) = none := by
        refine readback_none_of_missing _ _ (relabelOf input _ mol.atomCount)
          (List.mem_map_of_mem phantom) ?_
        rw [relabelOf_outside input _ _ (by rw [count mol input agreement])]
        exact phantomNone
      rw [← readback_map, target, left, readback_none_of_missing _ L _ phantom phantomNone]
      cases mirrorSense <;> rfl
    · have subNeighbors : ∀ y ∈ L, y ∈ mol.canonicalIncidentNeighbors node.atom := by
        intro y hy
        have member := perm.mem_iff.mp (sub y hy)
        rw [List.mem_append, List.mem_singleton] at member
        rcases member with inside | isPhantom
        · exact inside
        · exact absurd (isPhantom ▸ hy) phantom
      refine bothNone ?_
      rintro ⟨four, nodup⟩
      have := (nodup.subperm subNeighbors).length_le
      rw [four, three] at this
      omega

include agreement wellFormed unique supported singleGraph in
theorem agreeOn_of_proper (e : input.detectedMultiCenterMolecule.Aut) (root : Nat) (valid : root < mol.atomCount)
    (calibrated : ∀ c : input.detectedMultiCenterMolecule.Center, ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
    (proper : ∀ node, Below mol (canonicalCenterRoot root) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ c : input.detectedMultiCenterMolecule.Center, c.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e c = 1) :
    AgreeOn (Below mol (canonicalCenterRoot root)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))
      (inputGeometry input) := by
  have := agreeOn_of_sense mol input agreement wellFormed unique supported singleGraph cfg e root
    valid false calibrated (fun node below atoms frame c eq => by simpa using proper node below atoms frame c eq)
  simpa using this

include agreement wellFormed unique supported singleGraph in
theorem agreeOn_of_mirror (e : input.detectedMultiCenterMolecule.Aut) (root : Nat) (valid : root < mol.atomCount)
    (calibrated : ∀ c : input.detectedMultiCenterMolecule.Center, ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c)
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot root) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ c : input.detectedMultiCenterMolecule.Center, c.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e c = -1) :
    AgreeOn (Below mol (canonicalCenterRoot root)) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom)) (inputGeometry input))
      (mirror (inputGeometry input)) := by
  have := agreeOn_of_sense mol input agreement wellFormed unique supported singleGraph cfg e root
    valid true calibrated (fun node below atoms frame c eq => by simpa using mirrorSense node below atoms frame c eq)
  simpa using this

end Agreement

/-! ## A molecular symmetry from a multi-centre automorphism -/

section SymmetryOfAut

variable (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)

/-- Whether the written lone-pair phantom is inserted at an atom. -/
def lonePairActive (x : Nat) : Bool :=
  match mol.atomAt? x with
  | some spec =>
      RawMolecule.centreElementUsesLonePair spec.element && (mol.writtenNeighbors x).length == 3
  | none => false

/-- The written ligand view is, up to order, the written neighbours with the phantom when
active. -/
theorem ligands_perm_shape (x : Nat) :
    (mol.ligandsWithLonePair x).Perm
      ((if lonePairActive mol x then [mol.atomCount] else []) ++ mol.writtenNeighbors x) := by
  unfold RawMolecule.ligandsWithLonePair lonePairActive
  cases mol.atomAt? x with
  | none => simp
  | some spec =>
      simp only
      by_cases active : (RawMolecule.centreElementUsesLonePair spec.element &&
          (mol.writtenNeighbors x).length == 3) = true
      · rw [if_pos active, if_pos active]
        cases mol.hydrogenHasPreceding x with
        | false => simp
        | true =>
            cases mol.writtenNeighbors x with
            | nil => simp
            | cons first rest =>
                show (first :: mol.atomCount :: rest).Perm ([mol.atomCount] ++ first :: rest)
                exact List.Perm.swap mol.atomCount first rest
      · rw [if_neg active, if_neg active]
        simp

theorem relabel_involutive (e : Equiv.Perm input.Atom) (involutive : ∀ a, e (e a) = a) :
    Function.Involutive (relabelOf input e) := by
  intro x
  by_cases h : x < input.certified.input.molecule.atomCount
  · unfold relabelOf
    rw [dif_pos h, dif_pos (e ⟨x, h⟩).isLt]
    exact congrArg Fin.val (involutive ⟨x, h⟩)
  · rw [relabelOf_outside input e x (Nat.not_lt.mp h), relabelOf_outside input e x (Nat.not_lt.mp h)]

include agreement in
theorem relabelOf_lt (e : Equiv.Perm input.Atom) (x : Nat) (hx : x < mol.atomCount) :
    relabelOf input e x < mol.atomCount := by
  unfold relabelOf
  rw [dif_pos (by rw [count mol input agreement]; exact hx)]
  exact lt_of_lt_of_eq (e ⟨x, by rw [count mol input agreement]; exact hx⟩).isLt
    (count mol input agreement)

include agreement admissible supported in
/-- Bond orders are preserved by the relabelling of a multi-centre automorphism. -/
theorem bondOrder_relabel (e : input.detectedMultiCenterMolecule.Aut) (x y : Nat) :
    mol.bondOrder (relabelOf input (e : Equiv.Perm input.Atom) x)
        (relabelOf input (e : Equiv.Perm input.Atom) y) = mol.bondOrder x y := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have aut : input.moleculeGraph.IsAutomorphism (e : Equiv.Perm input.Atom) :=
    MultiCenterMolecule.Aut.mem_molAut (m := input.detectedMultiCenterMolecule) e
  have zero : ∀ u v, mol.atomCount ≤ u ∨ mol.atomCount ≤ v → mol.bondOrder u v = 0 := by
    intro u v h
    by_contra ne
    have bounds := mol.bondOrder_pos_endpoint_lt wellFormed (Nat.pos_of_ne_zero ne)
    rcases h with h | h
    · exact absurd bounds.1 (Nat.not_lt.mpr h)
    · exact absurd bounds.2 (Nat.not_lt.mpr h)
  rcases Nat.lt_or_ge x mol.atomCount with hx | hx <;>
    rcases Nat.lt_or_ge y mol.atomCount with hy | hy
  · have := aut.2.2.2 (atomOf mol input agreement x hx) (atomOf mol input agreement y hy)
    rw [moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported,
      moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported] at this
    simp only [atomOf_val] at this
    unfold relabelOf
    rw [dif_pos (by rw [count mol input agreement]; exact hx),
      dif_pos (by rw [count mol input agreement]; exact hy)]
    exact this
  · rw [relabelOf_outside input _ y (by rw [count mol input agreement]; exact hy),
      zero x y (Or.inr hy), zero _ y (Or.inr hy)]
  · rw [relabelOf_outside input _ x (by rw [count mol input agreement]; exact hx),
      zero x y (Or.inl hx), zero x _ (Or.inl hx)]
  · rw [relabelOf_outside input _ x (by rw [count mol input agreement]; exact hx),
      relabelOf_outside input _ y (by rw [count mol input agreement]; exact hy)]

include agreement admissible supported in
theorem neighbors_relabel (e : input.detectedMultiCenterMolecule.Aut)
    (involutive : ∀ a, (e : Equiv.Perm input.Atom) ((e : Equiv.Perm input.Atom) a) = a) (x : Nat) :
    (mol.canonicalIncidentNeighbors (relabelOf input (e : Equiv.Perm input.Atom) x)).Perm
      ((mol.canonicalIncidentNeighbors x).map (relabelOf input (e : Equiv.Perm input.Atom))) := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have inj : Function.Injective (relabelOf input (e : Equiv.Perm input.Atom)) :=
    (relabel_involutive input _ involutive).injective
  rw [List.perm_ext_iff_of_nodup (mol.canonicalIncidentNeighbors_nodup _ unique)
    ((mol.canonicalIncidentNeighbors_nodup _ unique).map inj)]
  intro y
  rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed, List.mem_map]
  constructor
  · intro positive
    refine ⟨relabelOf input _ y, ?_, relabel_involutive input _ involutive y⟩
    rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed,
      ← bondOrder_relabel mol input agreement admissible supported e, relabel_involutive input _ involutive]
    exact positive
  · rintro ⟨z, member, rfl⟩
    rw [mol.mem_canonicalIncidentNeighbors_iff _ wellFormed] at member
    rw [bondOrder_relabel mol input agreement admissible supported e]
    exact member

include agreement admissible supported in
/-- **A multi-centre automorphism preserving atom specifications is a molecular symmetry** of the
raw expansion. -/
theorem symmetry_of_aut (e : input.detectedMultiCenterMolecule.Aut)
    (involutive : ∀ a, (e : Equiv.Perm input.Atom) ((e : Equiv.Perm input.Atom) a) = a)
    (atomsPres : ∀ x, x < mol.atomCount →
      mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x) :
    Symmetry mol (relabelOf input (e : Equiv.Perm input.Atom)) where
  involutive := relabel_involutive input _ involutive
  inRange := fun x hx => relabelOf_lt mol input agreement _ x hx
  outside := fun x hx => relabelOf_outside input _ x (by rw [count mol input agreement]; exact hx)
  atoms := atomsPres
  bonds := bondOrder_relabel mol input agreement admissible supported e
  ligands := by
    intro x hx
    have wellFormed := admissible.1.1
    have unique := admissible.1.2
    have written := admissible.2
    have w := written_perm_incident mol wellFormed unique written ⟨x, hx⟩
    have w' := written_perm_incident mol wellFormed unique written
      ⟨_, relabelOf_lt mol input agreement (e : Equiv.Perm input.Atom) x hx⟩
    have nb := neighbors_relabel mol input agreement admissible supported e involutive x
    have lengthEq : (mol.writtenNeighbors (relabelOf input (e : Equiv.Perm input.Atom) x)).length =
        (mol.writtenNeighbors x).length := by
      rw [w'.length_eq, nb.length_eq, List.length_map, w.length_eq]
    have active : lonePairActive mol (relabelOf input (e : Equiv.Perm input.Atom) x) =
        lonePairActive mol x := by
      unfold lonePairActive
      rw [atomsPres x hx, lengthEq]
    have phantom : relabelOf input (e : Equiv.Perm input.Atom) mol.atomCount = mol.atomCount :=
      relabelOf_outside input _ _ (by rw [count mol input agreement])
    refine (ligands_perm_shape mol _).trans ?_
    refine List.Perm.trans ?_ ((ligands_perm_shape mol x).map _).symm
    rw [List.map_append, active]
    refine List.Perm.append (List.Perm.of_eq ?_) (w'.trans (nb.trans (w.map _).symm))
    cases lonePairActive mol x <;> simp [phantom]

end SymmetryOfAut

/-! ## The exchanged centre and the chemical instances -/

section Instances

variable (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (singleGraph : input.moleculeGraph.SimpleBonded)

include agreement admissible supported singleGraph in
/-- A centre fixed by `e` whose ligand permutation is a transposition is an exchanged centre of
the raw expansion, at the actual root frame. -/
theorem exchangedCentre (e : input.detectedMultiCenterMolecule.Aut) (c : input.detectedMultiCenterMolecule.Center)
    (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c) (i j : Fin 4) (ne : i ≠ j)
    (swapEq : input.detectedMultiCenterMolecule.ligandPermAt e c = Equiv.swap i j) :
    ExchangedCentre mol (relabelOf input (e : Equiv.Perm input.Atom)) c.1.val
      (frameAtomsOf (occurrenceLigandCursors mol (canonicalCenterRoot c.1.val)))
      (input.detectedMultiCenterMolecule.ligandAtomAt c i).val (input.detectedMultiCenterMolecule.ligandAtomAt c j).val := by
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have single : SingleBonded mol := raw_single mol input agreement wellFormed unique supported singleGraph
  have valid := raw_atom_bound mol input agreement c.1
  have frame := detected_root_frame mol input agreement admissible supported singleGraph c
  have degree := detected_raw_degree mol input agreement wellFormed unique supported c
  have perm : (frameAtomsOf (occurrenceLigandCursors mol (canonicalCenterRoot c.1.val))).Perm
      (mol.canonicalIncidentNeighbors c.1.val) := by
    rcases frame_atoms_perm_neighbors mol wellFormed single _ (reached_root mol _ valid) _ frame with
      ⟨_, perm⟩ | ⟨three, _⟩
    · exact perm
    · have three' : (mol.canonicalIncidentNeighbors c.1.val).length = 3 := three
      rw [degree] at three'
      cases three'
  have memLigand : ∀ k, (input.detectedMultiCenterMolecule.ligandAtomAt c k).val ∈
      frameAtomsOf (occurrenceLigandCursors mol (canonicalCenterRoot c.1.val)) := fun k =>
    perm.mem_iff.mpr ((mem_neighbors_iff mol input agreement wellFormed unique supported c _).mpr
      ⟨k, rfl⟩)
  refine ⟨valid, ?_, frame, ?_, memLigand i, memLigand j, ?_⟩
  · rw [relabelOf_val]
    exact congrArg Fin.val
      ((RootedTetrahedralBranchSymmetry.centerPerm_eq_iff input.detectedMultiCenterMolecule e c).mp fixed)
  · intro eq
    exact ne (input.detectedMultiCenterMolecule.ligandAtomAt_injective c (Fin.ext eq))
  · intro x hx
    obtain ⟨k, rfl⟩ := (mem_neighbors_iff mol input agreement wellFormed unique supported c x).mp
      (perm.mem_iff.mp hx)
    rw [relabelOf_val, ← MultiCenterMolecule.ligandAtomAt_ligandPermAt, fixed, swapEq]
    have inj := input.detectedMultiCenterMolecule.ligandAtomAt_injective c
    have hji : (input.detectedMultiCenterMolecule.ligandAtomAt c j).val ≠
        (input.detectedMultiCenterMolecule.ligandAtomAt c i).val :=
      fun h => ne (inj (Fin.ext h)).symm
    by_cases ki : k = i
    · rw [ki, Equiv.swap_apply_left]
      simp [swapAtom]
    · by_cases kj : k = j
      · rw [kj, Equiv.swap_apply_right]
        simp [swapAtom, hji]
      · have neI : (input.detectedMultiCenterMolecule.ligandAtomAt c k).val ≠
            (input.detectedMultiCenterMolecule.ligandAtomAt c i).val :=
          fun h => ki (inj (Fin.ext h))
        have neJ : (input.detectedMultiCenterMolecule.ligandAtomAt c k).val ≠
            (input.detectedMultiCenterMolecule.ligandAtomAt c j).val :=
          fun h => kj (inj (Fin.ext h))
        rw [Equiv.swap_apply_of_ne_of_ne ki kj]
        simp [swapAtom, neI, neJ]

variable {ops : LocalizedMarkedOperationEvaluator.Operations}
  (cfg : input.detectedMultiCenterMolecule.Configuration) (e : input.detectedMultiCenterMolecule.Aut)
  (involutive : ∀ a, (e : Equiv.Perm input.Atom) ((e : Equiv.Perm input.Atom) a) = a)
  (atomsPres : ∀ x, x < mol.atomCount →
    mol.atomAt? (relabelOf input (e : Equiv.Perm input.Atom) x) = mol.atomAt? x)
  (cov : Covariant mol ops (relabelOf input (e : Equiv.Perm input.Atom)))
  (c : input.detectedMultiCenterMolecule.Center) (fixed : input.detectedMultiCenterMolecule.centerPerm e c = c) {i j : Fin 4} (ne : i ≠ j)
  (swapEq : input.detectedMultiCenterMolecule.ligandPermAt e c = Equiv.swap i j)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center, ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported singleGraph involutive atomsPres cov fixed ne swapEq calibrated in
/-- **Refusal under a physical proper transposition symmetry**, existing evaluator: `e` fixes
the centre, exchanges two of its ligands, and has relative sign `1` at every detected centre
below it. -/
theorem assignCenter_none_of_physical_proper
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol ops (inputGeometry input) c.1.val = none :=
  assignCenter_none_of_proper (symmetry_of_aut mol input agreement admissible supported e involutive atomsPres)
    admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported singleGraph) cov
    (exchangedCentre mol input agreement admissible supported singleGraph e c fixed i j ne swapEq) _
    (agreeOn_of_proper mol input agreement admissible.1.1 admissible.1.2 supported singleGraph cfg e
      _ (raw_atom_bound mol input agreement c.1) calibrated proper)

include agreement admissible supported singleGraph involutive atomsPres cov fixed ne swapEq calibrated in
/-- **No uppercase letter under a physical mirror transposition symmetry**, existing evaluator. -/
theorem assignCenter_not_chiral_of_physical_mirror
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1) (v : RS) :
    LocalizedMarkedOperationEvaluator.assignCenter? mol ops (inputGeometry input) c.1.val ≠
      some (.chiral v) :=
  assignCenter_not_chiral_of_mirror
    (symmetry_of_aut mol input agreement admissible supported e involutive atomsPres)
    admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported singleGraph) cov
    (exchangedCentre mol input agreement admissible supported singleGraph e c fixed i j ne swapEq) _
    (agreeOn_of_mirror mol input agreement admissible.1.1 admissible.1.2 supported singleGraph cfg e
      _ (raw_atom_bound mol input agreement c.1) calibrated mirrorSense) v

include agreement admissible supported singleGraph involutive atomsPres cov fixed ne swapEq calibrated in
/-- Refusal under a physical proper transposition symmetry, distant-reference successor. -/
theorem distant_assignCenter_none_of_physical_proper
    (proper : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = 1) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops (inputGeometry input) c.1.val =
      none :=
  distant_assignCenter_none_of_proper
    (symmetry_of_aut mol input agreement admissible supported e involutive atomsPres)
    admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported singleGraph) cov
    (exchangedCentre mol input agreement admissible supported singleGraph e c fixed i j ne swapEq) _
    (agreeOn_of_proper mol input agreement admissible.1.1 admissible.1.2 supported singleGraph cfg e
      _ (raw_atom_bound mol input agreement c.1) calibrated proper)

include agreement admissible supported singleGraph involutive atomsPres cov fixed ne swapEq calibrated in
/-- No uppercase letter under a physical mirror transposition symmetry, distant-reference
successor. -/
theorem distant_assignCenter_not_chiral_of_physical_mirror
    (mirrorSense : ∀ node, Below mol (canonicalCenterRoot c.1.val) node →
      ∀ atoms, frameAtoms? mol node = some atoms → ∀ d : input.detectedMultiCenterMolecule.Center, d.1.val = node.atom → relativeSign input.detectedMultiCenterMolecule cfg e d = -1) (v : RS) :
    LocalizedPhysicalMarkedDistantEvaluator.assignCenter? mol ops (inputGeometry input) c.1.val ≠
      some (.chiral v) :=
  distant_assignCenter_not_chiral_of_mirror
    (symmetry_of_aut mol input agreement admissible supported e involutive atomsPres)
    admissible.1.1 admissible.1.2
    (raw_single mol input agreement admissible.1.1 admissible.1.2 supported singleGraph) cov
    (exchangedCentre mol input agreement admissible supported singleGraph e c fixed i j ne swapEq) _
    (agreeOn_of_mirror mol input agreement admissible.1.1 admissible.1.2 supported singleGraph cfg e
      _ (raw_atom_bound mol input agreement c.1) calibrated mirrorSense) v

end Instances

end TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.descriptor_eq_letterOfSign
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.readback_enumeration
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.readback_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.mem_neighbors_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.center_of_degree
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.baseFrame_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.agreeOn_of_sense
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.agreeOn_of_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.agreeOn_of_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.bondOrder_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.symmetry_of_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.exchangedCentre
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.assignCenter_none_of_physical_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.assignCenter_not_chiral_of_physical_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.distant_assignCenter_none_of_physical_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense.distant_assignCenter_not_chiral_of_physical_mirror
