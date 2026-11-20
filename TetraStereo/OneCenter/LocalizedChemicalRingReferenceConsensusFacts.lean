import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusContext
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
**The actual generated facts of the root do not depend on which root reference was selected.**

For both geometry sides and all four actually eligible root references, the recursively
generated state of the 46-atom root is literally the same list. The induction runs over the
actual occurrence forest of the four root arms, at the actual call depth; the depth bound is
required because the separation at `o+` and `o-` reads a generated label at the end of a
covering path. Every local case is derived; no reading success, label or comparison is supplied.

This does not yet assert root consensus: it removes the dependence of the ordinary keys on the
reference. Injectivity of those keys is proved separately.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingReferenceOrbitStabilizer
open LocalizedChemicalRingReferenceConsensusSymmetry LocalizedChemicalRingReferenceConsensusStabilizer
open LocalizedChemicalRingReferenceConsensusArmSeparation
open LocalizedChemicalRingReferenceConsensusArmMirror (arm_prior_separate_side)
open LocalizedChemicalRingReferenceConsensusArmTwin
open LocalizedChemicalRingReferenceConsensusArmBranch (descends_history)
open LocalizedChemicalRingReferenceConsensusContext
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSenseTransport (factsWith factsWith_succ descriptorWith)
open LocalizedChemicalRingPhysicalSense (relabelOf relabelOf_val relabelOf_outside atomOf center_of_degree)
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends descendant_reached history_mono)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachedFrameNeighbors (frame_atoms_perm_neighbors reached_atom_valid)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedMarkedDetectedFrames (detected_frame)
open LocalizedMarkedOperationEvaluator (mem_tiedChildren_actual underWith)
open LocalizedChemicalRingOrientationInduction (mirror_mirror)
open LocalizedGenericMarkedRecalculation (frameAtoms? frameAtoms?_forcedLeaf mirror structuralDepth
  flatMap_congr_mem)

noncomputable section
open scoped Classical

/-! ## Ordinary injectivity at `o+` and `o-` -/

theorem referenceAt_injective (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) :
    Function.Injective (referenceAt certified mol c node data) := by
  intro left right same
  exact data.ligandOf.injective (physical.ligandAtomAt_injective c same)

private theorem neighbors26 (x : Fin 46) (adjacent : graph.Adj 26 x) :
    x = 1 ∨ x = 27 ∨ x = 34 ∨ x = 35 := by
  revert adjacent
  fin_cases x <;> decide +kernel

private theorem o_injective (a : Fin 46) (allowed : RootMark a)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData certified mol otherCurrent node)
    (path : Descends mol (nodeOf [0, a.val]) node) (notStart : node.atom ≠ a.val)
    (member26 : (26 : Fin 46).val ∈ node.history) (member27 : (27 : Fin 46).val ∈ node.history)
    (state : OccurrenceAuxState) (s34 s35 : Fin 4)
    (at34 : referenceAt certified mol otherCurrent node data s34 = (34 : Fin 46))
    (at35 : referenceAt certified mol otherCurrent node data s35 = (35 : Fin 46))
    (separate : rawStateKeys certified single_bonded state data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl s34 ≠
      rawStateKeys certified single_bonded state data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl s35) :
    Function.Injective (rawStateKeys certified single_bonded state data.target data.real
      ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl) := by
  intro left right tie
  by_contra different
  obtain ⟨e, fixed, _, entry⟩ := tie_symmetry a allowed otherCurrent node data path notStart state
    left right different tie
  have fixed26 : e.val (26 : Fin 46) = (26 : Fin 46) :=
    fixed _ (history_of_data otherCurrent node data 26 member26)
  have fixed27 : e.val (27 : Fin 46) = (27 : Fin 46) :=
    fixed _ (history_of_data otherCurrent node data 27 member27)
  have fixed1 : e.val (1 : Fin 46) = (1 : Fin 46) :=
    fixed_of_signature graph ⟨e.val, e.2.1⟩ ([26] : List (Fin 46)) (1 : Fin 46)
      (by
        intro b member
        rw [List.mem_singleton.mp member]
        exact fixed26)
      (by unfold SignatureUnique; decide +kernel)
  have adjacentL : graph.Adj 26 (referenceAt certified mol otherCurrent node data left) :=
    physical.ligandAtomAt_adj otherCurrent (data.ligandOf left)
  have adjacentR : graph.Adj 26 (referenceAt certified mol otherCurrent node data right) :=
    physical.ligandAtomAt_adj otherCurrent (data.ligandOf right)
  have distinct : referenceAt certified mol otherCurrent node data left ≠
      referenceAt certified mol otherCurrent node data right :=
    fun same => different (referenceAt_injective otherCurrent node data same)
  have slotOf (slot : Fin 4) (b : Fin 4) (atom : Fin 46)
      (first : referenceAt certified mol otherCurrent node data slot = atom)
      (second : referenceAt certified mol otherCurrent node data b = atom) : slot = b :=
    referenceAt_injective otherCurrent node data (first.trans second.symm)
  have fromFixed (atom : Fin 46) (fixedAtom : e.val atom = atom)
      (atLeft : referenceAt certified mol otherCurrent node data left = atom) : False := by
    apply distinct
    rw [← entry, atLeft, fixedAtom]
  have toFixed (atom : Fin 46) (fixedAtom : e.val atom = atom)
      (atRight : referenceAt certified mol otherCurrent node data right = atom) : False := by
    apply distinct
    apply e.val.injective
    rw [entry, atRight, fixedAtom]
  rcases neighbors26 _ adjacentL with h1 | h27 | h34 | h35
  · exact fromFixed 1 fixed1 h1
  · exact fromFixed 27 fixed27 h27
  · rcases neighbors26 _ adjacentR with g1 | g27 | g34 | g35
    · exact toFixed 1 fixed1 g1
    · exact toFixed 27 fixed27 g27
    · exact distinct (h34.trans g34.symm)
    · have sameL := slotOf left s34 34 h34 at34
      have sameR := slotOf right s35 35 g35 at35
      subst sameL
      subst sameR
      exact separate tie
  · rcases neighbors26 _ adjacentR with g1 | g27 | g34 | g35
    · exact toFixed 1 fixed1 g1
    · exact toFixed 27 fixed27 g27
    · have sameL := slotOf left s35 35 h35 at35
      have sameR := slotOf right s34 34 g34 at34
      subst sameL
      subst sameR
      exact separate tie.symm
    · exact distinct (h35.trans g35.symm)

theorem plus_descends : Descends mol (nodeOf [0, 28]) armNode :=
  have first : nodeOf [0, 28, 32] ∈ mol.canonicalChildren (nodeOf [0, 28]) := by decide +kernel
  have second : nodeOf [0, 28, 32, 27] ∈ mol.canonicalChildren (nodeOf [0, 28, 32]) := by
    decide +kernel
  have third : armNode ∈ mol.canonicalChildren (nodeOf [0, 28, 32, 27]) := by decide +kernel
  ((Relation.ReflTransGen.refl.tail first).tail second).tail third

theorem plus_injective (side : Bool) (depth : Nat) (adequate : 13 ≤ depth) :
    Function.Injective (rawStateKeys certified single_bonded (gen armNode depth side 28)
      armData.target armData.real armUnit rfl) :=
  o_injective 28 (Or.inl rfl) armNode armData plus_descends (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ slot34 slot35 slot_atoms.1 slot_atoms.2
    (arm_prior_separate_side side depth adequate)

theorem minus_injective (side : Bool) (depth : Nat) (adequate : 13 ≤ depth) :
    Function.Injective (rawStateKeys certified single_bonded (gen twinNode depth side 29)
      twinData.target twinData.real twinUnit rfl) :=
  o_injective 29 (Or.inr (Or.inl rfl)) twinNode twinData twin_descends (by decide +kernel)
    (by decide +kernel) (by decide +kernel) _ twinSlot34 twinSlot35 twin_slot_atoms.1 twin_slot_atoms.2
    (twin_prior_separate side depth adequate)

/-! ## The classification applied to actual occurrences -/

private theorem center_values (c : physical.Center) :
    c.1.val = 0 ∨ c.1.val = 2 ∨ c.1.val = 3 ∨ c.1.val = 4 ∨ c.1.val = 26 := by
  obtain ⟨a, member⟩ := c
  change a ∈ graph.tetrahedralCenterSet at member
  rw [detected_inventory] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem center_atoms (a : Fin 46) (allowed : RootMark a) (c : physical.Center)
    (node : RawMolecule.CanonicalBranchNode) (path : Descends mol (nodeOf [0, a.val]) node)
    (real : node.forcedLeaf = false) (current : node.atom = c.1.val) :
    node.atom = 2 ∨ node.atom = 3 ∨ node.atom = 4 ∨ node.atom = 26 := by
  have values := center_values c
  rw [← current] at values
  rcases values with zero | rest
  · exfalso
    rcases path.cases_tail with same | ⟨parent, before, edge⟩
    · have atomEq : node.atom = a.val := by rw [same]; rfl
      rw [atomEq] at zero
      rcases allowed with rfl | rfl | rfl | rfl <;> cases zero
    · have fresh := (LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol parent node edge).2.1 real
      obtain ⟨rest, same⟩ := descends_history a.val parent before
      apply fresh
      rw [zero, same]
      simp
  · exact rest

theorem tie_classified (a : Fin 46) (allowed : RootMark a) (c : physical.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData certified mol c node)
    (path : Descends mol (nodeOf [0, a.val]) node) (real : node.forcedLeaf = false)
    (current : node.atom = c.1.val) (state : OccurrenceAuxState) (left right : Fin 4)
    (different : left ≠ right)
    (tie : rawStateKeys certified single_bonded state data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl left =
      rawStateKeys certified single_bonded state data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl right) :
    RhoOccurrence node ∨ node = armNode ∨ node = twinNode := by
  have atoms := center_atoms a allowed c node path real current
  have notStart : node.atom ≠ a.val := by
    intro same
    rcases allowed with rfl | rfl | rfl | rfl <;>
      rcases atoms with h | h | h | h <;> rw [same] at h <;> cases h
  obtain ⟨e, fixed, fixedArm, entry⟩ := tie_symmetry a allowed c node data path notStart state
    left right different tie
  let g : graph.Aut := ⟨e.val, e.2.1⟩
  have fixedRaw : ∀ value ∈ node.history, ∀ h : value < 46, g.val ⟨value, h⟩ = ⟨value, h⟩ :=
    fun value member h => fixed ⟨value, h⟩ (history_of_data c node data ⟨value, h⟩ member)
  have zeroMember : (0 : Nat) ∈ node.history := by
    obtain ⟨rest, same⟩ := descends_history a.val node path
    rw [same]
    simp
  have f0 : g.val (0 : Fin 46) = (0 : Fin 46) := fixedRaw 0 zeroMember (by decide)
  have fixedMark : ∀ h : a.val < 46, g.val ⟨a.val, h⟩ = ⟨a.val, h⟩ := fun _ => fixedArm
  have moves : MovesNeighbor g.val node := by
    refine ⟨atoms, c.1, current.symm, referenceAt certified mol c node data left,
      physical.ligandAtomAt_adj c (data.ligandOf left), ?_⟩
    intro same
    have values : referenceAt certified mol c node data right =
        referenceAt certified mol c node data left := entry.symm.trans same
    exact different (referenceAt_injective c node data values.symm)
  rcases allowed with rfl | rfl | rfl | rfl
  · exact o16_arm_classification 28 (Or.inl rfl) g f0 fixedMark node path real fixedRaw moves
  · exact o16_arm_classification 29 (Or.inr rfl) g f0 fixedMark node path real fixedRaw moves
  · exact Or.inl (o18_arm_classification 30 (Or.inl rfl) g f0 fixedMark node path real fixedRaw moves)
  · exact Or.inl (o18_arm_classification 31 (Or.inr rfl) g f0 fixedMark node path real fixedRaw moves)

/-! ## Rotation-fixed occurrences refuse every root mark -/

private theorem relabel_rho (value : Nat) (fixed : fixesNat rho value = true) :
    relabelOf certified rhoAut.val value = value := by
  by_cases bound : value < 46
  · have direct := relabelOf_val certified rhoAut.val (⟨value, bound⟩ : Fin 46)
    have same : rho ⟨value, bound⟩ = ⟨value, bound⟩ := by
      unfold fixesNat at fixed
      rw [dif_pos bound] at fixed
      exact of_decide_eq_true fixed
    change relabelOf certified rhoAut.val value = (rho ⟨value, bound⟩).val at direct
    rw [same] at direct
    exact direct
  · exact LocalizedChemicalRingPhysicalSense.relabelOf_outside certified _ _ (Nat.le_of_not_lt bound)

private theorem rho_marks (m : Fin 46) (allowed : RootMark m) : rhoAut.val m = m := by
  rcases allowed with rfl | rfl | rfl | rfl <;> rfl

private theorem rho_reading_none (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (real : node.provenance = .realAtom) (current : node.atom = c.1.val)
    (occurrence : RhoOccurrence node) (depth : Nat) (side : Bool) (m : Fin 46) (allowed : RootMark m) :
    reading node depth side m.val = none := by
  have frame := detected_frame mol certified structure_agreement admissible supported single_bonded
    c node reached real current
  have moved : ∃ atom ∈ LocalizedGenericMarkedRecalculation.frameAtomsOf
      (occurrenceLigandCursors mol node),
      relabelOf certified rhoAut.val atom ≠ atom := by
    have rawSingle := raw_single mol certified structure_agreement admissible.1.1 admissible.1.2
      supported single_bonded
    have degree := LocalizedMarkedDetectedFrames.detected_raw_degree mol certified structure_agreement
      admissible.1.1 admissible.1.2 supported c
    rw [← current] at degree
    have perm : (LocalizedGenericMarkedRecalculation.frameAtomsOf
        (occurrenceLigandCursors mol node)).Perm
        (mol.canonicalIncidentNeighbors node.atom) := by
      rcases frame_atoms_perm_neighbors mol admissible.1.1 rawSingle node reached _ frame with
        ⟨_, perm⟩ | ⟨three, _⟩
      · exact perm
      · rw [degree] at three
        cases three
    have pick (x : Fin 46) (present : x.val ∈ mol.canonicalIncidentNeighbors node.atom)
        (moved : rho x ≠ x) : ∃ atom ∈ LocalizedGenericMarkedRecalculation.frameAtomsOf
        (occurrenceLigandCursors mol node),
        relabelOf certified rhoAut.val atom ≠ atom := by
      refine ⟨x.val, perm.mem_iff.mpr present, ?_⟩
      rw [relabelOf_val]
      exact fun same => moved (Fin.ext same)
    rcases occurrence.2 with h | h | h
    · exact pick 5 (by rw [h]; decide +kernel) (by decide)
    · exact pick 14 (by rw [h]; decide +kernel) (by decide)
    · exact pick 15 (by rw [h]; decide +kernel) (by decide)
  exact LocalizedChemicalRingInheritedFixedReferenceRefusal.inheritedReading_none certified mol
    structure_agreement admissible supported single_bonded cfg rhoAut all_calibrated
    (rho_relativeSign cfg) c node reached real current
    (fun value member => relabel_rho value (occurrence.1 value member)) m (rho_marks m allowed)
    moved depth side

/-! ## Local reference independence -/

private theorem reading_eq_of_injective (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node) (depth : Nat) (side : Bool)
    (common : ∀ r r' : Fin 46, RootMark r → RootMark r' →
      gen node depth side r.val = gen node depth side r'.val)
    (base : Fin 46) (baseMark : RootMark base)
    (injective : Function.Injective (rawStateKeys certified single_bonded (gen node depth side base.val)
      data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl))
    (r r' : Fin 46) (hr : RootMark r) (hr' : RootMark r') :
    reading node depth side r.val = reading node depth side r'.val := by
  have atR : Function.Injective (rawStateKeys certified single_bonded (gen node depth side r.val)
      data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl) := by
    rw [common r base hr baseMark]
    exact injective
  have atR' : Function.Injective (rawStateKeys certified single_bonded (gen node depth side r'.val)
      data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl) := by
    rw [common r' base hr' baseMark]
    exact injective
  rw [reading_of_prior_injective c node data depth side r atR,
    reading_of_prior_injective c node data depth side r' atR', common r r' hr hr']

private theorem provenance_real (node : RawMolecule.CanonicalBranchNode)
    (real : node.forcedLeaf = false) : node.provenance = .realAtom := by
  unfold RawMolecule.CanonicalBranchNode.forcedLeaf at real
  cases h : node.provenance <;> simp_all

/-- One occurrence: all four root-mark readings agree, given reference-independent child facts. -/
theorem arm_reading_eq (a : Fin 46) (allowed : RootMark a) (node : RawMolecule.CanonicalBranchNode)
    (path : Descends mol (nodeOf [0, a.val]) node) (side : Bool) (depth : Nat)
    (bound : 18 ≤ node.history.length + depth)
    (common : ∀ r r' : Fin 46, RootMark r → RootMark r' →
      gen node depth side r.val = gen node depth side r'.val)
    (r r' : Fin 46) (hr : RootMark r) (hr' : RootMark r') :
    reading node depth side r.val = reading node depth side r'.val := by
  cases leaf : node.forcedLeaf with
  | true =>
      have noFrame := frameAtoms?_forcedLeaf mol node leaf
      rw [reading_none_of_frame_none node depth side _ noFrame,
        reading_none_of_frame_none node depth side _ noFrame]
  | false =>
      have real := provenance_real node leaf
      have armReached : Reached mol (nodeOf [0, a.val]) := by
        refine reached_child mol (canonicalCenterRoot 0) _ (reached_root mol 0 (by decide)) ?_
        rcases allowed with rfl | rfl | rfl | rfl <;> decide +kernel
      have reached := descendant_reached armReached path
      cases frame : frameAtoms? mol node with
      | none =>
          rw [reading_none_of_frame_none node depth side _ frame,
            reading_none_of_frame_none node depth side _ frame]
      | some atoms =>
          have rawSingle := raw_single mol certified structure_agreement admissible.1.1
            admissible.1.2 supported single_bonded
          rcases frame_atoms_perm_neighbors mol admissible.1.1 rawSingle node reached atoms frame with
            ⟨four, _⟩ | ⟨three, perm⟩
          · have valid := reached_atom_valid mol admissible.1.1 node reached
            let c : physical.Center :=
              ⟨atomOf mol certified structure_agreement node.atom valid,
                center_of_degree mol certified structure_agreement admissible.1.1 admissible.1.2
                  supported node.atom valid four⟩
            have current : node.atom = c.1.val := rfl
            by_cases plus : node = armNode
            · subst plus
              have adequate : 13 ≤ depth := by
                have length : armNode.history.length = 5 := by decide +kernel
                omega
              exact reading_eq_of_injective otherCurrent armNode armData depth side common 28
                (Or.inl rfl) (plus_injective side depth adequate) r r' hr hr'
            by_cases minus : node = twinNode
            · subst minus
              have adequate : 13 ≤ depth := by
                have length : twinNode.history.length = 5 := by decide +kernel
                omega
              exact reading_eq_of_injective otherCurrent twinNode twinData depth side common 29
                (Or.inr (Or.inl rfl)) (minus_injective side depth adequate) r r' hr hr'
            obtain ⟨data⟩ := occurrenceData_exists certified mol structure_agreement admissible
              supported single_bonded c node reached real current
            by_cases injective : Function.Injective (rawStateKeys certified single_bonded
                (gen node depth side r.val) data.target data.real
                ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl)
            · exact reading_eq_of_injective c node data depth side common r hr injective r r' hr hr'
            · obtain ⟨left, right, tie, different⟩ := Function.not_injective_iff.mp injective
              rcases tie_classified a allowed c node data path leaf current _ left right different tie with
                occurrence | same | same
              · rw [rho_reading_none c node reached real current occurrence depth side r hr,
                  rho_reading_none c node reached real current occurrence depth side r' hr']
              · exact absurd same plus
              · exact absurd same minus
          · rw [reading_none_of_three node depth side _ atoms frame three perm,
              reading_none_of_three node depth side _ atoms frame three perm]

/-! ## The whole arm forest -/

private theorem mirror_observed (side : Bool) :
    mirror (observedGeometry certified side) = observedGeometry certified (!side) := by
  cases side with
  | false => rfl
  | true => exact mirror_mirror _

/-- Reference independence of the actual fact lists throughout the root-arm forest. -/
theorem arm_facts_independent :
    ∀ (depth : Nat) (node : RawMolecule.CanonicalBranchNode) (a : Fin 46), RootMark a →
      Descends mol (nodeOf [0, a.val]) node → 19 ≤ node.history.length + depth →
      ∀ (side : Bool) (r r' : Fin 46), RootMark r → RootMark r' →
        factsWith LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
            depth (observedGeometry certified side) [] (some r.val) node =
          factsWith LocalizedChemicalRingInheritedFallback.rawStep? mol (sparseOperations certified mol)
            depth (observedGeometry certified side) [] (some r'.val) node := by
  intro depth
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro node a allowed path bound side r r' hr hr'
      have common (s : Bool) (x y : Fin 46) (hx : RootMark x) (hy : RootMark y) :
          gen node depth s x.val = gen node depth s y.val := by
        unfold gen generated underWith
        apply flatMap_congr_mem
        intro child member
        have edge := mem_tiedChildren_actual mol (sparseOperations certified mol) [] node child member
        have growth := congrArg List.length (mol.canonicalChildren_history node child edge)
        simp only [List.length_cons] at growth
        exact ih child a allowed (path.tail edge) (by omega) s x y hx hy
      have bound' : 18 ≤ node.history.length + depth := by omega
      have descriptor := LocalizedChemicalRingContextIndependence.descriptor_eq_of_reads_eq mol
        (sparseOperations certified mol) depth (observedGeometry certified side) [] node r.val r'.val
        (by
          intro g choice
          rcases choice with rfl | rfl
          · exact arm_reading_eq a allowed node path side depth bound' (common side) r r' hr hr'
          · rw [mirror_observed]
            exact arm_reading_eq a allowed node path (!side) depth bound' (common (!side)) r r' hr hr')
      rw [factsWith_succ, factsWith_succ]
      change (LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
          depth (observedGeometry certified side) [] (some r.val) node).toList.map _ ++ _ =
        (LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
          depth (observedGeometry certified side) [] (some r'.val) node).toList.map _ ++ _
      rw [descriptor]
      congr 1
      apply flatMap_congr_mem
      intro child edge
      have growth := congrArg List.length (mol.canonicalChildren_history node child edge)
      simp only [List.length_cons] at growth
      exact ih child a allowed (path.tail edge) (by omega) side r r' hr hr'

/-- Reference independence of the actual descriptor at one occurrence of the arm forest. -/
theorem arm_descriptor_independent (depth : Nat) (node : RawMolecule.CanonicalBranchNode) (a : Fin 46)
    (allowed : RootMark a) (path : Descends mol (nodeOf [0, a.val]) node)
    (bound : 18 ≤ node.history.length + depth) (side : Bool) (r r' : Fin 46)
    (hr : RootMark r) (hr' : RootMark r') :
    LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol) depth
        (observedGeometry certified side) [] (some r.val) node =
      LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol) depth
        (observedGeometry certified side) [] (some r'.val) node := by
  have common (s : Bool) (x y : Fin 46) (hx : RootMark x) (hy : RootMark y) :
      gen node depth s x.val = gen node depth s y.val := by
    unfold gen generated underWith
    apply flatMap_congr_mem
    intro child member
    have edge := mem_tiedChildren_actual mol (sparseOperations certified mol) [] node child member
    have growth := congrArg List.length (mol.canonicalChildren_history node child edge)
    simp only [List.length_cons] at growth
    exact arm_facts_independent depth child a allowed (path.tail edge) (by omega) s x y hx hy
  apply LocalizedChemicalRingContextIndependence.descriptor_eq_of_reads_eq
  intro g choice
  rcases choice with rfl | rfl
  · exact arm_reading_eq a allowed node path side depth bound (common side) r r' hr hr'
  · rw [mirror_observed]
    exact arm_reading_eq a allowed node path (!side) depth bound (common (!side)) r r' hr hr'

private theorem root_children :
    mol.canonicalChildren (canonicalCenterRoot 0) =
      [nodeOf [0, 28], nodeOf [0, 29], nodeOf [0, 30], nodeOf [0, 31]] := by
  decide +kernel

/-- **All four root references generate the same actual state**, on each geometry side. -/
theorem generated_independent (side : Bool) (r r' : Fin 46) (hr : RootMark r) (hr' : RootMark r') :
    gen (canonicalCenterRoot 0) (structuralDepth mol (canonicalCenterRoot 0)) side r.val =
      gen (canonicalCenterRoot 0) (structuralDepth mol (canonicalCenterRoot 0)) side r'.val := by
  unfold gen generated underWith
  apply flatMap_congr_mem
  intro child member
  have edge := mem_tiedChildren_actual mol (sparseOperations certified mol) [] _ child member
  have bound : 19 ≤ 2 + structuralDepth mol (canonicalCenterRoot 0) := by decide +kernel
  rw [root_children] at edge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at edge
  rcases edge with rfl | rfl | rfl | rfl
  · exact arm_facts_independent _ _ 28 (Or.inl rfl) .refl bound side r r' hr hr'
  · exact arm_facts_independent _ _ 29 (Or.inr (Or.inl rfl)) .refl bound side r r' hr hr'
  · exact arm_facts_independent _ _ 30 (Or.inr (Or.inr (Or.inl rfl))) .refl bound side r r' hr hr'
  · exact arm_facts_independent _ _ 31 (Or.inr (Or.inr (Or.inr rfl))) .refl bound side r r' hr hr'

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.referenceAt_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.plus_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.minus_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.arm_reading_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.arm_facts_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.arm_descriptor_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.tie_classified
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusFacts.generated_independent
