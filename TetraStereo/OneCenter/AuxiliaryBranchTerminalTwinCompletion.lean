import TetraStereo.OneCenter.FiniteAuxiliaryBranchTransport
import TetraStereo.OneCenter.TerminalTwinConfigurationGauge
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! History-relative completion of a non-twin sign witness by the accepted terminal-twin gauge.
The full theorem is intentionally parameterized by the two leaf-avoidance facts; an actual
occurrence-path theorem below derives them from real history and outward-slot evidence. -/

namespace TetraStereo.OneCenter.AuxiliaryBranchTerminalTwinCompletion

open FiniteAuxiliaryBranchTransport
open RootedTetrahedralBranchSymmetry
open RetainedCoherentSymmetry
open TerminalTwinConfigurationGauge
open CertifiedLocalizedCIPInput

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (m : MultiCenterMolecule V)


/-- A terminal twin leaf at a residual center cannot occur on an actual simple occurrence path
whose current and original-root endpoints are detected centers. The proof uses the actual simple
walk represented by the carrier occurrence. -/
theorem actualOccurrenceHistory_avoids_residualTwinLeaf
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {current : input.Atom}
    (currentObserved : occurrence.1.node.current? = some current)
    (rootCenter : occurrence.1.root ∈ input.detectedMultiCenterMolecule.centers)
    (currentCenter : current ∈ input.detectedMultiCenterMolecule.centers)
    {d leaf : input.Atom}
    (leafNotCenter : leaf ∉ input.detectedMultiCenterMolecule.centers)
    (leafNeighbors : input.moleculeGraph.neighborFinset leaf = {d})
    (dNotHistory : d ∉ occurrence.1.node.history) :
    leaf ∉ occurrence.1.node.history := by
  have path := input.simpleOccurrencePath_of_carrier_real singleBonded occurrence real
  obtain ⟨walkCurrent, walk, observed, _head, _prov, isPath, supportReverse, _parent⟩ :=
    input.simpleOccurrencePath_realPathNode path
  have currentEq : walkCurrent = current := Option.some.inj (observed.symm.trans currentObserved)
  intro leafHistory
  have leafSupport : leaf ∈ walk.support := by
    have h : leaf ∈ walk.support.reverse := by rw [supportReverse]; exact leafHistory
    exact List.mem_reverse.mp h
  obtain ⟨index, indexGet⟩ := List.mem_iff_get.mp leafSupport
  have indexBound : index.val ≤ walk.length := by
    have hlen := walk.length_support
    have h := index.isLt
    omega
  have getLeaf : walk.getVert index.val = leaf := by
    rw [walk.getVert_eq_support_getElem indexBound]
    simpa using indexGet
  have startNe : index.val ≠ 0 := by
    intro hi
    have eq : occurrence.1.root = leaf := by
      calc
        occurrence.1.root = walk.getVert 0 := by simp
        _ = walk.getVert index.val := by rw [hi]
        _ = leaf := getLeaf
    exact leafNotCenter (by simpa [eq] using rootCenter)
  have endNe : index.val ≠ walk.length := by
    intro hi
    have eq : current = leaf := by
      calc
        current = walkCurrent := currentEq.symm
        _ = walk.getVert walk.length := by simp
        _ = walk.getVert index.val := by rw [hi]
        _ = leaf := getLeaf
    exact leafNotCenter (by simpa [eq] using currentCenter)
  have indexLt : index.val < walk.length := by omega
  have nextAdjSimple :
      input.moleculeGraph.underlyingSimpleGraph.Adj (walk.getVert index.val)
        (walk.getVert (index.val + 1)) := by
    exact walk.adj_getVert_succ indexLt
  have nextAdj : input.moleculeGraph.Adj leaf (walk.getVert (index.val + 1)) := by
    apply (MoleculeGraph.underlyingSimpleGraph_adj input.moleculeGraph leaf _).mp
    simpa [getLeaf] using nextAdjSimple
  have nextMem : walk.getVert (index.val + 1) ∈ input.moleculeGraph.neighborFinset leaf :=
    (MoleculeGraph.mem_neighborFinset input.moleculeGraph leaf _).mpr nextAdj
  rw [leafNeighbors] at nextMem
  have nextEq : walk.getVert (index.val + 1) = d := Finset.mem_singleton.mp nextMem
  have nextInHistory : walk.getVert (index.val + 1) ∈ occurrence.1.node.history := by
    rw [← supportReverse]
    exact List.mem_reverse.mpr (walk.getVert_mem_support _)
  exact dNotHistory (nextEq ▸ nextInHistory)

/-- Actual occurrence hypotheses give the two avoidance obligations used by the history-relative
gauge. The retained history is endpoint-calibrated by detected center membership; each residual
center lies outside the history. -/
theorem actualOccurrence_terminalTwinLeafAvoidance
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {current source : input.Atom}
    (currentObserved : occurrence.1.node.current? = some current)
    (currentMember : current ∈ occurrence.1.node.history)
    (rootCenter : occurrence.1.root ∈ input.detectedMultiCenterMolecule.centers)
    (currentCenter : current ∈ input.detectedMultiCenterMolecule.centers)
    (sourceAdjacent : input.moleculeGraph.Adj current source) :
    (∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph occurrence.1.node.history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair
        input.detectedMultiCenterMolecule d a b → a ∉ occurrence.1.node.history ∧
          b ∉ occurrence.1.node.history) ∧
    (∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph occurrence.1.node.history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair
        input.detectedMultiCenterMolecule d a b → source ≠ a ∧ source ≠ b) := by
  constructor
  · intro d hd a b pair
    have dNotHistory := RetainedCoherentSymmetry.inComponent_not_mem
      input.moleculeGraph hd
    exact ⟨actualOccurrenceHistory_avoids_residualTwinLeaf input singleBonded occurrence real
      currentObserved rootCenter currentCenter pair.leaf_not_mem_centers_a pair.neighbor_a
      dNotHistory,
      actualOccurrenceHistory_avoids_residualTwinLeaf input singleBonded occurrence real
      currentObserved rootCenter currentCenter pair.leaf_not_mem_centers_b pair.neighbor_b
      dNotHistory⟩
  · intro d hd a b pair
    have dNotHistory := RetainedCoherentSymmetry.inComponent_not_mem
      input.moleculeGraph hd
    have neighA : input.moleculeGraph.neighborFinset a = {d.1} := pair.neighbor_a
    have neighB : input.moleculeGraph.neighborFinset b = {d.1} := pair.neighbor_b
    constructor
    · intro sourceEq
      have adj : input.moleculeGraph.Adj current a := by simpa [sourceEq] using sourceAdjacent
      have hmem : current ∈ input.moleculeGraph.neighborFinset a :=
        (MoleculeGraph.mem_neighborFinset input.moleculeGraph a current).mpr
          (input.moleculeGraph.adj_symm.mp adj)
      rw [neighA] at hmem
      have hcurrent : current = d.1 := Finset.mem_singleton.mp hmem
      exact dNotHistory (hcurrent ▸ currentMember)
    · intro sourceEq
      have adj : input.moleculeGraph.Adj current b := by simpa [sourceEq] using sourceAdjacent
      have hmem : current ∈ input.moleculeGraph.neighborFinset b :=
        (MoleculeGraph.mem_neighborFinset input.moleculeGraph b current).mpr
          (input.moleculeGraph.adj_symm.mp adj)
      rw [neighB] at hmem
      have hcurrent : current = d.1 := Finset.mem_singleton.mp hmem
      exact dNotHistory (hcurrent ▸ currentMember)

/-- The same whole-map witness with sign constraints only at residual centers lacking physical
terminal twins. -/
def AuxiliaryNonTwinComponentTransport (cfg : m.Configuration) (history : List V)
    (source target : V) (mirror : Bool) : Prop :=
  ∃ E : m.Aut,
    (∀ x ∈ history, (E : Equiv.Perm V) x = x) ∧
    (E : Equiv.Perm V) source = target ∧
    ∀ d : m.Center, InComponent m.mol history source d.1 →
      ¬ RootedBranchTerminalTwinCompletion.HasTerminalTwins m d →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt E d) =
        physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm E d)

private theorem pm_one_mul {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

private theorem mirrorFactor_pm_one (mirror : Bool) :
    physicalMirrorFactor mirror = 1 ∨ physicalMirrorFactor mirror = -1 := by
  cases mirror <;> simp [CertifiedLocalizedCIPInput.physicalMirrorFactor]

private theorem eq_neg_of_ne_of_pm_one {x z : ℝ} (hx : x = 1 ∨ x = -1)
    (hz : z = 1 ∨ z = -1) (hne : x ≠ z) : x = -z := by
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
  · exact False.elim (hne rfl)
  · norm_num
  · norm_num
  · exact False.elim (hne rfl)

private theorem familyAut_apply_eq_self_of_avoids
    {ι : Type*} {idx : ι → m.Center} {A B : ι → V}
    (fam : TerminalTwinFamily m idx A B) (l : List ι) (x : V)
    (avoids : ∀ i ∈ l, x ≠ A i ∧ x ≠ B i) :
    ((fam.familyAut l : m.Aut) : Equiv.Perm V) x = x := by
  induction l with
  | nil => simp [TerminalTwinFamily.familyAut]
  | cons i rest ih =>
      have hi := avoids i (by simp)
      have hrest : ∀ j ∈ rest, x ≠ A j ∧ x ≠ B j := fun j hj => avoids j (by simp [hj])
      have hcons : fam.familyAut (i :: rest) =
          (fam.twin i).swapAut * fam.familyAut rest := rfl
      change ((fam.familyAut (i :: rest) : m.Aut) : Equiv.Perm V) x = x
      rw [hcons]
      change Equiv.swap (A i) (B i) (((fam.familyAut rest : m.Aut) : Equiv.Perm V) x) = x
      rw [ih hrest]
      exact Equiv.swap_apply_of_ne_of_ne hi.1 hi.2

/-- **History-relative terminal-twin completion.** If all history atoms and the query source
avoid every selected terminal leaf, a whole-map witness satisfying the law at every non-twin
residual center can be corrected to satisfy the full `AuxiliaryComponentTransport` law. -/
theorem auxiliaryComponentTransport_iff_nonTwin
    (cfg : m.Configuration) (history : List V) (source target : V) (mirror : Bool)
    (historyLeafAvoid : ∀ d : m.Center, InComponent m.mol history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair m d a b → a ∉ history ∧ b ∉ history)
    (sourceLeafAvoid : ∀ d : m.Center, InComponent m.mol history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair m d a b → source ≠ a ∧ source ≠ b) :
    AuxiliaryComponentTransport m cfg history source target mirror ↔
      AuxiliaryNonTwinComponentTransport m cfg history source target mirror := by
  classical
  constructor
  · rintro ⟨E, hfixed, hsent, hlaw⟩
    exact ⟨E, hfixed, hsent, fun d hd _ => hlaw d hd⟩
  · rintro ⟨e, hfixed, hsent, hred⟩
    let Bad : m.Center → Prop := fun d => InComponent m.mol history source d.1 ∧
      ¬ (m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm e d))
    have hbadTwin : ∀ d, Bad d → RootedBranchTerminalTwinCompletion.HasTerminalTwins m d := by
      intro d hd
      by_contra hnot
      exact hd.2 (hred d hd.1 hnot)
    let ι := {d : m.Center // Bad d}
    let idx : ι → m.Center := fun q => q.1
    have idxInj : Function.Injective idx := fun _ _ h => Subtype.ext h
    let A : ι → V := fun q => Classical.choose (hbadTwin q.1 q.2)
    let B : ι → V := fun q => Classical.choose (Classical.choose_spec (hbadTwin q.1 q.2))
    have pair : ∀ q : ι, TerminalTwinConfigurationGauge.TerminalTwinPair m (idx q) (A q) (B q) := fun q =>
      Classical.choose_spec (Classical.choose_spec (hbadTwin q.1 q.2))
    let fam : TerminalTwinFamily m idx A B := ⟨pair, idxInj⟩
    let l : List ι := (Finset.univ : Finset ι).toList
    have lNodup : l.Nodup := by exact Finset.nodup_toList _
    let g : m.Aut := fam.familyAut l
    have gCenters : ∀ d : m.Center, m.centerPerm g d = d :=
      fun d => fam.centerPerm_familyAut_apply l d
    have gHistory : ∀ x ∈ history, (g : Equiv.Perm V) x = x := by
      intro x hx
      apply familyAut_apply_eq_self_of_avoids m fam l x
      intro q hq
      have qBad : Bad q.1 := q.2
      have leaves := historyLeafAvoid q.1 qBad.1 (A q) (B q) (pair q)
      exact ⟨fun h => leaves.1 (h ▸ hx), fun h => leaves.2 (h ▸ hx)⟩
    have gSource : (g : Equiv.Perm V) source = source := by
      apply familyAut_apply_eq_self_of_avoids m fam l source
      intro q hq
      have leaves := sourceLeafAvoid q.1 q.2.1 (A q) (B q) (pair q)
      exact ⟨leaves.1, leaves.2⟩
    have listNotMem : ∀ d : m.Center, ¬ Bad d → d ∉ l.map idx := by
      intro d hbad hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨q, _, hq⟩
      exact hbad (hq ▸ q.2)
    have listMem : ∀ d : m.Center, (hd : Bad d) → d ∈ l.map idx := by
      intro d hd
      exact List.mem_map.mpr ⟨⟨d, hd⟩, by simp [l], rfl⟩
    refine ⟨e * g, ?_, ?_, ?_⟩
    · intro x hx
      simpa [Equiv.Perm.mul_apply, gHistory x hx] using hfixed x hx
    · simpa [Equiv.Perm.mul_apply, gSource] using hsent
    · intro d hd
      by_cases heq : m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
          physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm e d)
      · have hnot : ¬ Bad d := fun hb => hb.2 heq
        have gLocal := fam.ligandPermAt_familyAut_of_not_mem l d (listNotMem d hnot)
        rw [m.ligandPermAt_mul, RootedTetrahedralBranchSymmetry.centerPerm_mul_apply,
          gCenters d, gLocal]
        simpa using heq
      · have hbad : Bad d := ⟨hd, heq⟩
        let q : ι := ⟨d, hbad⟩
        have hq : q ∈ l := by simp [l]
        have gLocal : m.ligandPermAt g d =
            Equiv.swap (fam.twin q).twinSlotA (fam.twin q).twinSlotB := by
          simpa [g, idx] using fam.ligandPermAt_familyAut_at_index l lNodup q hq
        have gOdd : permHandedness (m.ligandPermAt g d) = -1 := by
          rw [gLocal]
          exact TerminalTwinPair.permHandedness_swap_of_ne
            (fam.twin q).twinSlotA_ne_twinSlotB
        rw [m.ligandPermAt_mul, RootedTetrahedralBranchSymmetry.centerPerm_mul_apply,
          gCenters d, permHandedness_mul, gOdd]
        have lhsPM : m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) = 1 ∨
            m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) = -1 :=
          pm_one_mul (permHandedness_eq_one_or_eq_neg_one (cfg d))
            (permHandedness_eq_one_or_eq_neg_one (m.ligandPermAt e d))
        have rhsPM : physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm e d) = 1 ∨
            physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm e d) = -1 :=
          pm_one_mul (mirrorFactor_pm_one mirror)
            (permHandedness_eq_one_or_eq_neg_one (cfg (m.centerPerm e d)))
        have hneg := eq_neg_of_ne_of_pm_one lhsPM rhsPM heq
        calc m.configurationSign cfg d * (permHandedness (m.ligandPermAt e d) * -1)
            = -(m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)) := by ring
          _ = -( -(physicalMirrorFactor mirror *
              m.configurationSign cfg (m.centerPerm e d))) := by rw [hneg]
          _ = physicalMirrorFactor mirror *
              m.configurationSign cfg (m.centerPerm e d) := by ring

end TetraStereo.OneCenter.AuxiliaryBranchTerminalTwinCompletion

assert_kernel_only TetraStereo.OneCenter.AuxiliaryBranchTerminalTwinCompletion.AuxiliaryNonTwinComponentTransport
assert_kernel_only TetraStereo.OneCenter.AuxiliaryBranchTerminalTwinCompletion.actualOccurrenceHistory_avoids_residualTwinLeaf
assert_kernel_only TetraStereo.OneCenter.AuxiliaryBranchTerminalTwinCompletion.actualOccurrence_terminalTwinLeafAvoidance
assert_kernel_only TetraStereo.OneCenter.AuxiliaryBranchTerminalTwinCompletion.auxiliaryComponentTransport_iff_nonTwin
