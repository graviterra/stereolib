import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion
import TetraStereo.OneCenter.LocalizedRetainedSourceCutFrames
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# The root comparator's observation record cannot determine the physical root classification

The accepted 15-atom cage graph `C(H)(Cl)(X_A)(X_B)` of
`LocalizedRecursiveAuxiliaryPhysicalCompletion` is given **two** spatial tables that differ in one
coordinate only: the hydrogen of cage B points into the cage (`P10`, the accepted hidden-parity
input) or out of it (`P10out`, both cages out/out).

**The record.** `RootObservation` collects, indexed by the sorted-neighbour slot of each root
ligand atom, exactly what the evaluator's root comparator and geometric reader consult:

* `lt`: the strict through-Rule-5 order of the four actual retained ligand keys
  (`observation_lt_comparator`: it *is* the actual compound comparator's `lt` output);
* `priorTie`: the Rules-1–4c prior-key tie relation, the Rule-5 pair-count input
  (`observation_priorTie_comparator`: the actual prior comparator's `eq` output);
* `coordinate`: the certified position of each root ligand.

`observationWith P len` is built from the actual compiled frame of the family member with spatial
table `P`. `rootOutcome_factors` proves that the evaluator's root outcome is a function of this
record on the whole family, and `rootOutcome_of_observation` is the underlying determination
theorem. Nothing coarser (refusal flags, counts) is substituted for the record.

**Cross-input equality.** `observation_eq_of_rootGeometry` proves that two nondegenerate family
members with the same root ligand positions have *equal* records. The comparison tables are shown
equal to the comparison tables of input-independent keys: the four source predecessor cuts of the
root are pure graph data (`canonicalSlotCut`), every auxiliary read inside them is `none` on every
nondegenerate table (`reached_refusedWith`), and the retained comparison is window independent.

**The separation.** `hiddenParity_observationSeparation` joins the equal records of the two
tables with their different formal physical classifications: the hidden-parity table has pairwise
properly distinguishable root branches, the out/out table admits an explicit proper transport of
one cage arm onto the other (`oddArmPerm`). `no_observation_function_decides_distinguishability`
is the resulting no-function theorem: no function of the record decides pairwise proper
distinguishability on the family. Physical statements are about the formal calibrated domain
(`RecursiveAuxiliaryPhysicalDomain`); no equilibrium realizability is claimed.

The section `Family` proves the refusal facts for **every** spatial table of length 15 whose five
ligand tetrahedra are nondegenerate; the refusals never consult the geometry because every reached
occurrence carries a reader-free history refusal witness valid for every configuration.

The section `Correlation` records the promotion-indexed orientation datum that survives refusal:
for every ordering `ρ` of the three bridge slots, the product of the two promoted readings at the
attachment and far bridgeheads of one cage equals `-(s(C1)·s(C3))`, independent of `ρ` and
reflection invariant. This is a *candidate* datum, stated on the physical configuration; it is not
connected here to the evaluator's actual Rule-6 promoted readings, and no priority rule is asserted.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.CartesianPoint3
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion

/-! ## Walk closure in the root-deleted graph -/

/-- A walk avoiding `r` stays inside any vertex class closed under adjacency away from `r`. -/
theorem walk_closed {V : Type*} (G : SimpleGraph V) (S : V → Prop) (r : V)
    (closed : ∀ a b, S a → a ≠ r → b ≠ r → G.Adj a b → S b)
    {u v : V} (p : G.Walk u v) (avoid : r ∉ p.support) (start : S u) : S v := by
  revert avoid start
  induction p with
  | nil =>
      intro _ start
      exact start
  | @cons u w v edge rest ih =>
      intro avoid start
      rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at avoid
      have next : w ≠ r := by
        intro h
        apply avoid.2
        rw [← h]
        exact rest.start_mem_support
      exact ih avoid.2 (closed u w start (Ne.symm avoid.1) next edge)

noncomputable section

open LocalizedRecursiveAuxiliaryPhysicalDomain LocalizedCyclicRootPhysicalSetup
open LocalizedRecursiveAuxiliaryPhysicalInverse
open LocalizedRuleMajorReference DeclarativeCIP
open LocalizedRecursiveAuxiliaryPhysicalTransport LocalizedRecursiveAuxiliaryPhysicalCorrectness
open LocalizedCyclicMatchedReadingPhysicalTransport
open LocalizedRetainedSourceCutFrames LocalizedRecursiveAuxiliarySourceWindows
open LocalizedCyclicPhysicalStageTransport LocalizedCyclicRootArmReachability
open LocalizedRetainedDescriptorTransport
open DeclarativeCIP.RetainedOccurrenceCarrier DeclarativeCIP.RetainedCutAutomorphism
open scoped Classical

/-! ## The root comparator-visible record: input-independent carrier data -/

/-- The root's detected unit: atom `0` with the empty path. Every family member compiles its
final root occurrence at this unit. -/
def rootUnit : DetectedOccurrence graph :=
  ⟨⟨(0 : Fin 15), []⟩, tetrahedralCenter_isDetected cageCertified cageRoot⟩

/-- Carrier node of the root's own occurrence. -/
def rootCarrier : CarrierNode (Fin 15) := CarrierNode.real [0]

/-- Carrier node of the canonical ligand-root occurrence of sorted-neighbour slot `k`. -/
def ligandCarrier (k : Fin 4) : CarrierNode (Fin 15) :=
  CarrierNode.real [0, cageCanon.ligandAtomAt k0 k]

/-- The source predecessor cut of canonical root slot `k`: a rooted digraph determined by the
molecular graph alone. -/
def canonicalSlotCut (k : Fin 4) : RootedDigraph (Fin 15) :=
  sourceCutArm graph 0 (ligandCarrier k) rootCarrier

/-- Retained complete key of a canonical slot cut under a refusing auxiliary reader, at a
window. -/
def refusedSlotKey (W D : ℕ) (k : Fin 4) : CompleteLigandRule5Key :=
  retainedCompleteLigandRule5KeyAt graph (fun _ => none) rootUnit (canonicalSlotCut k) W D

/-- The native window of the four canonical slot cuts. -/
abbrev nativeW : ℕ := familyWidth canonicalSlotCut
abbrev nativeD : ℕ := familyHeight canonicalSlotCut

/-- **The root observation record.** Indexed by the sorted-neighbour slot `k` of the root ligand
atom (`cageCanon.ligandAtomAt k0 k`): the strict through-Rule-5 order of the actual retained keys,
the prior-key (Rules 1–4c) tie relation that feeds the Rule-5 pair count, and the certified ligand
coordinate. These are exactly the data the complete-root judgment consumes
(`completeRootOutcome_congr_order`). -/
@[ext]
structure RootObservation where
  lt : Fin 4 → Fin 4 → Prop
  priorTie : Fin 4 → Fin 4 → Prop
  coordinate : Fin 4 → Option CartesianPoint3

/-- Window independence of the refused canonical slot keys' order and prior-tie relations. -/
theorem refusedSlotKey_orderAgrees (W D : ℕ)
    (covers : ∀ k, WindowCovers (canonicalSlotCut k) W D) (k l : Fin 4) :
    (refusedSlotKey W D k < refusedSlotKey W D l ↔
        refusedSlotKey nativeW nativeD k < refusedSlotKey nativeW nativeD l) ∧
      ((ofLex (refusedSlotKey W D k)).1 = (ofLex (refusedSlotKey W D l)).1 ↔
        (ofLex (refusedSlotKey nativeW nativeD k)).1 =
          (ofLex (refusedSlotKey nativeW nativeD l)).1) := by
  have h := retainedCompleteLigandRule5KeyAt_orderAgrees_window graph (fun _ => none) rootUnit
    (covers k) (familyWindow_covers canonicalSlotCut k) (covers l)
    (familyWindow_covers canonicalSlotCut l)
  exact ⟨h.1.1, h.2.2⟩

theorem applySpace_false (point : CartesianPoint3) : applySpace false point = point := rfl

theorem labelAdjust_false (descriptor : LocalizedAuxiliaryLabel) :
    labelAdjust false descriptor = descriptor := rfl

theorem optionMap_labelAdjust_false (outcome : Option LocalizedAuxiliaryLabel) :
    outcome.map (labelAdjust false) = outcome := by
  cases outcome <;> rfl

/-! ## Graph-level facts shared by every spatial table -/

/-- Every center reached from the cage-A root slot (atom `3`) without passing through the root
lies in cage A. -/
theorem reach_armA_mem (v : Fin 15) (reached : LigandBranchReaches cageCanon k0 2 v) :
    v ∈ ([3, 4, 5, 6, 7, 8] : List (Fin 15)) := by
  obtain ⟨p, avoid⟩ := reached
  have closed : ∀ a b : Fin 15, a ∈ ([3, 4, 5, 6, 7, 8] : List (Fin 15)) → a ≠ 0 → b ≠ 0 →
      graph.Adj a b → b ∈ ([3, 4, 5, 6, 7, 8] : List (Fin 15)) := by decide
  refine walk_closed cageCanon.mol.underlyingSimpleGraph
    (fun x => x ∈ ([3, 4, 5, 6, 7, 8] : List (Fin 15))) 0 ?_ p avoid ?_
  · intro a b ha ha0 hb0 adjacent
    exact closed a b ha ha0 hb0 adjacent
  · show cageCanon.ligandAtomAt k0 2 ∈ ([3, 4, 5, 6, 7, 8] : List (Fin 15))
    rw [lig0.2.2.1]
    decide

private theorem edge35 : graph.underlyingSimpleGraph.Adj 3 5 :=
  (graph.underlyingSimpleGraph_adj 3 5).mpr (by decide)

private theorem edge58 : graph.underlyingSimpleGraph.Adj 5 8 :=
  (graph.underlyingSimpleGraph_adj 5 8).mpr (by decide)

theorem reach3 : LigandBranchReaches cageCanon k0 2 k3.1 := by
  unfold LigandBranchReaches
  rw [lig0.2.2.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [k0, k3]

theorem reach8 : LigandBranchReaches cageCanon k0 2 k8.1 := by
  unfold LigandBranchReaches
  rw [lig0.2.2.1]
  refine ⟨SimpleGraph.Walk.cons edge35 (SimpleGraph.Walk.cons edge58 SimpleGraph.Walk.nil), ?_⟩
  simp [k0, k8]

private def graphAut (e : cageCanon.Aut) : graph.Aut := ⟨e.val, e.property.1⟩

private theorem autZ (e : cageCanon.Aut) (atom : Fin 15) :
    graph.atomZ (e.val atom) = graph.atomZ atom :=
  MoleculeGraph.Aut.atomZ_eq (m := graph) (graphAut e) atom

/-- A branch transport at the root preserves the ligand atomic number. -/
theorem transportZ {cfg : cageCanon.Configuration} {i j : Fin 4} {mirror : Bool}
    (transport : BranchTransport cageCanon cfg k0 i j mirror) :
    graph.atomZ (cageCanon.ligandAtomAt k0 j) = graph.atomZ (cageCanon.ligandAtomAt k0 i) := by
  obtain ⟨e, fixed, sent, _⟩ := transport
  have action := cageCanon.ligandAtomAt_ligandPermAt (e := e) (c := k0) i
  rw [fixed, sent] at action
  rw [action]
  exact autZ e _

/-- Only the two cage arms share an atomic number at the root. -/
theorem rootZ_tie (i j : Fin 4)
    (tie : graph.atomZ (cageCanon.ligandAtomAt k0 j) = graph.atomZ (cageCanon.ligandAtomAt k0 i)) :
    i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  rw [lig0f] at tie
  revert tie
  revert i j
  decide

/-! ### Parity completion at a coupled pair of reached centers -/

section CoupledPair

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **One sign law suffices at a coupled pair.** Let the centers reached from slot `i` be exactly
`d₁` and `d₃`, and let every root-fixing exchange of slots `i`, `j` carry them to `d₁'`, `d₃'`
with equal frame handedness. An exchange obeying the sign law at `d₁` is a branch transport as
soon as the bridgehead sign products agree. -/
theorem branchTransport_of_coupledPair_sign (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i j : Fin 4) (d₁ d₃ d₁' d₃' : m.Center)
    (inventory : ∀ d : m.Center, LigandBranchReaches m c i d.1 → d = d₁ ∨ d = d₃)
    (coupled : ∀ e : m.Aut, m.centerPerm e c = c → m.ligandPermAt e c i = j →
      m.centerPerm e d₁ = d₁' ∧ m.centerPerm e d₃ = d₃' ∧
        permHandedness (m.ligandPermAt e d₁) = permHandedness (m.ligandPermAt e d₃))
    (e : m.Aut) (fixed : m.centerPerm e c = c) (sent : m.ligandPermAt e c i = j) (mirror : Bool)
    (law₁ : m.configurationSign cfg d₁ * permHandedness (m.ligandPermAt e d₁) =
      (if mirror then -1 else 1) * m.configurationSign cfg d₁')
    (agree : m.configurationSign cfg d₁ * m.configurationSign cfg d₃ =
      m.configurationSign cfg d₁' * m.configurationSign cfg d₃') :
    BranchTransport m cfg c i j mirror := by
  obtain ⟨image₁, image₃, sameHand⟩ := coupled e fixed sent
  refine ⟨e, fixed, sent, ?_⟩
  intro d reached
  rcases inventory d reached with h | h
  · rw [h, image₁]
    exact law₁
  · rw [h, image₃, ← sameHand]
    have sq₁ := permHandedness_mul_self (cfg d₁)
    have sq₁' := permHandedness_mul_self (cfg d₁')
    change permHandedness (cfg d₁) * permHandedness (m.ligandPermAt e d₁) =
      (if mirror then -1 else 1) * permHandedness (cfg d₁') at law₁
    change permHandedness (cfg d₁) * permHandedness (cfg d₃) =
      permHandedness (cfg d₁') * permHandedness (cfg d₃') at agree
    change permHandedness (cfg d₃) * permHandedness (m.ligandPermAt e d₁) =
      (if mirror then -1 else 1) * permHandedness (cfg d₃')
    linear_combination
      (-(permHandedness (cfg d₃) * permHandedness (m.ligandPermAt e d₁))) * sq₁ +
      (permHandedness (cfg d₁) * permHandedness (cfg d₃)) * law₁ +
      ((if mirror then -1 else 1 : ℝ) * permHandedness (cfg d₁')) * agree +
      ((if mirror then -1 else 1 : ℝ) * permHandedness (cfg d₃')) * sq₁'

/-- **Parity completion.** With both an even and an odd root-fixing exchange of the two slots
available, a proper or mirror branch transport exists **exactly** when the sign products of the
coupled bridgehead pairs agree. The forward direction is the accepted parity-coupling
obstruction; the converse chooses the exchange whose handedness realizes the required law. -/
theorem branchTransport_iff_of_coupledPair (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i j : Fin 4) (d₁ d₃ d₁' d₃' : m.Center)
    (reach₁ : LigandBranchReaches m c i d₁.1) (reach₃ : LigandBranchReaches m c i d₃.1)
    (inventory : ∀ d : m.Center, LigandBranchReaches m c i d.1 → d = d₁ ∨ d = d₃)
    (coupled : ∀ e : m.Aut, m.centerPerm e c = c → m.ligandPermAt e c i = j →
      m.centerPerm e d₁ = d₁' ∧ m.centerPerm e d₃ = d₃' ∧
        permHandedness (m.ligandPermAt e d₁) = permHandedness (m.ligandPermAt e d₃))
    (even : ∃ e : m.Aut, m.centerPerm e c = c ∧ m.ligandPermAt e c i = j ∧
      permHandedness (m.ligandPermAt e d₁) = 1)
    (odd : ∃ e : m.Aut, m.centerPerm e c = c ∧ m.ligandPermAt e c i = j ∧
      permHandedness (m.ligandPermAt e d₁) = -1)
    (mirror : Bool) :
    BranchTransport m cfg c i j mirror ↔
      m.configurationSign cfg d₁ * m.configurationSign cfg d₃ =
        m.configurationSign cfg d₁' * m.configurationSign cfg d₃' := by
  constructor
  · intro transport
    by_contra mismatch
    exact not_branchTransport_of_parityCoupling m cfg c i j d₁ d₃ d₁' d₃' reach₁ reach₃ coupled
      mismatch mirror transport
  · intro agree
    obtain ⟨eE, fE, sE, hE⟩ := even
    obtain ⟨eO, fO, sO, hO⟩ := odd
    have useEven : permHandedness (cfg d₁) * 1 =
        (if mirror then -1 else 1 : ℝ) * permHandedness (cfg d₁') →
        BranchTransport m cfg c i j mirror := fun law =>
      branchTransport_of_coupledPair_sign m cfg c i j d₁ d₃ d₁' d₃' inventory coupled eE fE sE
        mirror (by rw [hE]; exact law) agree
    have useOdd : permHandedness (cfg d₁) * -1 =
        (if mirror then -1 else 1 : ℝ) * permHandedness (cfg d₁') →
        BranchTransport m cfg c i j mirror := fun law =>
      branchTransport_of_coupledPair_sign m cfg c i j d₁ d₃ d₁' d₃' inventory coupled eO fO sO
        mirror (by rw [hO]; exact law) agree
    rcases permHandedness_eq_one_or_eq_neg_one (cfg d₁) with ha | ha <;>
      rcases permHandedness_eq_one_or_eq_neg_one (cfg d₁') with ha' | ha' <;>
      cases mirror
    · exact useEven (by rw [ha, ha']; norm_num)
    · exact useOdd (by rw [ha, ha']; norm_num)
    · exact useOdd (by rw [ha, ha']; norm_num)
    · exact useEven (by rw [ha, ha']; norm_num)
    · exact useOdd (by rw [ha, ha']; norm_num)
    · exact useEven (by rw [ha, ha']; norm_num)
    · exact useEven (by rw [ha, ha']; norm_num)
    · exact useOdd (by rw [ha, ha']; norm_num)

end CoupledPair

/-! ### The odd arm exchange -/

/-- The arm swap followed by one exchange of two bridges of cage B. It carries cage A onto cage B
and acts as the transposition of two bridge slots on both bridgehead frames. -/
def oddArmPerm : Equiv.Perm (Fin 15) := Equiv.swap 11 12 * armSwapPerm

theorem oddArm_isAutomorphism : graph.IsAutomorphism oddArmPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

def oddArm : graph.Aut := ⟨oddArmPerm, oddArm_isAutomorphism⟩

/-- A graph automorphism preserves the detected center set, hence is an automorphism of the
canonical multi-center molecule. -/
def canonAut (e : graph.Aut) : cageCanon.Aut := by
  refine ⟨(e : Equiv.Perm (Fin 15)), ⟨e.property, ?_⟩⟩
  intro c
  change c ∈ graph.tetrahedralCenterSet ↔ (e : Equiv.Perm (Fin 15)) c ∈ graph.tetrahedralCenterSet
  exact graph.mem_tetrahedralCenterSet_apply_aut_iff e c

def oddArmCanon : cageCanon.Aut := canonAut oddArm

theorem oddArm_fixes_root : cageCanon.centerPerm oddArmCanon k0 = k0 := by
  apply Subtype.ext
  show (oddArmCanon : Equiv.Perm (Fin 15)) 0 = 0
  decide

theorem oddArm_moves_arm : cageCanon.ligandPermAt oddArmCanon k0 2 = 3 := by
  have action := cageCanon.ligandAtomAt_ligandPermAt (e := oddArmCanon) (c := k0) 2
  rw [oddArm_fixes_root] at action
  have atomEq : cageCanon.ligandAtomAt k0 (cageCanon.ligandPermAt oddArmCanon k0 2) =
      cageCanon.ligandAtomAt k0 3 := by
    rw [action, lig0f]
    decide
  exact (cageCanon.ligandAtomAt_injective k0).eq_iff.mp atomEq

theorem oddArm_coupled :
    cageCanon.centerPerm oddArmCanon k3 = k9 ∧ cageCanon.centerPerm oddArmCanon k8 = k14 ∧
      permHandedness (cageCanon.ligandPermAt oddArmCanon k3) =
        permHandedness (cageCanon.ligandPermAt oddArmCanon k8) :=
  arm_coupled oddArmCanon oddArm_fixes_root oddArm_moves_arm

/-- On the attachment bridgehead frame `[0, 5, 6, 7]` the odd exchange is the transposition of
slots `1` and `2`. -/
theorem oddArm_frame3 : cageCanon.ligandPermAt oddArmCanon k3 = Equiv.swap 1 2 := by
  refine Equiv.ext fun i => ?_
  have action := cageCanon.ligandAtomAt_ligandPermAt (e := oddArmCanon) (c := k3) i
  rw [oddArm_coupled.1, lig3f] at action
  have atomEq : cageCanon.ligandAtomAt k9 (cageCanon.ligandPermAt oddArmCanon k3 i) =
      cageCanon.ligandAtomAt k9 (Equiv.swap 1 2 i) := by
    rw [action, lig9f]
    fin_cases i <;> decide
  exact cageCanon.ligandAtomAt_injective k9 atomEq

theorem swap12_odd : permHandedness (Equiv.swap (1 : Fin 4) 2) = -1 := by
  norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]

/-- On the far bridgehead frame `[4, 5, 6, 7]` the odd exchange acts with the same (odd) parity
as on the attachment frame: the accepted parity coupling of the two bridgeheads. -/
theorem oddArm_handedness8 : permHandedness (cageCanon.ligandPermAt oddArmCanon k8) = -1 := by
  rw [← oddArm_coupled.2.2, oddArm_frame3, swap12_odd]

theorem swap23_odd : permHandedness (Equiv.swap (2 : Fin 4) 3) = -1 := by
  norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (2 : Fin 4) ≠ 3)]

/-! ### The even arm exchange and the exact root classification of the cage graph -/

/-- The accepted arm swap as an automorphism of the canonical molecule. -/
def evenArmCanon : cageCanon.Aut := canonAut armSwap

theorem evenArm_fixes_root : cageCanon.centerPerm evenArmCanon k0 = k0 := by
  apply Subtype.ext
  show (evenArmCanon : Equiv.Perm (Fin 15)) 0 = 0
  decide

theorem evenArm_moves_arm : cageCanon.ligandPermAt evenArmCanon k0 2 = 3 := by
  have action := cageCanon.ligandAtomAt_ligandPermAt (e := evenArmCanon) (c := k0) 2
  rw [evenArm_fixes_root] at action
  have atomEq : cageCanon.ligandAtomAt k0 (cageCanon.ligandPermAt evenArmCanon k0 2) =
      cageCanon.ligandAtomAt k0 3 := by
    rw [action, lig0f]
    decide
  exact (cageCanon.ligandAtomAt_injective k0).eq_iff.mp atomEq

theorem evenArm_coupled :
    cageCanon.centerPerm evenArmCanon k3 = k9 ∧ cageCanon.centerPerm evenArmCanon k8 = k14 ∧
      permHandedness (cageCanon.ligandPermAt evenArmCanon k3) =
        permHandedness (cageCanon.ligandPermAt evenArmCanon k8) :=
  arm_coupled evenArmCanon evenArm_fixes_root evenArm_moves_arm

/-- The arm swap acts as the identity on the attachment bridgehead frame `[0, 5, 6, 7]`. -/
theorem evenArm_frame3 : cageCanon.ligandPermAt evenArmCanon k3 = 1 := by
  refine Equiv.ext fun i => ?_
  have action := cageCanon.ligandAtomAt_ligandPermAt (e := evenArmCanon) (c := k3) i
  rw [evenArm_coupled.1, lig3f] at action
  have atomEq : cageCanon.ligandAtomAt k9 (cageCanon.ligandPermAt evenArmCanon k3 i) =
      cageCanon.ligandAtomAt k9 ((1 : Equiv.Perm (Fin 4)) i) := by
    rw [action, lig9f]
    fin_cases i <;> decide
  exact cageCanon.ligandAtomAt_injective k9 atomEq

theorem evenArm_handedness3 : permHandedness (cageCanon.ligandPermAt evenArmCanon k3) = 1 := by
  rw [evenArm_frame3]
  exact permHandedness_one

theorem oddArm_handedness3 : permHandedness (cageCanon.ligandPermAt oddArmCanon k3) = -1 := by
  rw [oddArm_frame3]
  exact swap12_odd

/-- The centers reached from the cage-A root slot are exactly the two bridgeheads. -/
theorem armA_inventory (d : cageCanon.Center) (reached : LigandBranchReaches cageCanon k0 2 d.1) :
    d = k3 ∨ d = k8 := by
  have member := reach_armA_mem d.1 reached
  rcases center_cases d with rfl | rfl | rfl | rfl | rfl
  · exact absurd member (by decide)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd member (by decide)
  · exact absurd member (by decide)

/-- **Exact arm transport law of the cage graph**, for every configuration: a proper or mirror
transport of cage A onto cage B exists iff the bridgehead sign products of the two cages agree. -/
theorem arms_transport_iff (cfg : cageCanon.Configuration) (mirror : Bool) :
    BranchTransport cageCanon cfg k0 2 3 mirror ↔
      cageCanon.configurationSign cfg k3 * cageCanon.configurationSign cfg k8 =
        cageCanon.configurationSign cfg k9 * cageCanon.configurationSign cfg k14 :=
  branchTransport_iff_of_coupledPair cageCanon cfg k0 2 3 k3 k8 k9 k14 reach3 reach8
    armA_inventory arm_coupled
    ⟨evenArmCanon, evenArm_fixes_root, evenArm_moves_arm, evenArm_handedness3⟩
    ⟨oddArmCanon, oddArm_fixes_root, oddArm_moves_arm, oddArm_handedness3⟩ mirror

/-- Only the two cage arms can be related at all; a transport between them in either direction
is equivalent to the bridgehead sign-product agreement. -/
theorem root_transport_iff (cfg : cageCanon.Configuration) (i j : Fin 4) (distinct : i ≠ j)
    (mirror : Bool) :
    BranchTransport cageCanon cfg k0 i j mirror ↔
      ((i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) ∧
        cageCanon.configurationSign cfg k3 * cageCanon.configurationSign cfg k8 =
          cageCanon.configurationSign cfg k9 * cageCanon.configurationSign cfg k14 := by
  constructor
  · intro transport
    rcases rootZ_tie i j (transportZ transport) with same | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd same distinct
    · exact ⟨Or.inl ⟨rfl, rfl⟩, (arms_transport_iff cfg mirror).mp transport⟩
    · exact ⟨Or.inr ⟨rfl, rfl⟩, (arms_transport_iff cfg mirror).mp
        (branchTransport_inverse cageCanon cfg k0 transport)⟩
  · rintro ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, agree⟩
    · exact (arms_transport_iff cfg mirror).mpr agree
    · exact branchTransport_inverse cageCanon cfg k0 ((arms_transport_iff cfg mirror).mpr agree)

/-- **Exact root classification of the cage graph.** The root branches are pairwise properly
distinguishable iff the two cages have opposite bridgehead sign products. -/
theorem root_pairwise_iff (cfg : cageCanon.Configuration) :
    MultiCenterMolecule.PairwiseProperDistinguishable cageCanon cfg k0 ↔
      cageCanon.configurationSign cfg k3 * cageCanon.configurationSign cfg k8 ≠
        cageCanon.configurationSign cfg k9 * cageCanon.configurationSign cfg k14 := by
  constructor
  · intro pairwise agree
    exact pairwise 2 3 (by decide) ((arms_transport_iff cfg false).mpr agree)
  · intro mismatch i j distinct transport
    exact mismatch ((root_transport_iff cfg i j distinct false).mp transport).2

/-- **The cage root is never pseudoasymmetric**: for every configuration the physical
enantiomorphic pair count is `0`, because a mirror transport of the arms exists exactly when a
proper one does. -/
theorem root_pairCount_zero (cfg : cageCanon.Configuration) :
    physicalEnantiomorphicPairCount cageCanon cfg k0 = 0 := by
  have noPair : ∀ i j : Fin 4, ¬ Enantiomorphic cageCanon cfg k0 i j := by
    rintro i j ⟨distinct, mirrorTransport, notProper⟩
    obtain ⟨arms, agree⟩ := (root_transport_iff cfg i j distinct true).mp mirrorTransport
    exact notProper ((root_transport_iff cfg i j distinct false).mpr ⟨arms, agree⟩)
  simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, noPair]

/-! ## A family of certified inputs on the cage graph -/

/-- The accepted cage molecule with an arbitrary spatial table. -/
def sourceWith (P : List CartesianPoint3) : AuthoritativeChemicalInput :=
  { molecule := cageSource.molecule, spatial? := some { positions := P } }

theorem sourceWith_wellFormed (P : List CartesianPoint3) (len : P.length = 15) :
    (sourceWith P).StructurallyWellFormed := by
  obtain ⟨moleculeWellFormed, _, diagramWellFormed⟩ := cageAuthority.structurallyWellFormed
  refine ⟨moleculeWellFormed, ?_, diagramWellFormed⟩
  change P.length = 15
  exact len

section Family

variable (P : List CartesianPoint3) (len : P.length = 15)

def certifiedWith : CertifiedLocalizedCIPInput :=
  { certified := { input := sourceWith P, structurallyWellFormed := sourceWith_wellFormed P len }
    graphReady := cageCertified.graphReady }

theorem graphWith : (certifiedWith P len).moleculeGraph = graph := rfl

theorem detectedWith :
    (certifiedWith P len).detectedMultiCenterMolecule = cageCertified.detectedMultiCenterMolecule :=
  rfl

theorem simpleBondedWith : (certifiedWith P len).moleculeGraph.SimpleBonded := simple_bonded

theorem constantChargeWith :
    AcyclicCutBranchAutomorphism.ConstantFormalCharge (certifiedWith P len).moleculeGraph :=
  constant_charge

def posWith (atom : Fin 15) : CartesianPoint3 := P[atom.val]'(by rw [len]; exact atom.isLt)

theorem sourcePointAtWith (atom : Fin 15) :
    (certifiedWith P len).spatialPointAt? atom = some (posWith P len atom) := by
  rw [(certifiedWith P len).spatialPointAt?_eq_some_iff]
  refine ⟨⟨P⟩, rfl, ?_⟩
  change P[atom.val]? = some _
  exact List.getElem?_eq_getElem (by rw [len]; exact atom.isLt)

/-- Oriented volume of the four ligand positions of a center in sorted-neighbour order. -/
def ligandVolumeWith (c : cageCanon.Center) : ℚ :=
  orientedVolume (posWith P len (cageCanon.ligandAtomAt c 0))
    (posWith P len (cageCanon.ligandAtomAt c 1)) (posWith P len (cageCanon.ligandAtomAt c 2))
    (posWith P len (cageCanon.ligandAtomAt c 3))

/-- The calibrated configuration: the sign of each center is the sign of its ligand volume. -/
def cfgWith : cageCanon.Configuration := fun c =>
  if ligandVolumeWith P len c < 0 then Equiv.swap 0 1 else 1

theorem cfgSignWith (c : cageCanon.Center) :
    cageCanon.configurationSign (cfgWith P len) c =
      if ligandVolumeWith P len c < 0 then -1 else 1 := by
  simp only [MultiCenterMolecule.configurationSign, cfgWith]
  split_ifs <;> simp

/-- Every detected center has a nondegenerate ligand tetrahedron. -/
abbrev Nondegenerate : Prop := ∀ c : cageCanon.Center, ligandVolumeWith P len c ≠ 0

theorem canonCoordinatesWith (nondeg : Nondegenerate P len) (c : cageCanon.Center) :
    ActualPhysicalCalibratedCoordinates (certifiedWith P len) cageCanon (cfgWith P len) c := by
  refine ⟨fun i => posWith P len (cageCanon.ligandAtomAt c i),
    fun i => sourcePointAtWith P len _, nondeg c, ?_⟩
  show rationalVolumeSign (ligandVolumeWith P len c) = _
  rw [cfgSignWith]
  split_ifs with negative
  · exact rationalVolumeSign_of_neg negative
  · exact rationalVolumeSign_of_pos
      (lt_of_le_of_ne (not_lt.mp negative) (nondeg c).symm)

/-! ### The detected molecule -/

private theorem calibratedCoordinates_reindexFrames
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration} (tau : m.Center → Equiv.Perm (Fin 4)) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input (m.reindexFrames tau)
      (m.reindexConfiguration tau cfg) center := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := coordinates
  refine ⟨fun i => pointAt (tau center i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed (tau center i)
  · exact cartesianOrientedVolume_perm_ne_zero pointAt (tau center) nonzero
  · have hvec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) k = pointAt k := by
      intro k
      fin_cases k <;> rfl
    have hperm : RationalTetrahedralPermutation.permutedOrientedVolume
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) (tau center) =
        CartesianPoint3.orientedVolume
          (pointAt (tau center 0)) (pointAt (tau center 1))
            (pointAt (tau center 2)) (pointAt (tau center 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
    rw [← hperm, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

private theorem calibratedCoordinates_congr
    {input : CertifiedLocalizedCIPInput} {m n : MultiCenterMolecule input.Atom}
    (h : m = n) (cfg : m.Configuration) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) center) := by
  cases h
  exact coordinates

private theorem branchTransport_congr {m n : MultiCenterMolecule (Fin 15)} (h : m = n)
    (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport m cfg c i j mirror) :
    BranchTransport n (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c) i j mirror := by
  cases h
  exact transport

private theorem pairCount_congr {m n : MultiCenterMolecule (Fin 15)} (h : m = n)
    (cfg : m.Configuration) (c : m.Center) :
    physicalEnantiomorphicPairCount n (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c) =
      physicalEnantiomorphicPairCount m cfg c := by
  cases h
  rfl

/-- The accepted frame reindexing identifies the canonical molecule with the detected molecule of
every input on this graph. -/
theorem tauSpecWith :
    cageCanon.reindexFrames cageTau = (certifiedWith P len).detectedMultiCenterMolecule :=
  cageTau_spec

/-- The calibrated configuration in the detected ligand enumeration. -/
def detectedCfgWith : (certifiedWith P len).detectedMultiCenterMolecule.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration (tauSpecWith P len))
    (cageCanon.reindexConfiguration cageTau (cfgWith P len))

theorem detectedCoordinatesWith (nondeg : Nondegenerate P len)
    (center : (certifiedWith P len).detectedMultiCenterMolecule.Center) :
    ActualPhysicalCalibratedCoordinates (certifiedWith P len)
      (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len) center := by
  let center' : (cageCanon.reindexFrames cageTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center (tauSpecWith P len).symm) center
  have coordinates' := calibratedCoordinates_reindexFrames
    (input := certifiedWith P len) (m := cageCanon) (cfg := cfgWith P len) cageTau center'
    (canonCoordinatesWith P len nondeg center')
  simpa [detectedCfgWith] using
    calibratedCoordinates_congr (input := certifiedWith P len)
      (m := cageCanon.reindexFrames cageTau)
      (n := (certifiedWith P len).detectedMultiCenterMolecule) (tauSpecWith P len)
      (cageCanon.reindexConfiguration cageTau (cfgWith P len)) center' coordinates'

def rootWith : (certifiedWith P len).TetrahedralCenter :=
  ⟨(0 : Fin 15), (degree_four_iff 0).mpr (by decide)⟩

theorem detectedDomainWith (nondeg : Nondegenerate P len) :
    RecursiveAuxiliaryPhysicalDomain (certifiedWith P len) (detectedCfgWith P len)
      (rootWith P len) :=
  ⟨fun center _ => Or.inr (detectedCoordinatesWith P len nondeg center)⟩

theorem detectedGeometryWith (nondeg : Nondegenerate P len) :
    RootPhysicalGeometry (certifiedWith P len)
      (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len) (rootWith P len) := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := detectedCoordinatesWith P len nondeg (rootWith P len)
  exact ⟨pointAt, observed, nonzero, sign⟩

/-! ### Physical classification at the canonical root -/

private theorem sign_mul_sign {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((if a < 0 then (-1 : ℝ) else 1) * (if b < 0 then (-1 : ℝ) else 1)) =
      if a * b < 0 then -1 else 1 := by
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · have : ¬ a * b < 0 := not_lt.mpr (mul_pos_of_neg_of_neg ha' hb').le
    simp [ha', hb', this]
  · have : a * b < 0 := mul_neg_of_neg_of_pos ha' hb'
    simp [ha', not_lt.mpr hb'.le, this]
  · have : a * b < 0 := mul_neg_of_pos_of_neg ha' hb'
    simp [not_lt.mpr ha'.le, hb', this]
  · have : ¬ a * b < 0 := not_lt.mpr (mul_pos ha' hb').le
    simp [not_lt.mpr ha'.le, not_lt.mpr hb'.le, this]

/-- Opposite bridgehead parities of the two cages. -/
theorem parity_mismatchWith (nondeg : Nondegenerate P len)
    (hA : ligandVolumeWith P len k3 * ligandVolumeWith P len k8 < 0)
    (hB : 0 < ligandVolumeWith P len k9 * ligandVolumeWith P len k14) :
    cageCanon.configurationSign (cfgWith P len) k3 * cageCanon.configurationSign (cfgWith P len) k8 ≠
      cageCanon.configurationSign (cfgWith P len) k9 *
        cageCanon.configurationSign (cfgWith P len) k14 := by
  rw [cfgSignWith, cfgSignWith, cfgSignWith, cfgSignWith, sign_mul_sign (nondeg k3) (nondeg k8),
    sign_mul_sign (nondeg k9) (nondeg k14), if_pos hA, if_neg (not_lt.mpr hB.le)]
  norm_num

/-- Equal bridgehead parities of the two cages. -/
theorem parity_matchWith (nondeg : Nondegenerate P len)
    (hA : ligandVolumeWith P len k3 * ligandVolumeWith P len k8 < 0)
    (hB : ligandVolumeWith P len k9 * ligandVolumeWith P len k14 < 0) :
    cageCanon.configurationSign (cfgWith P len) k3 * cageCanon.configurationSign (cfgWith P len) k8 =
      cageCanon.configurationSign (cfgWith P len) k9 *
        cageCanon.configurationSign (cfgWith P len) k14 := by
  rw [cfgSignWith, cfgSignWith, cfgSignWith, cfgSignWith, sign_mul_sign (nondeg k3) (nondeg k8),
    sign_mul_sign (nondeg k9) (nondeg k14), if_pos hA, if_pos hB]

theorem arms_noTransportWith
    (mismatch : cageCanon.configurationSign (cfgWith P len) k3 *
        cageCanon.configurationSign (cfgWith P len) k8 ≠
      cageCanon.configurationSign (cfgWith P len) k9 *
        cageCanon.configurationSign (cfgWith P len) k14)
    (mirror : Bool) : ¬ BranchTransport cageCanon (cfgWith P len) k0 2 3 mirror :=
  not_branchTransport_of_parityCoupling cageCanon (cfgWith P len) k0 2 3 k3 k8 k9 k14 reach3 reach8
    arm_coupled mismatch mirror

/-- No two distinct root branches are related by any branch transport when the parities differ. -/
theorem root_noTransportWith
    (mismatch : cageCanon.configurationSign (cfgWith P len) k3 *
        cageCanon.configurationSign (cfgWith P len) k8 ≠
      cageCanon.configurationSign (cfgWith P len) k9 *
        cageCanon.configurationSign (cfgWith P len) k14)
    (i j : Fin 4) (mirror : Bool) (distinct : i ≠ j) :
    ¬ BranchTransport cageCanon (cfgWith P len) k0 i j mirror := by
  intro transport
  rcases rootZ_tie i j (transportZ transport) with same | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact distinct same
  · exact arms_noTransportWith P len mismatch mirror transport
  · exact arms_noTransportWith P len mismatch mirror
      (branchTransport_inverse cageCanon (cfgWith P len) k0 transport)

theorem pairCountWith_of_mismatch
    (mismatch : cageCanon.configurationSign (cfgWith P len) k3 *
        cageCanon.configurationSign (cfgWith P len) k8 ≠
      cageCanon.configurationSign (cfgWith P len) k9 *
        cageCanon.configurationSign (cfgWith P len) k14) :
    physicalEnantiomorphicPairCount cageCanon (cfgWith P len) k0 = 0 := by
  have noPair : ∀ i j : Fin 4, ¬ Enantiomorphic cageCanon (cfgWith P len) k0 i j :=
    fun i j pair => root_noTransportWith P len mismatch i j true pair.1 pair.2.1
  simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, noPair]

private theorem sign_law_neg {a b : ℚ} (ha : a ≠ 0) (hb : b = -a) :
    (if a < 0 then (-1 : ℝ) else 1) * (-1) =
      (if (false : Bool) then (-1 : ℝ) else 1) * (if b < 0 then (-1 : ℝ) else 1) := by
  subst hb
  rcases lt_or_gt_of_ne ha with h | h
  · have h' : ¬ (-a < 0) := by linarith
    norm_num [h, h']
  · have h' : -a < 0 := by linarith
    norm_num [not_lt.mpr h.le, h']

/-- **A proper transport of cage A onto cage B** whenever cage B is the exact spatial mirror
image of cage A: the odd exchange `oddArmPerm` obeys the proper sign law at both reached
bridgeheads. -/
theorem arms_properTransportWith (nondeg : Nondegenerate P len)
    (h9 : ligandVolumeWith P len k9 = - ligandVolumeWith P len k3)
    (h14 : ligandVolumeWith P len k14 = - ligandVolumeWith P len k8) :
    BranchTransport cageCanon (cfgWith P len) k0 2 3 false := by
  refine ⟨oddArmCanon, oddArm_fixes_root, oddArm_moves_arm, ?_⟩
  intro d reached
  have member := reach_armA_mem d.1 reached
  rcases center_cases d with rfl | rfl | rfl | rfl | rfl
  · exact absurd member (by decide)
  · rw [oddArm_coupled.1, oddArm_frame3, swap12_odd, cfgSignWith, cfgSignWith]
    exact sign_law_neg (nondeg k3) h9
  · rw [oddArm_coupled.2.1, oddArm_handedness8, cfgSignWith, cfgSignWith]
    exact sign_law_neg (nondeg k8) h14
  · exact absurd member (by decide)
  · exact absurd member (by decide)

theorem not_pairwiseWith (nondeg : Nondegenerate P len)
    (h9 : ligandVolumeWith P len k9 = - ligandVolumeWith P len k3)
    (h14 : ligandVolumeWith P len k14 = - ligandVolumeWith P len k8) :
    ¬ MultiCenterMolecule.PairwiseProperDistinguishable cageCanon (cfgWith P len) k0 :=
  fun pairwise => pairwise 2 3 (by decide) (arms_properTransportWith P len nondeg h9 h14)

/-- With a proper arm transport present, no root pair is enantiomorphic: the arm pair is properly
related, and every other pair differs in atomic number. -/
theorem noEnantiomorphicWith (nondeg : Nondegenerate P len)
    (h9 : ligandVolumeWith P len k9 = - ligandVolumeWith P len k3)
    (h14 : ligandVolumeWith P len k14 = - ligandVolumeWith P len k8) (i j : Fin 4) :
    ¬ Enantiomorphic cageCanon (cfgWith P len) k0 i j := by
  rintro ⟨distinct, mirrorTransport, notProper⟩
  rcases rootZ_tie i j (transportZ mirrorTransport) with same | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact distinct same
  · exact notProper (arms_properTransportWith P len nondeg h9 h14)
  · exact notProper (branchTransport_inverse cageCanon (cfgWith P len) k0
      (arms_properTransportWith P len nondeg h9 h14))

theorem pairCountWith_of_proper (nondeg : Nondegenerate P len)
    (h9 : ligandVolumeWith P len k9 = - ligandVolumeWith P len k3)
    (h14 : ligandVolumeWith P len k14 = - ligandVolumeWith P len k8) :
    physicalEnantiomorphicPairCount cageCanon (cfgWith P len) k0 = 0 := by
  have noPair := noEnantiomorphicWith P len nondeg h9 h14
  simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, noPair]

/-! ### Physical classification at the detected root -/

theorem detected_noTransportWith
    (mismatch : cageCanon.configurationSign (cfgWith P len) k3 *
        cageCanon.configurationSign (cfgWith P len) k8 ≠
      cageCanon.configurationSign (cfgWith P len) k9 *
        cageCanon.configurationSign (cfgWith P len) k14)
    (i j : Fin 4) (mirror : Bool) (distinct : i ≠ j) :
    ¬ BranchTransport (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
      (rootWith P len) i j mirror := by
  intro transport
  have back := branchTransport_congr (tauSpecWith P len).symm (detectedCfgWith P len)
    (rootWith P len) i j mirror transport
  have back' : BranchTransport (cageCanon.reindexFrames cageTau)
      (cageCanon.reindexConfiguration cageTau (cfgWith P len)) (rootWith P len) i j mirror := by
    simpa [detectedCfgWith] using back
  have reindexed : BranchTransport (cageCanon.reindexFrames cageTau)
      (cageCanon.reindexConfiguration cageTau (cfgWith P len)) k0 i j mirror := back'
  have canonical := (MultiCenterMolecule.branchTransport_reindexFrames_iff cageCanon cageTau
    (cfgWith P len) k0 i j mirror).1 reindexed
  exact root_noTransportWith P len mismatch _ _ mirror
    (fun same => distinct ((cageTau k0).injective same)) canonical

theorem detectedPairwiseWith
    (mismatch : cageCanon.configurationSign (cfgWith P len) k3 *
        cageCanon.configurationSign (cfgWith P len) k8 ≠
      cageCanon.configurationSign (cfgWith P len) k9 *
        cageCanon.configurationSign (cfgWith P len) k14) :
    MultiCenterMolecule.PairwiseProperDistinguishable
      (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len) (rootWith P len) :=
  fun i j distinct => detected_noTransportWith P len mismatch i j false distinct

/-- The proper arm transport in the detected enumeration. -/
theorem detected_properTransportWith (nondeg : Nondegenerate P len)
    (h9 : ligandVolumeWith P len k9 = - ligandVolumeWith P len k3)
    (h14 : ligandVolumeWith P len k14 = - ligandVolumeWith P len k8) :
    BranchTransport (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
      (rootWith P len) ((cageTau k0).symm 2) ((cageTau k0).symm 3) false := by
  have canonical := arms_properTransportWith P len nondeg h9 h14
  have reindexed : BranchTransport (cageCanon.reindexFrames cageTau)
      (cageCanon.reindexConfiguration cageTau (cfgWith P len)) k0
      ((cageTau k0).symm 2) ((cageTau k0).symm 3) false := by
    rw [MultiCenterMolecule.branchTransport_reindexFrames_iff, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact canonical
  have moved := branchTransport_congr (tauSpecWith P len)
    (cageCanon.reindexConfiguration cageTau (cfgWith P len)) k0 _ _ false reindexed
  simpa [detectedCfgWith] using moved

theorem detected_notPairwiseWith (nondeg : Nondegenerate P len)
    (h9 : ligandVolumeWith P len k9 = - ligandVolumeWith P len k3)
    (h14 : ligandVolumeWith P len k14 = - ligandVolumeWith P len k8) :
    ¬ MultiCenterMolecule.PairwiseProperDistinguishable
      (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len) (rootWith P len) := by
  intro pairwise
  have distinct : (cageTau k0).symm 2 ≠ (cageTau k0).symm 3 := fun same =>
    absurd ((cageTau k0).symm.injective same) (by decide)
  exact pairwise _ _ distinct (detected_properTransportWith P len nondeg h9 h14)

/-- The detected physical count is the canonical physical count. -/
theorem detectedPairCountWith :
    physicalEnantiomorphicPairCount (certifiedWith P len).detectedMultiCenterMolecule
        (detectedCfgWith P len) (rootWith P len) =
      physicalEnantiomorphicPairCount cageCanon (cfgWith P len) k0 := by
  have step := pairCount_congr (tauSpecWith P len)
    (cageCanon.reindexConfiguration cageTau (cfgWith P len)) k0
  rw [physicalEnantiomorphicPairCount_reindexFrames] at step
  simpa [detectedCfgWith] using step

/-- The pair count of every family member's root is `0`: the root is never pseudoasymmetric. -/
theorem detectedPairCountWith_zero :
    physicalEnantiomorphicPairCount (certifiedWith P len).detectedMultiCenterMolecule
      (detectedCfgWith P len) (rootWith P len) = 0 :=
  (detectedPairCountWith P len).trans (root_pairCount_zero (cfgWith P len))

private theorem pairwise_congr {m n : MultiCenterMolecule (Fin 15)} (h : m = n)
    (cfg : m.Configuration) (c : m.Center) :
    MultiCenterMolecule.PairwiseProperDistinguishable n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) c) ↔
      MultiCenterMolecule.PairwiseProperDistinguishable m cfg c := by
  cases h
  exact Iff.rfl

/-- Detected-level pairwise proper distinguishability is the canonical one. -/
theorem detectedPairwiseWith_iff :
    MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len) (rootWith P len) ↔
      MultiCenterMolecule.PairwiseProperDistinguishable cageCanon (cfgWith P len) k0 := by
  have step := pairwise_congr (tauSpecWith P len)
    (cageCanon.reindexConfiguration cageTau (cfgWith P len)) k0
  rw [MultiCenterMolecule.pairwiseProperDistinguishable_reindexFrames_iff] at step
  simpa [detectedCfgWith] using step

/-- The bridgehead sign products agree iff the two cages have the same in/out volume pattern. -/
theorem signProducts_eq_iff_volumes (nondeg : Nondegenerate P len) :
    cageCanon.configurationSign (cfgWith P len) k3 * cageCanon.configurationSign (cfgWith P len) k8 =
        cageCanon.configurationSign (cfgWith P len) k9 *
          cageCanon.configurationSign (cfgWith P len) k14 ↔
      (ligandVolumeWith P len k3 * ligandVolumeWith P len k8 < 0 ↔
        ligandVolumeWith P len k9 * ligandVolumeWith P len k14 < 0) := by
  rw [cfgSignWith, cfgSignWith, cfgSignWith, cfgSignWith, sign_mul_sign (nondeg k3) (nondeg k8),
    sign_mul_sign (nondeg k9) (nondeg k14)]
  by_cases hA : ligandVolumeWith P len k3 * ligandVolumeWith P len k8 < 0 <;>
    by_cases hB : ligandVolumeWith P len k9 * ligandVolumeWith P len k14 < 0 <;>
    norm_num [hA, hB]

/-- **Exact formal physical classification of every nondegenerate family member.** The root is
pairwise properly distinguishable iff exactly one cage is in/out (opposite volume-product signs),
and its physical enantiomorphic pair count is always `0`. -/
theorem family_root_classification (nondeg : Nondegenerate P len) :
    (MultiCenterMolecule.PairwiseProperDistinguishable
        (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len) (rootWith P len) ↔
      ¬ (ligandVolumeWith P len k3 * ligandVolumeWith P len k8 < 0 ↔
        ligandVolumeWith P len k9 * ligandVolumeWith P len k14 < 0)) ∧
    physicalEnantiomorphicPairCount (certifiedWith P len).detectedMultiCenterMolecule
      (detectedCfgWith P len) (rootWith P len) = 0 := by
  refine ⟨?_, detectedPairCountWith_zero P len⟩
  rw [detectedPairwiseWith_iff, root_pairwise_iff]
  exact not_congr (signProducts_eq_iff_volumes P len nondeg)

/-! ### The actual evaluator on every spatial table -/

def referenceWith : LocalizedRuleMajorReference.Input where
  certified := certifiedWith P len

abbrev framesWith := finalRootFrames (referenceWith P len) (simpleBondedWith P len) (rootWith P len)

abbrev targetWith : LocalizedRuleMajorReference.Occurrence (referenceWith P len) :=
  (certifiedWith P len).localizedFinalOccurrenceExecutable (carrierFuel (referenceWith P len))
    (rootWith P len)

theorem centerWith : (framesWith P len).center = rootWith P len :=
  finalRootFrames_center (referenceWith P len) (simpleBondedWith P len) (rootWith P len)

theorem addressWith : (targetWith P len).1.address = [] :=
  (certifiedWith P len).localizedFinalOccurrenceExecutable_address
    (carrierFuel (referenceWith P len)) (rootWith P len)

theorem realWith : (targetWith P len).1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real (referenceWith P len) (rootWith P len)

theorem historyWith : (targetWith P len).1.node.history = ([0] : List (Fin 15)) := by
  have facts := (rootFrame_target_facts (framesWith P len) (addressWith P len) (realWith P len)).2.1
  refine facts.trans ?_
  rw [centerWith P len]
  rfl

theorem slotWith (a : Fin 15) (adjacent : graph.Adj 0 a) :
    ∃ s : Fin 4, (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt
      (framesWith P len).center ((framesWith P len).detectedLigandPermutation s) = a := by
  have adjacentCenter : graph.Adj (framesWith P len).center.1 a := by
    rw [centerWith P len]
    exact adjacent
  obtain ⟨k, hk⟩ := (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt_surjective
    (framesWith P len).center a adjacentCenter
  exact ⟨(framesWith P len).detectedLigandPermutation.symm k, by
    rw [Equiv.apply_symm_apply]; exact hk⟩

def slotAWith : Fin 4 := Classical.choose (slotWith P len 3 (by decide))
def slotBWith : Fin 4 := Classical.choose (slotWith P len 9 (by decide))

theorem slotAWith_spec : (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt
    (framesWith P len).center ((framesWith P len).detectedLigandPermutation (slotAWith P len)) =
      (3 : Fin 15) :=
  Classical.choose_spec (slotWith P len 3 (by decide))

theorem slotBWith_spec : (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt
    (framesWith P len).center ((framesWith P len).detectedLigandPermutation (slotBWith P len)) =
      (9 : Fin 15) :=
  Classical.choose_spec (slotWith P len 9 (by decide))

theorem slotsWith_ne : slotAWith P len ≠ slotBWith P len := by
  intro same
  have atoms := slotAWith_spec P len
  rw [same, slotBWith_spec P len] at atoms
  exact absurd atoms (by decide : (9 : Fin 15) ≠ 3)

theorem armSwap_rootWith :
    (armSwap : Equiv.Perm (Fin 15)) (framesWith P len).center.1 = (framesWith P len).center.1 := by
  rw [centerWith P len]
  show (armSwap : Equiv.Perm (Fin 15)) 0 = 0
  decide

theorem armSwap_ABWith : (armSwap : Equiv.Perm (Fin 15))
      ((certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
        ((framesWith P len).detectedLigandPermutation (slotAWith P len))) =
    (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
      ((framesWith P len).detectedLigandPermutation (slotBWith P len)) := by
  rw [slotAWith_spec P len, slotBWith_spec P len]
  decide

/-! ### Reader-free refusal witnesses, valid for every configuration -/

/-- Bridge 3-cycle at an attachment bridgehead, history `[c1, 0]`. The residual component
contains only the far bridgehead, which the 3-cycle fixes with even action; no coordinate or
configuration is consulted. -/
theorem cycleWitnessWith (cfg : (certifiedWith P len).detectedMultiCenterMolecule.Configuration)
    (σ : graph.Aut) (c1 c3 s t : Fin 15) (inner : List (Fin 15))
    (basics : s ≠ t ∧ graph.Adj c1 s ∧ graph.Adj c1 t ∧ s ∉ [c1, 0] ∧ t ∉ [c1, 0] ∧
      (∀ x ∈ [c1, 0], (σ : Equiv.Perm (Fin 15)) x = x) ∧ (σ : Equiv.Perm (Fin 15)) s = t)
    (closed : ∀ a b, a ∈ inner → a ∉ [c1, 0] → b ∉ [c1, 0] → graph.Adj a b → b ∈ inner)
    (start : s ∈ inner)
    (centers : ∀ x ∈ inner, x ∈ graph.tetrahedralCenterSet → x = c3)
    (fixes : (σ : Equiv.Perm (Fin 15)) c3 = c3)
    (cube : (σ : Equiv.Perm (Fin 15)) * σ * σ = 1) :
    HistoryRefusalWitness (referenceWith P len) cfg ([c1, 0] : List (Fin 15)) c1 := by
  obtain ⟨st, adjS, adjT, freshS, freshT, fixedHistory, sent⟩ := basics
  refine ⟨σ, s, t, st, adjS, adjT, freshS, freshT, fixedHistory, sent, ?_⟩
  intro d component
  have member := inComponent_closed graph [c1, 0] (fun x => x ∈ inner) closed component start
  have dEq : d.1 = c3 := centers _ member d.2
  have fixedE : (referenceWith P len).certified.detectedMultiCenterMolecule.centerPerm
      ((referenceWith P len).certified.physicalDetectedAut σ) d = d := by
    apply Subtype.ext
    show (σ : Equiv.Perm (Fin 15)) d.1 = d.1
    rw [dEq]
    exact fixes
  have cubeE : (referenceWith P len).certified.physicalDetectedAut σ *
      (referenceWith P len).certified.physicalDetectedAut σ *
      (referenceWith P len).certified.physicalDetectedAut σ = 1 := Subtype.ext cube
  rw [fixedE, handedness_of_cube _ _ d fixedE cubeE, mul_one]

/-- Bridge swap at a far bridgehead, history `[c3, o, c1, 0]`. The residual component of a fresh
bridge is that oxygen alone, so the sign law is vacuous for every configuration. -/
theorem swapWitnessWith (cfg : (certifiedWith P len).detectedMultiCenterMolecule.Configuration)
    (σ : graph.Aut) (c1 c3 o s t : Fin 15)
    (basics : s ≠ t ∧ graph.Adj c3 s ∧ graph.Adj c3 t ∧ s ∉ [c3, o, c1, 0] ∧
      t ∉ [c3, o, c1, 0] ∧ (∀ x ∈ [c3, o, c1, 0], (σ : Equiv.Perm (Fin 15)) x = x) ∧
      (σ : Equiv.Perm (Fin 15)) s = t)
    (isolated : ∀ b, b ∉ [c3, o, c1, 0] → graph.Adj s b → False)
    (notCenter : s ∉ graph.tetrahedralCenterSet) :
    HistoryRefusalWitness (referenceWith P len) cfg ([c3, o, c1, 0] : List (Fin 15)) c3 := by
  obtain ⟨st, adjS, adjT, freshS, freshT, fixedHistory, sent⟩ := basics
  refine ⟨σ, s, t, st, adjS, adjT, freshS, freshT, fixedHistory, sent, ?_⟩
  intro d component
  have member := inComponent_closed graph [c3, o, c1, 0] (fun x => x = s)
    (fun a b ha _ hb adjacent => (isolated b hb (ha ▸ adjacent)).elim) component rfl
  have mem : d.1 ∈ graph.tetrahedralCenterSet := d.2
  exact absurd (member ▸ mem) notCenter

theorem cycleWitnessAWith (cfg : (certifiedWith P len).detectedMultiCenterMolecule.Configuration) :
    HistoryRefusalWitness (referenceWith P len) cfg ([3, 0] : List (Fin 15)) (3 : Fin 15) :=
  cycleWitnessWith P len cfg cycleA 3 8 5 6 [4, 5, 6, 7, 8] (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem cycleWitnessBWith (cfg : (certifiedWith P len).detectedMultiCenterMolecule.Configuration) :
    HistoryRefusalWitness (referenceWith P len) cfg ([9, 0] : List (Fin 15)) (9 : Fin 15) :=
  cycleWitnessWith P len cfg cycleB 9 14 11 12 [10, 11, 12, 13, 14] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem swapWitnessAWith (cfg : (certifiedWith P len).detectedMultiCenterMolecule.Configuration)
    (o : Fin 15) (ho : o ∈ [5, 6, 7]) :
    HistoryRefusalWitness (referenceWith P len) cfg ([8, o, 3, 0] : List (Fin 15)) (8 : Fin 15) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact swapWitnessWith P len cfg (otherBridgeSwap 5) 3 8 5 6 7 (by decide) (by decide) (by decide)
  · exact swapWitnessWith P len cfg (otherBridgeSwap 6) 3 8 6 5 7 (by decide) (by decide) (by decide)
  · exact swapWitnessWith P len cfg (otherBridgeSwap 7) 3 8 7 5 6 (by decide) (by decide) (by decide)

theorem swapWitnessBWith (cfg : (certifiedWith P len).detectedMultiCenterMolecule.Configuration)
    (o : Fin 15) (ho : o ∈ [11, 12, 13]) :
    HistoryRefusalWitness (referenceWith P len) cfg ([14, o, 9, 0] : List (Fin 15)) (14 : Fin 15) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact swapWitnessWith P len cfg (otherBridgeSwap 11) 9 14 11 12 13 (by decide) (by decide)
      (by decide)
  · exact swapWitnessWith P len cfg (otherBridgeSwap 12) 9 14 12 11 13 (by decide) (by decide)
      (by decide)
  · exact swapWitnessWith P len cfg (otherBridgeSwap 13) 9 14 13 11 12 (by decide) (by decide)
      (by decide)

/-! ### Every reached occurrence is refused -/

private theorem getLast?_append_of {α : Type*} (l m : List α) {a : α}
    (h : m.getLast? = some a) : (l ++ m).getLast? = some a := by
  simp [List.getLast?_append, h]

theorem blind_of_cageWith (nondeg : Nondegenerate P len) {i j : Fin 4} (distinct : i ≠ j)
    (sent : (armSwap : Equiv.Perm (Fin 15))
        ((certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
          ((framesWith P len).detectedLigandPermutation i)) =
      (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
        ((framesWith P len).detectedLigandPermutation j))
    {c1 c3 h : Fin 15} {os : List (Fin 15)}
    (ligand : (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt
      (framesWith P len).center ((framesWith P len).detectedLigandPermutation i) = c1)
    (cage : Cage graph.Adj 0 c1 c3 h os)
    (armClosed : ∀ a b, a ∈ c1 :: c3 :: h :: os → a ∉ [0] → b ∉ [0] → graph.Adj a b →
      b ∈ c1 :: c3 :: h :: os)
    (centers : ∀ x ∈ c1 :: c3 :: h :: os, x ∈ graph.tetrahedralCenterSet → x = c1 ∨ x = c3)
    (cycleW : HistoryRefusalWitness (referenceWith P len) (detectedCfgWith P len)
      ([c1, 0] : List (Fin 15)) c1)
    (swapW : ∀ o ∈ os, HistoryRefusalWitness (referenceWith P len) (detectedCfgWith P len)
      ([c3, o, c1, 0] : List (Fin 15)) c3) :
    ∀ z, Reach (framesWith P len) i z → referenceState (referenceWith P len) z = none := by
  intro z reach
  by_cases real : z.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  swap
  · exact referenceState_none_of_not_real (referenceWith P len) z real
  by_cases detected : IsDetectedCenter (certifiedWith P len).moleculeGraph
      ((certifiedWith P len).molecularFrameUnit z.1).atom
  swap
  · exact (LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none
      (referenceWith P len) (simpleBondedWith P len) armSwap z real detected).1
  have domain : RecursiveAuxiliaryPhysicalDomain (certifiedWith P len) (detectedCfgWith P len)
      (framesWith P len).center := by
    rw [centerWith P len]
    exact detectedDomainWith P len nondeg
  apply referenceState_none_of_historyWitness (simpleBondedWith P len) (framesWith P len)
    (addressWith P len) (realWith P len) distinct armSwap (armSwap_rootWith P len) sent
    (detectedCfgWith P len) domain z reach real detected
  intro d current
  obtain ⟨cursor, cursorEq, reachable⟩ := reach
  have outwardI : IsLocalizedActualFrameOutwardCursor (certifiedWith P len) (targetWith P len)
      ((framesWith P len).frame.cursorAt i) :=
    ⟨_, (rootFramePair (framesWith P len) (addressWith P len) i i).leftAddress⟩
  obtain ⟨extra, _extraNe, history, located⟩ :=
    reached_history_inComponent (simpleBondedWith P len) (framesWith P len) (realWith P len)
      outwardI cursor reachable
  rw [cursorEq] at history located
  obtain ⟨atom, current', component⟩ := located real
  have atomEq : atom = d := Option.some.inj (current'.symm.trans current)
  subst atomEq
  change RetainedCoherentSymmetry.InComponent graph (targetWith P len).1.node.history
    ((certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
      ((framesWith P len).detectedLigandPermutation i)) atom at component
  rw [ligand, historyWith P len] at component
  have member := inComponent_closed graph [0] (fun x => x ∈ c1 :: c3 :: h :: os) armClosed
    component List.mem_cons_self
  let unit : DetectedOccurrence (certifiedWith P len).moleculeGraph :=
    ⟨(certifiedWith P len).molecularFrameUnit z.1, detected⟩
  let frames := cyclicContextFrameCompilation (referenceWith P len) (simpleBondedWith P len) z real
    unit rfl
  have centerMeaning := ((certifiedWith P len).localizedOccurrenceDescriptorCenter?_eq_some_iff z
    frames.center).mp frames.centerComputed
  have atomCenter : atom = frames.center.1 :=
    Option.some.inj (current.symm.trans centerMeaning.2)
  have isCenter : atom ∈ graph.tetrahedralCenterSet := by
    rw [atomCenter]
    exact frames.center.2
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    (certifiedWith P len) z real
  have head : z.1.node.history.head? = some atom := facts.2.symm.trans current
  have chain : z.1.node.history.IsChain graph.Adj :=
    (certifiedWith P len).declarativeLocalizedOccurrence_node_history_chain
      (((certifiedWith P len).mem_localizedOccurrences_iff _ z.1).mp z.2)
  have rootLast : (targetWith P len).1.node.history.getLast? = some (0 : Fin 15) := by
    rw [historyWith P len]
    rfl
  have last : z.1.node.history.getLast? = some (0 : Fin 15) := by
    rw [history]
    exact getLast?_append_of extra _ rootLast
  rcases centers atom member isCenter with rfl | rfl
  · rw [cage.history_c1 facts.1 chain head last]
    exact cycleW
  · obtain ⟨o, ho, historyEq⟩ := cage.history_c3 facts.1 chain head last
    rw [historyEq]
    exact swapW o ho

/-- A root slot whose ligand is a terminal non-center atom (here H or Cl) reaches only real
non-detected occurrences, all refused. -/
theorem blind_of_isolatedWith {i : Fin 4} {a : Fin 15}
    (ligand : (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt
      (framesWith P len).center ((framesWith P len).detectedLigandPermutation i) = a)
    (isolated : ∀ b, graph.Adj a b → b = 0)
    (notCenter : a ∉ graph.tetrahedralCenterSet) :
    ∀ z, Reach (framesWith P len) i z → referenceState (referenceWith P len) z = none := by
  intro z reach
  by_cases real : z.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  swap
  · exact referenceState_none_of_not_real (referenceWith P len) z real
  by_cases detected : IsDetectedCenter (certifiedWith P len).moleculeGraph
      ((certifiedWith P len).molecularFrameUnit z.1).atom
  swap
  · exact (LocalizedCyclicPhysicalBranchReaderTransport.realNondetected_state_transport_none
      (referenceWith P len) (simpleBondedWith P len) armSwap z real detected).1
  exfalso
  obtain ⟨cursor, cursorEq, reachable⟩ := reach
  have outwardI : IsLocalizedActualFrameOutwardCursor (certifiedWith P len) (targetWith P len)
      ((framesWith P len).frame.cursorAt i) :=
    ⟨_, (rootFramePair (framesWith P len) (addressWith P len) i i).leftAddress⟩
  obtain ⟨extra, _extraNe, history, located⟩ :=
    reached_history_inComponent (simpleBondedWith P len) (framesWith P len) (realWith P len)
      outwardI cursor reachable
  rw [cursorEq] at history located
  obtain ⟨atom, current, component⟩ := located real
  change RetainedCoherentSymmetry.InComponent graph (targetWith P len).1.node.history
    ((certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
      ((framesWith P len).detectedLigandPermutation i)) atom at component
  rw [ligand, historyWith P len] at component
  have member : atom = a := by
    refine inComponent_closed graph [0] (fun x => x = a) ?_ component rfl
    intro x y hx _ hy adjacent
    have hx' : x = a := hx
    rw [hx'] at adjacent
    exact (hy (List.mem_singleton.mpr (isolated y adjacent))).elim
  let unit : DetectedOccurrence (certifiedWith P len).moleculeGraph :=
    ⟨(certifiedWith P len).molecularFrameUnit z.1, detected⟩
  let frames := cyclicContextFrameCompilation (referenceWith P len) (simpleBondedWith P len) z real
    unit rfl
  have centerMeaning := ((certifiedWith P len).localizedOccurrenceDescriptorCenter?_eq_some_iff z
    frames.center).mp frames.centerComputed
  have atomCenter : atom = frames.center.1 :=
    Option.some.inj (current.symm.trans centerMeaning.2)
  apply notCenter
  rw [← member, atomCenter]
  exact frames.center.2

/-- **Every occurrence reached from any root slot is refused.** The H and Cl slots reach only
non-center atoms; the two cage slots are label-blind by the configuration-free witnesses. -/
theorem reached_refusedWith (nondeg : Nondegenerate P len) (i : Fin 4)
    (z : Occurrence (referenceWith P len)) (reach : Reach (framesWith P len) i z) :
    referenceState (referenceWith P len) z = none := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 15, (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt
      (framesWith P len).center ((framesWith P len).detectedLigandPermutation i) = a := ⟨_, rfl⟩
  have adjacent : graph.Adj (framesWith P len).center.1 a := by
    rw [← ha]
    exact (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt_adj
      (framesWith P len).center _
  rw [centerWith P len] at adjacent
  change graph.Adj 0 a at adjacent
  have cases : ∀ x : Fin 15, graph.Adj 0 x → x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 9 := by decide
  rcases cases a adjacent with rfl | rfl | rfl | rfl
  · exact blind_of_isolatedWith P len ha (by decide) (by decide) z reach
  · exact blind_of_isolatedWith P len ha (by decide) (by decide) z reach
  · have distinct : i ≠ slotBWith P len := by
      intro same
      have atoms := slotBWith_spec P len
      rw [← same, ha] at atoms
      exact absurd atoms (by decide : (3 : Fin 15) ≠ 9)
    have sent : (armSwap : Equiv.Perm (Fin 15))
        ((certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
          ((framesWith P len).detectedLigandPermutation i)) =
        (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
          ((framesWith P len).detectedLigandPermutation (slotBWith P len)) := by
      rw [ha, slotBWith_spec P len]
      decide
    exact blind_of_cageWith P len nondeg distinct sent ha cageA (by decide) (by decide)
      (cycleWitnessAWith P len _) (swapWitnessAWith P len _) z reach
  · have distinct : i ≠ slotAWith P len := by
      intro same
      have atoms := slotAWith_spec P len
      rw [← same, ha] at atoms
      exact absurd atoms (by decide : (9 : Fin 15) ≠ 3)
    have sent : (armSwap : Equiv.Perm (Fin 15))
        ((certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
          ((framesWith P len).detectedLigandPermutation i)) =
        (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
          ((framesWith P len).detectedLigandPermutation (slotAWith P len)) := by
      rw [ha, slotAWith_spec P len]
      decide
    exact blind_of_cageWith P len nondeg distinct sent ha cageB (by decide) (by decide)
      (cycleWitnessBWith P len _) (swapWitnessBWith P len _) z reach

/-- The two cage-arm complete keys tie on every nondegenerate spatial table. -/
theorem rootKeys_eqWith (nondeg : Nondegenerate P len) :
    (framesWith P len).retainedKeys (slotAWith P len) =
      (framesWith P len).retainedKeys (slotBWith P len) :=
  retainedKeys_eq_of_blindArms (simpleBondedWith P len) (framesWith P len) (addressWith P len)
    (realWith P len) armSwap (armSwap_rootWith P len) (armSwap_ABWith P len)
    (fun z reach => reach.elim (reached_refusedWith P len nondeg _ z)
      (reached_refusedWith P len nondeg _ z))

/-- The root refuses on every nondegenerate spatial table. -/
theorem root_refusesWith (nondeg : Nondegenerate P len) :
    referenceState (referenceWith P len) (targetWith P len) = none :=
  referenceState_none_of_blindArms (simpleBondedWith P len) (framesWith P len) (addressWith P len)
    (realWith P len) armSwap (slotsWith_ne P len) (armSwap_rootWith P len) (armSwap_ABWith P len)
    (fun z reach => reach.elim (reached_refusedWith P len nondeg _ z)
      (reached_refusedWith P len nondeg _ z))

theorem report_refusesWith (nondeg : Nondegenerate P len) :
    ((rootWith P len).val.val, none) ∈ analyze (referenceWith P len) := by
  rw [analyze_eq_referenceReport (referenceWith P len)]
  exact List.mem_map.mpr ⟨rootWith P len,
    ((certifiedWith P len).mem_canonicalTetrahedralCenters_iff (rootWith P len)).mpr
      (rootWith P len).2,
    Prod.ext rfl (root_refusesWith P len nondeg)⟩

/-! ### The actual root record of a family member -/

theorem finalCenterUnit_eq : finalCenterUnit (referenceWith P len) (rootWith P len) = rootUnit := rfl

/-- The sorted-neighbour slot of each compiled frame slot. -/
def slotPermWith : Equiv.Perm (Fin 4) :=
  (framesWith P len).detectedLigandPermutation.trans
    ((certifiedWith P len).canonicalLigandReindex (rootWith P len))

theorem canonicalLigandAtomWith (k : Fin 4) :
    (certifiedWith P len).canonicalLigandAtom (rootWith P len) k = cageCanon.ligandAtomAt k0 k := rfl

/-- Each compiled frame slot's ligand atom is the sorted-neighbour atom of its canonical slot. -/
theorem actualLigandAtoms_slotPerm (i : Fin 4) :
    (framesWith P len).actualLigandAtoms i = cageCanon.ligandAtomAt k0 (slotPermWith P len i) := by
  have reindex := (certifiedWith P len).canonicalLigandReindex_spec (rootWith P len)
    ((framesWith P len).detectedLigandPermutation i)
  show (certifiedWith P len).detectedMultiCenterMolecule.ligandAtomAt (framesWith P len).center
    ((framesWith P len).detectedLigandPermutation i) = _
  rw [centerWith P len]
  exact reindex.trans (canonicalLigandAtomWith P len _)

/-- The actual coordinate of each compiled frame slot is the certified position of its atom. -/
theorem actualCoordinates_slotPerm (i : Fin 4) :
    (framesWith P len).actualCoordinates i =
      some (posWith P len (cageCanon.ligandAtomAt k0 (slotPermWith P len i))) := by
  show (certifiedWith P len).spatialPointAt? ((framesWith P len).actualLigandAtoms i) = _
  rw [actualLigandAtoms_slotPerm, sourcePointAtWith]

/-- The canonical ligand-root cursor of slot `k` has carrier node `real [0, a]`. -/
theorem ligandCursorCarrier (k : Fin 4) :
    (referenceWith P len).certified.occurrenceCarrierNode (simpleBondedWith P len)
      ((referenceWith P len).certified.localizedLigandRootCursor (rootWith P len) k).occurrence =
    ligandCarrier k := by
  have node : ((referenceWith P len).certified.localizedLigandRootCursor
      (rootWith P len) k).occurrence.1.node =
      (OfficialCIPNode.root (0 : Fin 15)).extend (cageCanon.ligandAtomAt k0 k) 0 := rfl
  have real : ((referenceWith P len).certified.localizedLigandRootCursor
      (rootWith P len) k).occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
    (referenceWith P len).certified.localizedLigandRootNode_provenance (rootWith P len) k
  unfold CertifiedLocalizedCIPInput.occurrenceCarrierNode
  rw [if_pos real, node]
  rfl

/-- The root occurrence has carrier node `real [0]`. -/
theorem targetCarrier :
    (referenceWith P len).certified.occurrenceCarrierNode (simpleBondedWith P len)
      (targetWith P len) = rootCarrier := by
  unfold CertifiedLocalizedCIPInput.occurrenceCarrierNode
  rw [if_pos (realWith P len)]
  rfl

/-- **The compiled canonical cuts are the input-independent slot cuts**, reindexed by the
sorted-neighbour slot of each frame slot. -/
theorem canonicalCutGraphs_slotCut (i : Fin 4) :
    (framesWith P len).canonicalCutGraphs (simpleBondedWith P len) i =
      canonicalSlotCut (slotPermWith P len i) := by
  rw [canonicalCutGraphs_eq_source (framesWith P len) (simpleBondedWith P len)]
  simp only [sourceCutGraphs]
  rw [rootSlot_eq_canonicalLigandCursor (simpleBondedWith P len) (framesWith P len)
    (addressWith P len) (realWith P len) i, centerWith P len]
  show sourceCutArm graph
    ((referenceWith P len).certified.localizedLigandRootCursor (rootWith P len)
      (slotPermWith P len i)).occurrence.1.root
    ((referenceWith P len).certified.occurrenceCarrierNode (simpleBondedWith P len)
      ((referenceWith P len).certified.localizedLigandRootCursor (rootWith P len)
        (slotPermWith P len i)).occurrence)
    ((referenceWith P len).certified.occurrenceCarrierNode (simpleBondedWith P len)
      (targetWith P len)) = _
  rw [ligandCursorCarrier, targetCarrier]
  rfl

/-- The compilation window covers every canonical slot cut. -/
theorem slotCut_windowCovers (k : Fin 4) :
    WindowCovers (canonicalSlotCut k) (framesWith P len).W (framesWith P len).D := by
  have h := canonicalCutGraphs_windowCovers (framesWith P len) (simpleBondedWith P len)
    ((slotPermWith P len).symm k)
  rwa [canonicalCutGraphs_slotCut, Equiv.apply_symm_apply] at h

/-- Every auxiliary read of an actual arm graph is `none`: the read occurrence is reached from
that slot and refused. -/
theorem actualArm_reads_none (nondeg : Nondegenerate P len) (i : Fin 4) :
    ReadsAgree graph 1 (descriptorMap (referenceWith P len)) (fun _ => none) rootUnit
      ((framesWith P len).actualArmGraphs i) := by
  intro node steps occ _real ancestors context
  obtain ⟨cursor, reach, unitEq⟩ := actualArm_read_source (simpleBondedWith P len)
    (framesWith P len) i node steps occ ancestors context
  rw [mapDetected_one graph occ,
    descriptorMap_eq_of_actualState (referenceWith P len) (simpleBondedWith P len) occ
      cursor.occurrence unitEq,
    reached_refusedWith P len nondeg i cursor.occurrence ⟨cursor, rfl, reach⟩]
  rfl

/-- **The actual retained keys are the refused slot keys** at the compilation window. -/
theorem retainedKeys_refused (nondeg : Nondegenerate P len) (i : Fin 4) :
    (framesWith P len).retainedKeys i =
      refusedSlotKey (framesWith P len).W (framesWith P len).D (slotPermWith P len i) := by
  let iso : RootedDigraph.Iso
      ((framesWith P len).canonicalCutGraphs (simpleBondedWith P len) i)
      ((framesWith P len).actualArmGraphs i) :=
    Classical.choice ((framesWith P len).canonicalLigandCut (simpleBondedWith P len) i).faithful
  have armKey := retainedCompleteLigandRule5KeyAt_iso graph (descriptorMap (referenceWith P len))
    rootUnit iso (framesWith P len).W (framesWith P len).D
  have reads := readsAgree_of_iso (molecule := graph) 1 (descriptorMap (referenceWith P len))
    (fun _ => none) rootUnit iso.symm (actualArm_reads_none P len nondeg i)
  have congr := retainedCompleteLigandRule5KeyAt_congr graph
    ((framesWith P len).canonicalCutGraphs (simpleBondedWith P len) i)
    (fun a b n ha hb => cut_parent_unique
      ((framesWith P len).canonicalLigandCut (simpleBondedWith P len) i).focus
      (some ((framesWith P len).canonicalLigandCut (simpleBondedWith P len) i).incoming)
      ((framesWith P len).canonicalLigandCut (simpleBondedWith P len) i).anchor a b n ha hb)
    (descriptorMap (referenceWith P len)) (fun _ => none) rootUnit
    (fun node steps occ real ancestors context => by
      have h := reads node steps occ real ancestors context
      rwa [mapDetected_one graph occ] at h)
    (framesWith P len).W (framesWith P len).D
  calc (framesWith P len).retainedKeys i
      = retainedCompleteLigandRule5KeyAt graph (descriptorMap (referenceWith P len)) rootUnit
          ((framesWith P len).actualArmGraphs i) (framesWith P len).W (framesWith P len).D := rfl
    _ = retainedCompleteLigandRule5KeyAt graph (descriptorMap (referenceWith P len)) rootUnit
          ((framesWith P len).canonicalCutGraphs (simpleBondedWith P len) i)
          (framesWith P len).W (framesWith P len).D := armKey
    _ = retainedCompleteLigandRule5KeyAt graph (fun _ => none) rootUnit
          ((framesWith P len).canonicalCutGraphs (simpleBondedWith P len) i)
          (framesWith P len).W (framesWith P len).D := congr
    _ = refusedSlotKey (framesWith P len).W (framesWith P len).D (slotPermWith P len i) := by
          rw [canonicalCutGraphs_slotCut]
          rfl

/-- The actual root observation record of the family member, indexed by sorted-neighbour slot. -/
def observationWith : RootObservation where
  lt k l := (framesWith P len).retainedKeys ((slotPermWith P len).symm k) <
    (framesWith P len).retainedKeys ((slotPermWith P len).symm l)
  priorTie k l := (ofLex ((framesWith P len).retainedKeys ((slotPermWith P len).symm k))).1 =
    (ofLex ((framesWith P len).retainedKeys ((slotPermWith P len).symm l))).1
  coordinate k := (framesWith P len).actualCoordinates ((slotPermWith P len).symm k)

/-- **The record's order is the actual compound comparator output** through Rule 5: the actual
comparator reports `lt` on two frame slots exactly when the record orders their canonical slots. -/
theorem observation_lt_comparator (i j : Fin 4) :
    ((certifiedWith P len).compareLocalizedRerootCompoundThroughRule5
        ((framesWith P len).compounds i) ((framesWith P len).compounds j)).ordering =
        Ordering.lt ↔
      (observationWith P len).lt (slotPermWith P len i) (slotPermWith P len j) := by
  have actual : ((certifiedWith P len).compareLocalizedRerootCompoundThroughRule5
      ((framesWith P len).compounds i) ((framesWith P len).compounds j)).ordering =
      compare ((framesWith P len).retainedKeys i) ((framesWith P len).retainedKeys j) :=
    (framesWith P len).retainedActual_fullOrdering (simpleBondedWith P len) i j
  rw [actual]
  show _ ↔ (framesWith P len).retainedKeys ((slotPermWith P len).symm (slotPermWith P len i)) <
    (framesWith P len).retainedKeys ((slotPermWith P len).symm (slotPermWith P len j))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact completeLigandRule5Key_compare_lt_iff _ _

/-- **The record's prior tie is the actual prior-key comparator tie** (Rules 1–4c). -/
theorem observation_priorTie_comparator (i j : Fin 4) :
    (certifiedWith P len).compareLocalizedRerootCompoundRule4bcKeys
        ((framesWith P len).compounds i).prior ((framesWith P len).compounds j).prior =
        Ordering.eq ↔
      (observationWith P len).priorTie (slotPermWith P len i) (slotPermWith P len j) := by
  have actual : (certifiedWith P len).compareLocalizedRerootCompoundRule4bcKeys
      ((framesWith P len).compounds i).prior ((framesWith P len).compounds j).prior =
      compare (ofLex ((framesWith P len).retainedKeys i)).1
        (ofLex ((framesWith P len).retainedKeys j)).1 :=
    (framesWith P len).retainedActual_priorComparison (simpleBondedWith P len) i j
  rw [actual]
  show _ ↔ (ofLex ((framesWith P len).retainedKeys
      ((slotPermWith P len).symm (slotPermWith P len i)))).1 =
    (ofLex ((framesWith P len).retainedKeys ((slotPermWith P len).symm (slotPermWith P len j)))).1
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact completeLigandPriorKey_compare_eq_iff _ _

/-- The record's coordinates are the certified positions of the sorted root ligands. -/
theorem observation_coordinate (k : Fin 4) :
    (observationWith P len).coordinate k = some (posWith P len (cageCanon.ligandAtomAt k0 k)) := by
  show (framesWith P len).actualCoordinates ((slotPermWith P len).symm k) = _
  rw [actualCoordinates_slotPerm, Equiv.apply_symm_apply]

/-- The record's order relation is the input-independent refused order. -/
theorem observation_lt (nondeg : Nondegenerate P len) (k l : Fin 4) :
    (observationWith P len).lt k l ↔
      refusedSlotKey nativeW nativeD k < refusedSlotKey nativeW nativeD l := by
  show (framesWith P len).retainedKeys ((slotPermWith P len).symm k) <
    (framesWith P len).retainedKeys ((slotPermWith P len).symm l) ↔ _
  rw [retainedKeys_refused P len nondeg, retainedKeys_refused P len nondeg,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (refusedSlotKey_orderAgrees _ _ (slotCut_windowCovers P len) k l).1

/-- The record's prior-tie relation is the input-independent refused tie relation. -/
theorem observation_priorTie (nondeg : Nondegenerate P len) (k l : Fin 4) :
    (observationWith P len).priorTie k l ↔
      (ofLex (refusedSlotKey nativeW nativeD k)).1 = (ofLex (refusedSlotKey nativeW nativeD l)).1 := by
  show (ofLex ((framesWith P len).retainedKeys ((slotPermWith P len).symm k))).1 =
    (ofLex ((framesWith P len).retainedKeys ((slotPermWith P len).symm l))).1 ↔ _
  rw [retainedKeys_refused P len nondeg, retainedKeys_refused P len nondeg,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (refusedSlotKey_orderAgrees _ _ (slotCut_windowCovers P len) k l).2

/-- **The evaluator's root outcome is the complete-root outcome on the record's keys and
points.** The keys are the actual retained keys in sorted-neighbour order; the points are the
certified root ligand positions. No nondegeneracy is needed: coordinates are always present. -/
theorem rootOutcome_completeRoot (outcome : Option LocalizedAuxiliaryLabel) :
    referenceState (referenceWith P len) (targetWith P len) = outcome ↔
      CompleteRootOutcome (fun k => (framesWith P len).retainedKeys ((slotPermWith P len).symm k))
        (fun k => posWith P len (cageCanon.ligandAtomAt k0 k)) outcome := by
  have retained := (framesWith P len).referenceState_retainedOutcome (simpleBondedWith P len)
  have available : ∀ i, (framesWith P len).actualCoordinates i =
      some (posWith P len (cageCanon.ligandAtomAt k0 (slotPermWith P len i))) :=
    actualCoordinates_slotPerm P len
  have complete := (retainedContextualOutcomeAt_iff_completeRootOutcome graph
    (descriptorMap (referenceWith P len)) rootUnit (framesWith P len).actualArmGraphs
    (framesWith P len).W (framesWith P len).D (framesWith P len).actualCoordinates
    (fun i => posWith P len (cageCanon.ligandAtomAt k0 (slotPermWith P len i))) available
    (referenceState (referenceWith P len) (targetWith P len))).mp retained
  have moved := completeRootOutcome_frameTransport graph (descriptorMap (referenceWith P len))
    rootUnit (framesWith P len).actualArmGraphs
    (fun i => posWith P len (cageCanon.ligandAtomAt k0 (slotPermWith P len i)))
    (slotPermWith P len) false (framesWith P len).W (framesWith P len).D
    (referenceState (referenceWith P len) (targetWith P len)) complete
  have moved' : CompleteRootOutcome
      (fun k => (framesWith P len).retainedKeys ((slotPermWith P len).symm k))
      (fun k => posWith P len
        (cageCanon.ligandAtomAt k0 (slotPermWith P len ((slotPermWith P len).symm k))))
      (referenceState (referenceWith P len) (targetWith P len)) := by
    simpa only [applySpace_false, optionMap_labelAdjust_false] using moved
  simp only [Equiv.apply_symm_apply] at moved'
  constructor
  · rintro rfl
    exact moved'
  · intro holds
    exact (completeRootOutcome_unique holds moved').symm

end Family

/-! ## Determination of the root outcome by the record -/

/-- **Determination.** Two family members with equal root records have equal evaluator root
outcomes. Only the comparison tables and the coordinates of the record are used. -/
theorem rootOutcome_of_observation {P P' : List CartesianPoint3} {len : P.length = 15}
    {len' : P'.length = 15} (same : observationWith P len = observationWith P' len') :
    referenceState (referenceWith P len) (targetWith P len) =
      referenceState (referenceWith P' len') (targetWith P' len') := by
  have first := (rootOutcome_completeRoot P len _).mp rfl
  have second := (rootOutcome_completeRoot P' len' _).mp rfl
  have ltIff : ∀ k l, (framesWith P len).retainedKeys ((slotPermWith P len).symm k) <
      (framesWith P len).retainedKeys ((slotPermWith P len).symm l) ↔
      (framesWith P' len').retainedKeys ((slotPermWith P' len').symm k) <
        (framesWith P' len').retainedKeys ((slotPermWith P' len').symm l) :=
    fun k l => Iff.of_eq (congrArg (fun obs : RootObservation => obs.lt k l) same)
  have priorIff : ∀ k l,
      (ofLex ((framesWith P len).retainedKeys ((slotPermWith P len).symm k))).1 =
        (ofLex ((framesWith P len).retainedKeys ((slotPermWith P len).symm l))).1 ↔
      (ofLex ((framesWith P' len').retainedKeys ((slotPermWith P' len').symm k))).1 =
        (ofLex ((framesWith P' len').retainedKeys ((slotPermWith P' len').symm l))).1 :=
    fun k l => Iff.of_eq (congrArg (fun obs : RootObservation => obs.priorTie k l) same)
  have pointsEq : (fun k => posWith P len (cageCanon.ligandAtomAt k0 k)) =
      fun k => posWith P' len' (cageCanon.ligandAtomAt k0 k) := by
    funext k
    have coord := congrArg (fun obs : RootObservation => obs.coordinate k) same
    simp only [observation_coordinate] at coord
    exact Option.some.inj coord
  have transported := (completeRootOutcome_congr_order ltIff priorIff
    (fun k => posWith P len (cageCanon.ligandAtomAt k0 k))
    (referenceState (referenceWith P len) (targetWith P len))).mp first
  rw [pointsEq] at transported
  exact completeRootOutcome_unique transported second

/-- **The evaluator's root outcome factors through the record** on the whole family. -/
theorem rootOutcome_factors :
    ∃ G : RootObservation → Option LocalizedAuxiliaryLabel,
      ∀ (P : List CartesianPoint3) (len : P.length = 15),
        referenceState (referenceWith P len) (targetWith P len) = G (observationWith P len) := by
  refine ⟨fun obs =>
    if h : ∃ table : {P : List CartesianPoint3 // P.length = 15},
        observationWith table.1 table.2 = obs
    then referenceState (referenceWith h.choose.1 h.choose.2) (targetWith h.choose.1 h.choose.2)
    else none, ?_⟩
  intro P len
  have h : ∃ table : {P : List CartesianPoint3 // P.length = 15},
      observationWith table.1 table.2 = observationWith P len := ⟨⟨P, len⟩, rfl⟩
  simp only [dif_pos h]
  exact (rootOutcome_of_observation h.choose_spec).symm

/-- **Equal root records.** Two nondegenerate family members whose four root ligands occupy the
same positions have the same root observation record. -/
theorem observation_eq_of_rootGeometry {P P' : List CartesianPoint3} {len : P.length = 15}
    {len' : P'.length = 15} (nondeg : Nondegenerate P len) (nondeg' : Nondegenerate P' len')
    (same : ∀ k : Fin 4, posWith P len (cageCanon.ligandAtomAt k0 k) =
      posWith P' len' (cageCanon.ligandAtomAt k0 k)) :
    observationWith P len = observationWith P' len' := by
  refine RootObservation.ext ?_ ?_ ?_
  · funext k l
    exact propext ((observation_lt P len nondeg k l).trans (observation_lt P' len' nondeg' k l).symm)
  · funext k l
    exact propext ((observation_priorTie P len nondeg k l).trans
      (observation_priorTie P' len' nondeg' k l).symm)
  · funext k
    rw [observation_coordinate, observation_coordinate, same k]

/-! ## The promotion-indexed orientation datum that survives refusal -/

section Correlation

/-- The four-cycle `rank ↦ rank + 1` placing the exo hydrogen (slot `0`) at the lowest rank: with
the three bridges ordered by a promotion ordering `ρ` of the slots `1, 2, 3`, the far bridgehead's
rank-to-slot map is `ρ * hydrogenLast`, whereas the attachment bridgehead's is `ρ` (its slot `0`
is the parent). -/
def hydrogenLast : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3

theorem hydrogenLast_odd : permHandedness hydrogenLast = -1 := by
  rw [hydrogenLast, permHandedness_mul, permHandedness_mul, permHandedness_swap, swap12_odd,
    swap23_odd]
  norm_num

/-- The geometric letter sign read at a center under a rank-to-slot map `π`: the configuration
sign times the handedness of the promoted frame ordering. -/
def promotedReading (cfg : cageCanon.Configuration) (c : cageCanon.Center)
    (π : Equiv.Perm (Fin 4)) : ℝ :=
  cageCanon.configurationSign cfg c * permHandedness π

/-- **Promotion-choice invariance of the coupled readings.** For every ordering `ρ` of the bridge
slots, the product of the attachment reading under `ρ` and the far reading under the same ordering
with hydrogen last is `-(s(c)·s(d))`: a like/unlike bit independent of the promotion choice. -/
theorem promotedCorrelation_invariant (cfg : cageCanon.Configuration) (c d : cageCanon.Center)
    (ρ : Equiv.Perm (Fin 4)) :
    promotedReading cfg c ρ * promotedReading cfg d (ρ * hydrogenLast) =
      - (cageCanon.configurationSign cfg c * cageCanon.configurationSign cfg d) := by
  unfold promotedReading
  rw [permHandedness_mul, hydrogenLast_odd]
  have sq := LocalizedRecursiveAuxiliaryPhysicalInverse.permHandedness_mul_self ρ
  linear_combination (-(cageCanon.configurationSign cfg c * cageCanon.configurationSign cfg d)) * sq

/-- The coupled reading is reflection invariant: both signs flip under the mirror configuration. -/
theorem promotedCorrelation_mirror (cfg : cageCanon.Configuration) (c d : cageCanon.Center)
    (ρ : Equiv.Perm (Fin 4)) :
    promotedReading (cageCanon.mirrorConfiguration cfg) c ρ *
        promotedReading (cageCanon.mirrorConfiguration cfg) d (ρ * hydrogenLast) =
      promotedReading cfg c ρ * promotedReading cfg d (ρ * hydrogenLast) := by
  rw [promotedCorrelation_invariant, promotedCorrelation_invariant,
    MultiCenterMolecule.configurationSign_mirrorConfiguration,
    MultiCenterMolecule.configurationSign_mirrorConfiguration]
  ring

end Correlation

/-! ## The two concrete spatial tables -/

section Concrete

theorem positions_length : positions.length = 15 := by decide

/-- The hydrogen of cage B pointing out of the cage: cage B becomes the exact spatial mirror
image of cage A. -/
def P10out : CartesianPoint3 := point (-5) 0 0

def positionsOut : List CartesianPoint3 :=
  [P0, P1, P2, P3, P4, P5, P6, P7, P8, P9, P10out, P11, P12, P13, P14]

theorem positionsOut_length : positionsOut.length = 15 := by decide

/-! ### Volumes of the accepted hidden-parity table -/

theorem inVolume0 : ligandVolumeWith positions positions_length k0 = orientedVolume P1 P2 P3 P9 := by
  simp only [ligandVolumeWith, lig0.1, lig0.2.1, lig0.2.2.1, lig0.2.2.2]
  rfl
theorem inVolume3 : ligandVolumeWith positions positions_length k3 = orientedVolume P0 P5 P6 P7 := by
  simp only [ligandVolumeWith, lig3.1, lig3.2.1, lig3.2.2.1, lig3.2.2.2]
  rfl
theorem inVolume8 : ligandVolumeWith positions positions_length k8 = orientedVolume P4 P5 P6 P7 := by
  simp only [ligandVolumeWith, lig8.1, lig8.2.1, lig8.2.2.1, lig8.2.2.2]
  rfl
theorem inVolume9 :
    ligandVolumeWith positions positions_length k9 = orientedVolume P0 P11 P12 P13 := by
  simp only [ligandVolumeWith, lig9.1, lig9.2.1, lig9.2.2.1, lig9.2.2.2]
  rfl
theorem inVolume14 :
    ligandVolumeWith positions positions_length k14 = orientedVolume P10 P11 P12 P13 := by
  simp only [ligandVolumeWith, lig14.1, lig14.2.1, lig14.2.2.1, lig14.2.2.2]
  rfl

/-! ### Volumes of the out/out table -/

theorem outVolume0 :
    ligandVolumeWith positionsOut positionsOut_length k0 = orientedVolume P1 P2 P3 P9 := by
  simp only [ligandVolumeWith, lig0.1, lig0.2.1, lig0.2.2.1, lig0.2.2.2]
  rfl
theorem outVolume3 :
    ligandVolumeWith positionsOut positionsOut_length k3 = orientedVolume P0 P5 P6 P7 := by
  simp only [ligandVolumeWith, lig3.1, lig3.2.1, lig3.2.2.1, lig3.2.2.2]
  rfl
theorem outVolume8 :
    ligandVolumeWith positionsOut positionsOut_length k8 = orientedVolume P4 P5 P6 P7 := by
  simp only [ligandVolumeWith, lig8.1, lig8.2.1, lig8.2.2.1, lig8.2.2.2]
  rfl
theorem outVolume9 :
    ligandVolumeWith positionsOut positionsOut_length k9 = orientedVolume P0 P11 P12 P13 := by
  simp only [ligandVolumeWith, lig9.1, lig9.2.1, lig9.2.2.1, lig9.2.2.2]
  rfl
theorem outVolume14 :
    ligandVolumeWith positionsOut positionsOut_length k14 = orientedVolume P10out P11 P12 P13 := by
  simp only [ligandVolumeWith, lig14.1, lig14.2.1, lig14.2.2.1, lig14.2.2.2]
  rfl

theorem inNondegenerate : Nondegenerate positions positions_length := fun c => by
  rcases center_cases c with rfl | rfl | rfl | rfl | rfl
  · rw [inVolume0]; norm_num [orientedVolume, P1, P2, P3, P9, point]
  · rw [inVolume3]; norm_num [orientedVolume, P0, P5, P6, P7, point]
  · rw [inVolume8]; norm_num [orientedVolume, P4, P5, P6, P7, point]
  · rw [inVolume9]; norm_num [orientedVolume, P0, P11, P12, P13, point]
  · rw [inVolume14]; norm_num [orientedVolume, P10, P11, P12, P13, point]

theorem outNondegenerate : Nondegenerate positionsOut positionsOut_length := fun c => by
  rcases center_cases c with rfl | rfl | rfl | rfl | rfl
  · rw [outVolume0]; norm_num [orientedVolume, P1, P2, P3, P9, point]
  · rw [outVolume3]; norm_num [orientedVolume, P0, P5, P6, P7, point]
  · rw [outVolume8]; norm_num [orientedVolume, P4, P5, P6, P7, point]
  · rw [outVolume9]; norm_num [orientedVolume, P0, P11, P12, P13, point]
  · rw [outVolume14]; norm_num [orientedVolume, P10out, P11, P12, P13, point]

/-- Cage A is out/out on both tables. -/
theorem inCageA : ligandVolumeWith positions positions_length k3 *
    ligandVolumeWith positions positions_length k8 < 0 := by
  rw [inVolume3, inVolume8]
  norm_num [orientedVolume, P0, P4, P5, P6, P7, point]

theorem outCageA : ligandVolumeWith positionsOut positionsOut_length k3 *
    ligandVolumeWith positionsOut positionsOut_length k8 < 0 := by
  rw [outVolume3, outVolume8]
  norm_num [orientedVolume, P0, P4, P5, P6, P7, point]

/-- Cage B carries the inner hydrogen on the accepted table. -/
theorem inCageB : 0 < ligandVolumeWith positions positions_length k9 *
    ligandVolumeWith positions positions_length k14 := by
  rw [inVolume9, inVolume14]
  norm_num [orientedVolume, P0, P10, P11, P12, P13, point]

/-- Cage B is out/out on the out/out table. -/
theorem outCageB : ligandVolumeWith positionsOut positionsOut_length k9 *
    ligandVolumeWith positionsOut positionsOut_length k14 < 0 := by
  rw [outVolume9, outVolume14]
  norm_num [orientedVolume, P0, P10out, P11, P12, P13, point]

/-- On the out/out table cage B is the spatial mirror image of cage A at both bridgeheads. -/
theorem outVolume9_neg : ligandVolumeWith positionsOut positionsOut_length k9 =
    - ligandVolumeWith positionsOut positionsOut_length k3 := by
  rw [outVolume9, outVolume3]
  norm_num [orientedVolume, P0, P5, P6, P7, P11, P12, P13, point]

theorem outVolume14_neg : ligandVolumeWith positionsOut positionsOut_length k14 =
    - ligandVolumeWith positionsOut positionsOut_length k8 := by
  rw [outVolume14, outVolume8]
  norm_num [orientedVolume, P4, P5, P6, P7, P10out, P11, P12, P13, point]

theorem inMismatch :
    cageCanon.configurationSign (cfgWith positions positions_length) k3 *
        cageCanon.configurationSign (cfgWith positions positions_length) k8 ≠
      cageCanon.configurationSign (cfgWith positions positions_length) k9 *
        cageCanon.configurationSign (cfgWith positions positions_length) k14 :=
  parity_mismatchWith positions positions_length inNondegenerate inCageA inCageB

theorem outMatch :
    cageCanon.configurationSign (cfgWith positionsOut positionsOut_length) k3 *
        cageCanon.configurationSign (cfgWith positionsOut positionsOut_length) k8 =
      cageCanon.configurationSign (cfgWith positionsOut positionsOut_length) k9 *
        cageCanon.configurationSign (cfgWith positionsOut positionsOut_length) k14 :=
  parity_matchWith positionsOut positionsOut_length outNondegenerate outCageA outCageB

/-! ### Same root geometry -/

/-- The root and its four ligands occupy the same positions on both tables. -/
theorem rootGeometry_same : ∀ a ∈ ([0, 1, 2, 3, 9] : List (Fin 15)),
    (certifiedWith positionsOut positionsOut_length).spatialPointAt? a =
      (certifiedWith positions positions_length).spatialPointAt? a := by
  intro a ha
  rw [sourcePointAtWith positionsOut positionsOut_length, sourcePointAtWith positions positions_length]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The calibrated root sign agrees on both tables. -/
theorem rootSign_same : cfgWith positionsOut positionsOut_length k0 =
    cfgWith positions positions_length k0 := by
  have volumes : ligandVolumeWith positionsOut positionsOut_length k0 =
      ligandVolumeWith positions positions_length k0 := by
    rw [outVolume0, inVolume0]
  simp only [cfgWith, volumes]

/-- The four sorted root ligands (atoms 1, 2, 3, 9) have the same positions on both tables. -/
theorem rootLigandPositions_same (k : Fin 4) :
    posWith positions positions_length (cageCanon.ligandAtomAt k0 k) =
      posWith positionsOut positionsOut_length (cageCanon.ligandAtomAt k0 k) := by
  rw [lig0f]
  fin_cases k <;> rfl

/-- **Equal actual root observation records** of the two tables. -/
theorem observation_same :
    observationWith positions positions_length = observationWith positionsOut positionsOut_length :=
  observation_eq_of_rootGeometry inNondegenerate outNondegenerate rootLigandPositions_same

/-- **No function of the root observation record decides pairwise proper distinguishability**
on the nondegenerate family: the two tables have equal records and opposite verdicts. -/
theorem no_observation_function_decides_distinguishability :
    ¬ ∃ F : RootObservation → Bool,
      ∀ (P : List CartesianPoint3) (len : P.length = 15), Nondegenerate P len →
        (F (observationWith P len) = true ↔
          MultiCenterMolecule.PairwiseProperDistinguishable
            (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
            (rootWith P len)) := by
  rintro ⟨F, decides⟩
  have inVerdict := (decides positions positions_length inNondegenerate).mpr
    (detectedPairwiseWith positions positions_length inMismatch)
  have outVerdict := (decides positionsOut positionsOut_length outNondegenerate).mp
  rw [← observation_same] at outVerdict
  exact detected_notPairwiseWith positionsOut positionsOut_length outNondegenerate outVolume9_neg
    outVolume14_neg (outVerdict inVerdict)

/-- Option-valued form: no classifier of the record returns a descriptor exactly at the
pairwise properly distinguishable members. -/
theorem no_observation_classifier :
    ¬ ∃ F : RootObservation → Option LocalizedAuxiliaryLabel,
      ∀ (P : List CartesianPoint3) (len : P.length = 15), Nondegenerate P len →
        ((F (observationWith P len)).isSome = true ↔
          MultiCenterMolecule.PairwiseProperDistinguishable
            (certifiedWith P len).detectedMultiCenterMolecule (detectedCfgWith P len)
            (rootWith P len)) := by
  rintro ⟨F, decides⟩
  exact no_observation_function_decides_distinguishability
    ⟨fun obs => (F obs).isSome, decides⟩

/-! ### Correlation data of the two tables -/

theorem inCorrelation_separates (ρ : Equiv.Perm (Fin 4)) :
    promotedReading (cfgWith positions positions_length) k3 ρ *
        promotedReading (cfgWith positions positions_length) k8 (ρ * hydrogenLast) ≠
      promotedReading (cfgWith positions positions_length) k9 ρ *
        promotedReading (cfgWith positions positions_length) k14 (ρ * hydrogenLast) := by
  rw [promotedCorrelation_invariant, promotedCorrelation_invariant]
  exact fun h => inMismatch (neg_injective h)

theorem outCorrelation_agrees (ρ : Equiv.Perm (Fin 4)) :
    promotedReading (cfgWith positionsOut positionsOut_length) k3 ρ *
        promotedReading (cfgWith positionsOut positionsOut_length) k8 (ρ * hydrogenLast) =
      promotedReading (cfgWith positionsOut positionsOut_length) k9 ρ *
        promotedReading (cfgWith positionsOut positionsOut_length) k14 (ρ * hydrogenLast) := by
  rw [promotedCorrelation_invariant, promotedCorrelation_invariant, outMatch]

/-! ### The separation -/

/-- **The root observation record cannot determine the formal physical root classification.**
Two certified inputs on the accepted cage graph, with the same root geometry and calibrated root
sign, both in the recursive calibrated physical domain, have the **same actual root observation
record** (`observationWith`: the actual retained-key comparison tables through Rule 5, the
prior-key comparison tables, and the root ligand coordinates, all in sorted-neighbour slot order),
every occurrence reached from any root slot refuses, the cage-arm complete keys tie within each
input, the root refuses, the report records the refusal, and the physical pair count is `0` in
both. Yet on the accepted hidden-parity table the root branches are pairwise properly
distinguishable, whereas on the out/out table a proper transport exchanges the two cage arms. The
evaluator's root outcome factors through the record (`rootOutcome_factors`), so it is `none` on
both; the no-function form is `no_observation_function_decides_distinguishability`. -/
theorem hiddenParity_observationSeparation :
    observationWith positions positions_length =
        observationWith positionsOut positionsOut_length ∧
    (certifiedWith positionsOut positionsOut_length).moleculeGraph =
        (certifiedWith positions positions_length).moleculeGraph ∧
    (certifiedWith positions positions_length).moleculeGraph.SimpleBonded ∧
    AcyclicCutBranchAutomorphism.ConstantFormalCharge
      (certifiedWith positions positions_length).moleculeGraph ∧
    (∀ a ∈ ([0, 1, 2, 3, 9] : List (Fin 15)),
      (certifiedWith positionsOut positionsOut_length).spatialPointAt? a =
        (certifiedWith positions positions_length).spatialPointAt? a) ∧
    cfgWith positionsOut positionsOut_length k0 = cfgWith positions positions_length k0 ∧
    RecursiveAuxiliaryPhysicalDomain (certifiedWith positions positions_length)
      (detectedCfgWith positions positions_length) (rootWith positions positions_length) ∧
    RootPhysicalGeometry (certifiedWith positions positions_length)
      (certifiedWith positions positions_length).detectedMultiCenterMolecule
      (detectedCfgWith positions positions_length) (rootWith positions positions_length) ∧
    RecursiveAuxiliaryPhysicalDomain (certifiedWith positionsOut positionsOut_length)
      (detectedCfgWith positionsOut positionsOut_length) (rootWith positionsOut positionsOut_length) ∧
    RootPhysicalGeometry (certifiedWith positionsOut positionsOut_length)
      (certifiedWith positionsOut positionsOut_length).detectedMultiCenterMolecule
      (detectedCfgWith positionsOut positionsOut_length) (rootWith positionsOut positionsOut_length) ∧
    (∀ i z, Reach (framesWith positions positions_length) i z →
      referenceState (referenceWith positions positions_length) z = none) ∧
    (∀ i z, Reach (framesWith positionsOut positionsOut_length) i z →
      referenceState (referenceWith positionsOut positionsOut_length) z = none) ∧
    (framesWith positions positions_length).retainedKeys (slotAWith positions positions_length) =
      (framesWith positions positions_length).retainedKeys (slotBWith positions positions_length) ∧
    (framesWith positionsOut positionsOut_length).retainedKeys
        (slotAWith positionsOut positionsOut_length) =
      (framesWith positionsOut positionsOut_length).retainedKeys
        (slotBWith positionsOut positionsOut_length) ∧
    referenceState (referenceWith positions positions_length)
      (targetWith positions positions_length) = none ∧
    referenceState (referenceWith positionsOut positionsOut_length)
      (targetWith positionsOut positionsOut_length) = none ∧
    ((rootWith positions positions_length).val.val, none) ∈
      analyze (referenceWith positions positions_length) ∧
    ((rootWith positionsOut positionsOut_length).val.val, none) ∈
      analyze (referenceWith positionsOut positionsOut_length) ∧
    physicalEnantiomorphicPairCount (certifiedWith positions positions_length).detectedMultiCenterMolecule
      (detectedCfgWith positions positions_length) (rootWith positions positions_length) = 0 ∧
    physicalEnantiomorphicPairCount
      (certifiedWith positionsOut positionsOut_length).detectedMultiCenterMolecule
      (detectedCfgWith positionsOut positionsOut_length) (rootWith positionsOut positionsOut_length) = 0 ∧
    MultiCenterMolecule.PairwiseProperDistinguishable
      (certifiedWith positions positions_length).detectedMultiCenterMolecule
      (detectedCfgWith positions positions_length) (rootWith positions positions_length) ∧
    ¬ MultiCenterMolecule.PairwiseProperDistinguishable
      (certifiedWith positionsOut positionsOut_length).detectedMultiCenterMolecule
      (detectedCfgWith positionsOut positionsOut_length) (rootWith positionsOut positionsOut_length) :=
  ⟨observation_same, rfl, simpleBondedWith positions positions_length,
    constantChargeWith positions positions_length, rootGeometry_same, rootSign_same,
    detectedDomainWith positions positions_length inNondegenerate,
    detectedGeometryWith positions positions_length inNondegenerate,
    detectedDomainWith positionsOut positionsOut_length outNondegenerate,
    detectedGeometryWith positionsOut positionsOut_length outNondegenerate,
    reached_refusedWith positions positions_length inNondegenerate,
    reached_refusedWith positionsOut positionsOut_length outNondegenerate,
    rootKeys_eqWith positions positions_length inNondegenerate,
    rootKeys_eqWith positionsOut positionsOut_length outNondegenerate,
    root_refusesWith positions positions_length inNondegenerate,
    root_refusesWith positionsOut positionsOut_length outNondegenerate,
    report_refusesWith positions positions_length inNondegenerate,
    report_refusesWith positionsOut positionsOut_length outNondegenerate,
    (detectedPairCountWith positions positions_length).trans
      (pairCountWith_of_mismatch positions positions_length inMismatch),
    (detectedPairCountWith positionsOut positionsOut_length).trans
      (pairCountWith_of_proper positionsOut positionsOut_length outNondegenerate outVolume9_neg
        outVolume14_neg),
    detectedPairwiseWith positions positions_length inMismatch,
    detected_notPairwiseWith positionsOut positionsOut_length outNondegenerate outVolume9_neg
      outVolume14_neg⟩

/-- The explicit proper transport of the out/out root, in the detected enumeration. -/
theorem out_properTransport :
    BranchTransport (certifiedWith positionsOut positionsOut_length).detectedMultiCenterMolecule
      (detectedCfgWith positionsOut positionsOut_length) (rootWith positionsOut positionsOut_length)
      ((cageTau k0).symm 2) ((cageTau k0).symm 3) false :=
  detected_properTransportWith positionsOut positionsOut_length outNondegenerate outVolume9_neg
    outVolume14_neg

/-! ### Bridge to the accepted counterexample input -/

/-- The hidden-parity member of the family is definitionally the accepted counterexample input. -/
theorem inCertified_eq_accepted : certifiedWith positions positions_length = cageCertified := rfl

/-- Its calibrated canonical configuration is definitionally the accepted one. -/
theorem inCfg_eq_accepted : cfgWith positions positions_length = cageCfg := rfl

end Concrete

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.walk_closed
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.reach_armA_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.oddArm_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.oddArm_frame3
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.oddArm_handedness8
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.arms_properTransportWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.root_noTransportWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.detected_noTransportWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.detected_properTransportWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.detectedPairCountWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.cycleWitnessWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.swapWitnessWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.blind_of_cageWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.blind_of_isolatedWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.reached_refusedWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.rootKeys_eqWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.root_refusesWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.report_refusesWith
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.promotedCorrelation_invariant
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.promotedCorrelation_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.inCorrelation_separates
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.outCorrelation_agrees
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.branchTransport_of_coupledPair_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.branchTransport_iff_of_coupledPair
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.evenArm_frame3
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.armA_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.arms_transport_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.root_transport_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.root_pairwise_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.root_pairCount_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.detectedPairwiseWith_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.family_root_classification
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.refusedSlotKey_orderAgrees
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.actualLigandAtoms_slotPerm
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.canonicalCutGraphs_slotCut
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.actualArm_reads_none
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.retainedKeys_refused
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.observation_lt_comparator
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.observation_priorTie_comparator
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.rootOutcome_completeRoot
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.rootOutcome_of_observation
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.rootOutcome_factors
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.observation_eq_of_rootGeometry
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.observation_same
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.no_observation_function_decides_distinguishability
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.no_observation_classifier
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.hiddenParity_observationSeparation
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.out_properTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryObservationSeparation.inCertified_eq_accepted
