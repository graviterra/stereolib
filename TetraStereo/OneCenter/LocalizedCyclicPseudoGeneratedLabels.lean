import TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

/-!
# Geometry and truncated-key support for the cyclic pseudoasymmetry candidate

`pseudoCfg` is the canonical-frame calibration constructed in
`LocalizedCyclicPseudoSpatialWitness`. It is not a generated R/S map. The letters
below are `descriptorOfOrientedVolume?` of the points `spatialPointAt?` returns,
in the ligand order derived from manually assembled one-step official Rule-1a keys.
These keys have not been identified with actual standard-fuel built-stage keys, and
`real_center_paths` establishes history/provenance rather than carrier membership.
No generated `referenceState` label is proved in this module.

The rootward carbon is the real parent already on the path. Extending a node
back onto that parent is a ring duplicate; those duplicate nodes are not the
parent keys. In particular, `armViaParent` and `closingViaParent` below use backtrack
duplicates as atomic-number placeholders in truncated tables; they are not actual
retained cursor expansions. Their Rule-1a calculations give the proposed order
`Cl > Cl-bearing carbon > root carbon > H`, decided by the first two Rule-1a
spheres. Transferring those calculations to the actual full builder remains separate.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels

open TetraStereo.OneCenter
open AuthoritativeChemicalInput
open CartesianPoint3
open CertifiedLocalizedCIPInput
open LocalizedCyclicPseudoInputWitness
open LocalizedCyclicPseudoSpatialWitness
open MoleculeGraph
open OfficialCIPNode
open OfficialRuleMajorKey

/-! ## Comparator facts -/

private theorem compareNat_eq_self (n : ℕ) : compareNat n n = Ordering.eq := by
  simp [compareNat]

private theorem compareNat_gt {a b : ℕ} (higher : b < a) : compareNat a b = Ordering.gt := by
  have notLt : ¬ a < b := Nat.not_lt_of_gt higher
  have notEq : a ≠ b := ne_of_gt higher
  simp only [compareNat]
  change compareOfLessAndEq a b = Ordering.gt
  simp [compareOfLessAndEq, notLt, notEq]

private theorem compareLex_nat_eq_self :
    ∀ address : List ℕ, List.compareLex compareNat address address = Ordering.eq
  | [] => by simp [List.compareLex]
  | head :: tail => by
      rw [List.compareLex_cons_cons, compareNat_eq_self head, compareLex_nat_eq_self tail]
      rfl

private theorem entry_eq (address : List ℕ) (value : ℕ) :
    compareSparseEntry compareNat (address, value) (address, value) = Ordering.eq := by
  unfold compareSparseEntry compareLex Ordering.byKey
  simp [flip, compareLex_nat_eq_self address, compareNat_eq_self value]

private theorem entry_gt (a b : ℕ) (higher : b < a) :
    compareSparseEntry compareNat ([0], a) ([0], b) = Ordering.gt := by
  have compared : compareNat a b = Ordering.gt := compareNat_gt higher
  unfold compareSparseEntry compareLex Ordering.byKey
  simp only [List.compareLex, flip, compared]
  rw [compareNat_eq_self]
  rfl

private theorem singleton_layer_eq (z : ℕ) :
    compareSparseLayer compareNat [([], z)] [([], z)] = Ordering.eq := by
  unfold compareSparseLayer
  rw [List.compareLex_cons_cons, entry_eq [] z, List.compareLex_nil_nil]
  rfl

private theorem compare_gt_of_heads {left right : OfficialRuleMajorKey (Fin 9)}
    {leftZ rightZ : ℕ}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (higher : rightZ < leftZ) :
    compare left right = Ordering.gt := by
  have layers := officialRuleMajorKey_compare_rule1a_gt_of_heads_gt leftHead rightHead higher
  rw [compare_eq_rule1a_of_decisive (by rw [layers]; decide), layers]

private theorem second_gt (z a b : ℕ) (higher : b < a)
    (tailL tailR : List (OfficialSparseEntry ℕ)) :
    compareSparseLayers compareNat
      [[([], z)], ([0], a) :: tailL] [[([], z)], ([0], b) :: tailR] = Ordering.gt := by
  unfold compareSparseLayers
  rw [List.compareLex_cons_cons, singleton_layer_eq z, List.compareLex_cons_cons]
  have head : compareSparseLayer compareNat (([0], a) :: tailL) (([0], b) :: tailR) =
      Ordering.gt := by
    unfold compareSparseLayer
    rw [List.compareLex_cons_cons, entry_gt a b higher]
    rfl
  rw [head, List.compareLex_nil_nil]
  rfl

private theorem compare_gt_of_rule1a {left right : OfficialRuleMajorKey (Fin 9)}
    {layersL layersR : List (List (OfficialSparseEntry ℕ))}
    (leftRule : left.rule1a = layersL) (rightRule : right.rule1a = layersR)
    (layers : compareSparseLayers compareNat layersL layersR = Ordering.gt) :
    compare left right = Ordering.gt := by
  have decisive : compareSparseLayers compareNat left.rule1a right.rule1a = Ordering.gt := by
    rw [leftRule, rightRule, layers]
  rw [compare_eq_rule1a_of_decisive (by rw [decisive]; decide), decisive]

private theorem second_against_leaf (z : ℕ) (second : List (OfficialSparseEntry ℕ)) :
    compareSparseLayers compareNat [[([], z)], second] [[([], z)]] = Ordering.gt := by
  unfold compareSparseLayers
  rw [List.compareLex_cons_cons, singleton_layer_eq z, List.compareLex_cons_nil]
  rfl

private theorem entry_refl (cmp : ℕ → ℕ → Ordering) (hrefl : ∀ n, cmp n n = Ordering.eq)
    (entry : OfficialSparseEntry ℕ) : compareSparseEntry cmp entry entry = Ordering.eq := by
  cases entry with
  | mk address value =>
      unfold compareSparseEntry compareLex Ordering.byKey
      simp [flip, compareLex_nat_eq_self address, hrefl value]

private theorem layerLex_refl (cmp : ℕ → ℕ → Ordering) (hrefl : ∀ n, cmp n n = Ordering.eq) :
    ∀ layer : List (OfficialSparseEntry ℕ),
      List.compareLex (compareSparseEntry cmp) layer layer = Ordering.eq
  | [] => by simp [List.compareLex]
  | entry :: rest => by
      rw [List.compareLex_cons_cons, entry_refl cmp hrefl entry, layerLex_refl cmp hrefl rest]
      rfl

private theorem layer_refl (cmp : ℕ → ℕ → Ordering) (hrefl : ∀ n, cmp n n = Ordering.eq)
    (layer : List (OfficialSparseEntry ℕ)) : compareSparseLayer cmp layer layer = Ordering.eq := by
  simpa [compareSparseLayer] using layerLex_refl cmp hrefl layer

private theorem layersLex_refl (cmp : ℕ → ℕ → Ordering) (hrefl : ∀ n, cmp n n = Ordering.eq) :
    ∀ layers : List (List (OfficialSparseEntry ℕ)),
      List.compareLex (compareSparseLayer cmp) layers layers = Ordering.eq
  | [] => by simp [List.compareLex]
  | layer :: rest => by
      rw [List.compareLex_cons_cons, layer_refl cmp hrefl layer, layersLex_refl cmp hrefl rest]
      rfl

private theorem layers_refl (cmp : ℕ → ℕ → Ordering) (hrefl : ∀ n, cmp n n = Ordering.eq)
    (layers : List (List (OfficialSparseEntry ℕ))) :
    compareSparseLayers cmp layers layers = Ordering.eq := by
  simpa [compareSparseLayers] using layersLex_refl cmp hrefl layers

private theorem compareRule1b_eq_self (n : ℕ) : compareRule1b n n = Ordering.eq := by
  simp [compareRule1b, flip, compareNat_eq_self]

private theorem compare_eq_of_projections {left right : OfficialRuleMajorKey (Fin 9)}
    (rule1aEq : left.rule1a = right.rule1a) (rule1bEq : left.rule1b = right.rule1b)
    (rule2Eq : left.rule2 = right.rule2) :
    OfficialRuleMajorKey.compare left right = Ordering.eq := by
  unfold OfficialRuleMajorKey.compare compareLex Ordering.byKey
  rw [rule1aEq, rule1bEq, rule2Eq]
  rw [layers_refl compareNat compareNat_eq_self right.rule1a,
    layers_refl compareRule1b compareRule1b_eq_self right.rule1b,
    layers_refl compareNat compareNat_eq_self right.rule2]
  rfl

/-! ## Real path nodes -/

def rootNode : OfficialCIPNode (Fin 9) := OfficialCIPNode.root 0

def step (node : OfficialCIPNode (Fin 9)) (next : Fin 9) : OfficialCIPNode (Fin 9) :=
  node.extend next 0

def occ2 : OfficialCIPNode (Fin 9) := step rootNode 2
def occ4 : OfficialCIPNode (Fin 9) := step rootNode 4
def occ24 : OfficialCIPNode (Fin 9) := step occ2 4
def occ42 : OfficialCIPNode (Fin 9) := step occ4 2

private theorem root_history : rootNode.history = [0] := rfl

private theorem step_history (node : OfficialCIPNode (Fin 9)) (next : Fin 9) :
    (step node next).history = next :: node.history := rfl

private theorem step_current (node : OfficialCIPNode (Fin 9)) (next : Fin 9) :
    (step node next).current? = some next := rfl

private theorem root_current : rootNode.current? = some 0 := rfl

private theorem step_real_of_not_mem {node : OfficialCIPNode (Fin 9)} {next : Fin 9}
    (absent : next ∉ node.history) :
    (step node next).provenance = OfficialCIPNodeProvenance.realAtom := by
  simp only [step, OfficialCIPNode.extend]
  unfold OfficialCIPNode.childProvenance
  rw [if_pos (rfl : (0 : ℕ) = 0), if_neg absent]

private theorem step_duplicate_of_mem {node : OfficialCIPNode (Fin 9)} {next : Fin 9}
    (present : next ∈ node.history) :
    (step node next).provenance =
      OfficialCIPNodeProvenance.ringDuplicate (node.duplicateRootDistance next) := by
  simp only [step, OfficialCIPNode.extend]
  unfold OfficialCIPNode.childProvenance
  rw [if_pos (rfl : (0 : ℕ) = 0), if_pos present]

private theorem absent_root (next : Fin 9) (different : next ≠ 0) : next ∉ rootNode.history := by
  simp [root_history, different]

private theorem occ2_history : occ2.history = [2, 0] := by simp [occ2, step_history, root_history]
private theorem occ4_history : occ4.history = [4, 0] := by simp [occ4, step_history, root_history]
private theorem occ24_history : occ24.history = [4, 2, 0] := by
  simp [occ24, step_history, occ2_history]
private theorem occ42_history : occ42.history = [2, 4, 0] := by
  simp [occ42, step_history, occ4_history]

private theorem occ2_real : occ2.provenance = OfficialCIPNodeProvenance.realAtom :=
  step_real_of_not_mem (absent_root 2 (by decide))

private theorem occ4_real : occ4.provenance = OfficialCIPNodeProvenance.realAtom :=
  step_real_of_not_mem (absent_root 4 (by decide))

private theorem absent_24_8 : (8 : Fin 9) ∉ occ2.history := by simp [occ2_history]
private theorem absent_24 : (4 : Fin 9) ∉ occ2.history := by simp [occ2_history]
private theorem absent_26 : (6 : Fin 9) ∉ occ2.history := by simp [occ2_history]
private theorem absent_23 : (3 : Fin 9) ∉ occ2.history := by simp [occ2_history]
private theorem absent_42 : (2 : Fin 9) ∉ occ4.history := by simp [occ4_history]
private theorem absent_48 : (8 : Fin 9) ∉ occ4.history := by simp [occ4_history]
private theorem absent_47 : (7 : Fin 9) ∉ occ4.history := by simp [occ4_history]
private theorem absent_root_1 : (1 : Fin 9) ∉ rootNode.history := absent_root 1 (by decide)
private theorem absent_root_5 : (5 : Fin 9) ∉ rootNode.history := absent_root 5 (by decide)

private theorem occ24_real : occ24.provenance = OfficialCIPNodeProvenance.realAtom :=
  step_real_of_not_mem absent_24

private theorem occ42_real : occ42.provenance = OfficialCIPNodeProvenance.realAtom :=
  step_real_of_not_mem absent_42

private theorem mem_0_24 : (0 : Fin 9) ∈ occ24.history := by simp [occ24_history]
private theorem mem_2_24 : (2 : Fin 9) ∈ occ24.history := by simp [occ24_history]
private theorem mem_0_42 : (0 : Fin 9) ∈ occ42.history := by simp [occ42_history]
private theorem mem_4_42 : (4 : Fin 9) ∈ occ42.history := by simp [occ42_history]
private theorem mem_0_4 : (0 : Fin 9) ∈ occ4.history := by simp [occ4_history]
private theorem absent_423 : (3 : Fin 9) ∉ occ42.history := by simp [occ42_history]
private theorem absent_426 : (6 : Fin 9) ∉ occ42.history := by simp [occ42_history]
private theorem absent_248 : (8 : Fin 9) ∉ occ24.history := by simp [occ24_history]
private theorem absent_247 : (7 : Fin 9) ∉ occ24.history := by simp [occ24_history]

theorem real_center_paths :
    occ2.history = [2, 0] ∧ occ2.provenance = OfficialCIPNodeProvenance.realAtom ∧
    occ4.history = [4, 0] ∧ occ4.provenance = OfficialCIPNodeProvenance.realAtom ∧
    occ24.history = [4, 2, 0] ∧ occ24.provenance = OfficialCIPNodeProvenance.realAtom ∧
    occ42.history = [2, 4, 0] ∧ occ42.provenance = OfficialCIPNodeProvenance.realAtom :=
  ⟨occ2_history, occ2_real, occ4_history, occ4_real, occ24_history, occ24_real,
    occ42_history, occ42_real⟩

theorem backtrack_from_42_is_duplicate :
    (step occ42 4).provenance =
      OfficialCIPNodeProvenance.ringDuplicate (occ42.duplicateRootDistance 4) :=
  step_duplicate_of_mem mem_4_42

theorem backtrack_from_24_is_duplicate :
    (step occ24 2).provenance =
      OfficialCIPNodeProvenance.ringDuplicate (occ24.duplicateRootDistance 2) :=
  step_duplicate_of_mem mem_2_24

theorem root_center_children (next : Fin 9) :
    graph.Adj 0 next ∧ next ∈ graph.tetrahedralCenterSet ↔ next = 2 ∨ next = 4 := by
  constructor
  · intro ⟨adjacent, center⟩
    have neighbors := (adj_root next).mp adjacent
    have which := (degree_four_iff next).mp center
    rcases neighbors with rfl | rfl | rfl | rfl
    · exact absurd which (by decide)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd which (by decide)
  · intro which
    rcases which with rfl | rfl
    · exact ⟨(adj_root 2).mpr (Or.inr (Or.inl rfl)),
        (degree_four_iff 2).mpr (Or.inr (Or.inl rfl))⟩
    · exact ⟨(adj_root 4).mpr (Or.inr (Or.inr (Or.inl rfl))),
        (degree_four_iff 4).mpr (Or.inr (Or.inr rfl))⟩

theorem no_further_center_from_24 (next : Fin 9) (adjacent : graph.Adj 4 next)
    (center : next ∈ graph.tetrahedralCenterSet) : next ∈ occ24.history := by
  have neighbors := (adj_closing next).mp adjacent
  have which := (degree_four_iff next).mp center
  rcases neighbors with rfl | rfl | rfl | rfl
  · simp [occ24_history]
  · simp [occ24_history]
  · exact absurd which (by decide)
  · exact absurd which (by decide)

theorem no_further_center_from_42 (next : Fin 9) (adjacent : graph.Adj 2 next)
    (center : next ∈ graph.tetrahedralCenterSet) : next ∈ occ42.history := by
  have neighbors := (adj_arm next).mp adjacent
  have which := (degree_four_iff next).mp center
  rcases neighbors with rfl | rfl | rfl | rfl
  · simp [occ42_history]
  · exact absurd which (by decide)
  · simp [occ42_history]
  · exact absurd which (by decide)

/-! ## One-step keys -/

private theorem z0 : graph.atomZ 0 = 6 := (z_carbon 0).mpr (Or.inl rfl)
private theorem z1 : graph.atomZ 1 = 9 := (z_fluorine 1).mpr rfl
private theorem z2 : graph.atomZ 2 = 6 := (z_carbon 2).mpr (Or.inr (Or.inl rfl))
private theorem z3 : graph.atomZ 3 = 17 := (z_chlorine 3).mpr (Or.inl rfl)
private theorem z4 : graph.atomZ 4 = 6 := (z_carbon 4).mpr (Or.inr (Or.inr rfl))
private theorem z5 : graph.atomZ 5 = 1 := (z_hydrogen 5).mpr (Or.inl rfl)
private theorem z6 : graph.atomZ 6 = 1 := (z_hydrogen 6).mpr (Or.inr (Or.inl rfl))
private theorem z7 : graph.atomZ 7 = 1 := (z_hydrogen 7).mpr (Or.inr (Or.inr rfl))
private theorem z8 : graph.atomZ 8 = 17 := (z_chlorine 8).mpr (Or.inr rfl)

private theorem node_z (node : OfficialCIPNode (Fin 9)) (atom : Fin 9)
    (current : node.current? = some atom) :
    (ofLex (graph.officialNodeAtomLabel node)).1 = graph.atomZ atom := by
  cases provenance : node.provenance <;>
    simp [officialNodeAtomLabel, current, provenance, rawCIPAtomLabel, ofLex_toLex]

private theorem node_mass (node : OfficialCIPNode (Fin 9)) (atom : Fin 9)
    (current : node.current? = some atom)
    (real : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    (ofLex (graph.officialNodeAtomLabel node)).2 = graph.atomMass atom := by
  simp [officialNodeAtomLabel, current, real, rawCIPAtomLabel, ofLex_toLex]

def leafKey (node : OfficialCIPNode (Fin 9)) : OfficialRuleMajorKey (Fin 9) :=
  graph.officialRuleMajorRootKey node true

def branchKey (node : OfficialCIPNode (Fin 9)) (children : List (OfficialRuleMajorKey (Fin 9))) :
    OfficialRuleMajorKey (Fin 9) :=
  assemble (graph.officialRuleMajorRootKey node false) children

private theorem leaf_rule1a (node : OfficialCIPNode (Fin 9)) (atom : Fin 9)
    (current : node.current? = some atom) :
    (leafKey node).rule1a = [[([], graph.atomZ atom)]] := by
  rw [leafKey, officialRuleMajorRootKey_rule1a, node_z node atom current]

private theorem leaf_head (node : OfficialCIPNode (Fin 9)) (atom : Fin 9)
    (current : node.current? = some atom) :
    (leafKey node).rule1a.head? = some [([], graph.atomZ atom)] := by
  rw [leaf_rule1a node atom current]
  rfl

private theorem leaf_rule1b (node : OfficialCIPNode (Fin 9)) {distance : ℕ}
    (distanceEq : node.rule1bRootDistance = distance) :
    (leafKey node).rule1b = [[([], distance)]] := by
  rw [leafKey, officialRuleMajorRootKey_rule1b, distanceEq]

private theorem leaf_rule2 (node : OfficialCIPNode (Fin 9)) (atom : Fin 9)
    (current : node.current? = some atom)
    (real : node.provenance = OfficialCIPNodeProvenance.realAtom) :
    (leafKey node).rule2 = [[([], graph.atomMass atom)]] := by
  rw [leafKey, officialRuleMajorRootKey_rule2, node_mass node atom current real]

private theorem root_distance : rootNode.rule1bRootDistance = 0 := by
  simp [rootNode, OfficialCIPNode.root, rule1bRootDistance, depth]

private theorem distance_of_real (node : OfficialCIPNode (Fin 9)) (n : ℕ)
    (real : node.provenance = OfficialCIPNodeProvenance.realAtom)
    (historyEq : node.history.length = n + 1) : node.rule1bRootDistance = n := by
  simp [rule1bRootDistance, real, depth, historyEq]

private theorem occ2_distance : occ2.rule1bRootDistance = 1 :=
  distance_of_real occ2 1 occ2_real (by simp [occ2_history])

private theorem occ4_distance : occ4.rule1bRootDistance = 1 :=
  distance_of_real occ4 1 occ4_real (by simp [occ4_history])

private theorem child_distance (node : OfficialCIPNode (Fin 9)) (next : Fin 9) (n : ℕ)
    (real : (step node next).provenance = OfficialCIPNodeProvenance.realAtom)
    (parentLength : node.history.length = n) :
    (step node next).rule1bRootDistance = n := by
  have lengthEq : (step node next).history.length = n + 1 := by
    simp [step_history, parentLength]
  exact distance_of_real (step node next) n real lengthEq

private theorem occ24_distance : occ24.rule1bRootDistance = 2 :=
  child_distance occ2 4 2 occ24_real (by simp [occ2_history])

private theorem occ42_distance : occ42.rule1bRootDistance = 2 :=
  child_distance occ4 2 2 occ42_real (by simp [occ4_history])

private theorem merge_three
    (proj : OfficialRuleMajorKey (Fin 9) → List (List (OfficialSparseEntry ℕ)))
    (a b c : OfficialRuleMajorKey (Fin 9)) (za zb zc : ℕ)
    (ha : proj a = [[([], za)]]) (hb : proj b = [[([], zb)]])
    (hc : proj c = [[([], zc)]]) :
    mergeChildren [a, b, c] proj = [[([0], za), ([1], zb), ([2], zc)]] := by
  have count : childLayerCount [a, b, c] proj = 1 := by
    simp [childLayerCount, ha, hb, hc]
  have range1 : List.range 1 = [0] := by decide
  simp [mergeChildren, count, range1, List.zipIdx_cons, List.zipIdx_nil, prefixLayer, ha, hb, hc]

private theorem branch_rule1a (node : OfficialCIPNode (Fin 9))
    (children : List (OfficialRuleMajorKey (Fin 9))) (z : ℕ)
    (merged : List (OfficialSparseEntry ℕ))
    (rootZ : (ofLex (graph.officialNodeAtomLabel node)).1 = z)
    (mergeEq : mergeChildren children rule1a = [merged]) :
    (branchKey node children).rule1a = [[([], z)], merged] := by
  simp [branchKey, assemble, officialRuleMajorRootKey, rootZ, mergeEq]

private theorem branch_rule1b (node : OfficialCIPNode (Fin 9))
    (children : List (OfficialRuleMajorKey (Fin 9))) (distance : ℕ)
    (merged : List (OfficialSparseEntry ℕ))
    (rootDistance : node.rule1bRootDistance = distance)
    (mergeEq : mergeChildren children rule1b = [merged]) :
    (branchKey node children).rule1b = [[([], distance)], merged] := by
  simp [branchKey, assemble, officialRuleMajorRootKey, rootDistance, mergeEq]

private theorem branch_rule2 (node : OfficialCIPNode (Fin 9))
    (children : List (OfficialRuleMajorKey (Fin 9))) (mass : ℕ)
    (merged : List (OfficialSparseEntry ℕ))
    (rootMass : (ofLex (graph.officialNodeAtomLabel node)).2 = mass)
    (mergeEq : mergeChildren children rule2 = [merged]) :
    (branchKey node children).rule2 = [[([], mass)], merged] := by
  simp [branchKey, assemble, officialRuleMajorRootKey, rootMass, mergeEq]

private theorem mass_3_8 : graph.atomMass 3 = graph.atomMass 8 := by decide +kernel
private theorem mass_2_4 : graph.atomMass 2 = graph.atomMass 4 := by decide +kernel
private theorem mass_6_7 : graph.atomMass 6 = graph.atomMass 7 := by decide +kernel

/-! ## Root constitutional shell -/

def rootFluorineKey : OfficialRuleMajorKey (Fin 9) := leafKey (step rootNode 1)
def rootHydrogenKey : OfficialRuleMajorKey (Fin 9) := leafKey (step rootNode 5)
def rootCarbon2Key : OfficialRuleMajorKey (Fin 9) :=
  branchKey occ2 [leafKey (step occ2 3), leafKey occ24, leafKey (step occ2 6)]
def rootCarbon4Key : OfficialRuleMajorKey (Fin 9) :=
  branchKey occ4 [leafKey (step occ4 8), leafKey occ42, leafKey (step occ4 7)]

private theorem fluorine_rule1a : rootFluorineKey.rule1a = [[([], 9)]] := by
  simpa [rootFluorineKey, z1] using
    leaf_rule1a (step rootNode 1) 1 (step_current rootNode 1)

private theorem hydrogen_rule1a : rootHydrogenKey.rule1a = [[([], 1)]] := by
  simpa [rootHydrogenKey, z5] using
    leaf_rule1a (step rootNode 5) 5 (step_current rootNode 5)

private theorem carbon2_child_rule1a :
    (leafKey (step occ2 3)).rule1a = [[([], 17)]] ∧
    (leafKey occ24).rule1a = [[([], 6)]] ∧
    (leafKey (step occ2 6)).rule1a = [[([], 1)]] := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [z3] using leaf_rule1a (step occ2 3) 3 (step_current occ2 3)
  · simpa [z4] using leaf_rule1a occ24 4 (step_current occ2 4)
  · simpa [z6] using leaf_rule1a (step occ2 6) 6 (step_current occ2 6)

private theorem carbon4_child_rule1a :
    (leafKey (step occ4 8)).rule1a = [[([], 17)]] ∧
    (leafKey occ42).rule1a = [[([], 6)]] ∧
    (leafKey (step occ4 7)).rule1a = [[([], 1)]] := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [z8] using leaf_rule1a (step occ4 8) 8 (step_current occ4 8)
  · simpa [z2] using leaf_rule1a occ42 2 (step_current occ4 2)
  · simpa [z7] using leaf_rule1a (step occ4 7) 7 (step_current occ4 7)

private theorem carbon2_rule1a :
    rootCarbon2Key.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]] := by
  have children := carbon2_child_rule1a
  have merged := merge_three (·.rule1a) (leafKey (step occ2 3)) (leafKey occ24)
    (leafKey (step occ2 6)) 17 6 1 children.1 children.2.1 children.2.2
  have rootZ : (ofLex (graph.officialNodeAtomLabel occ2)).1 = 6 := by
    rw [node_z occ2 2 (step_current rootNode 2), z2]
  simpa [rootCarbon2Key] using
    branch_rule1a occ2 _ 6 _ rootZ merged

private theorem carbon4_rule1a :
    rootCarbon4Key.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]] := by
  have children := carbon4_child_rule1a
  have merged := merge_three (·.rule1a) (leafKey (step occ4 8)) (leafKey occ42)
    (leafKey (step occ4 7)) 17 6 1 children.1 children.2.1 children.2.2
  have rootZ : (ofLex (graph.officialNodeAtomLabel occ4)).1 = 6 := by
    rw [node_z occ4 4 (step_current rootNode 4), z4]
  simpa [rootCarbon4Key] using
    branch_rule1a occ4 _ 6 _ rootZ merged

private theorem real_child_distance (parent : OfficialCIPNode (Fin 9)) (next : Fin 9)
    (real : (step parent next).provenance = OfficialCIPNodeProvenance.realAtom)
    (parentHistory : parent.history.length = 2) :
    (step parent next).rule1bRootDistance = 2 :=
  child_distance parent next 2 real parentHistory

private theorem carbon_child_rule1b (parent : OfficialCIPNode (Fin 9))
    (chlorineAtom otherAtom hydrogenAtom : Fin 9)
    (chlorineReal : (step parent chlorineAtom).provenance = OfficialCIPNodeProvenance.realAtom)
    (otherReal : (step parent otherAtom).provenance = OfficialCIPNodeProvenance.realAtom)
    (hydrogenReal : (step parent hydrogenAtom).provenance = OfficialCIPNodeProvenance.realAtom)
    (parentLength : parent.history.length = 2) :
    (leafKey (step parent chlorineAtom)).rule1b = [[([], 2)]] ∧
    (leafKey (step parent otherAtom)).rule1b = [[([], 2)]] ∧
    (leafKey (step parent hydrogenAtom)).rule1b = [[([], 2)]] := by
  refine ⟨?_, ?_, ?_⟩
  · exact leaf_rule1b (step parent chlorineAtom)
      (real_child_distance parent chlorineAtom chlorineReal parentLength)
  · exact leaf_rule1b (step parent otherAtom)
      (real_child_distance parent otherAtom otherReal parentLength)
  · exact leaf_rule1b (step parent hydrogenAtom)
      (real_child_distance parent hydrogenAtom hydrogenReal parentLength)

private theorem carbon2_rule1b :
    rootCarbon2Key.rule1b = [[([], 1)], [([0], 2), ([1], 2), ([2], 2)]] := by
  have children := carbon_child_rule1b occ2 3 4 6
    (step_real_of_not_mem absent_23) occ24_real (step_real_of_not_mem absent_26)
    (by simp [occ2_history])
  have merged := merge_three (·.rule1b) (leafKey (step occ2 3)) (leafKey occ24)
    (leafKey (step occ2 6)) 2 2 2 children.1 children.2.1 children.2.2
  simpa [rootCarbon2Key] using
    branch_rule1b occ2 _ 1 _ occ2_distance merged

private theorem carbon4_rule1b :
    rootCarbon4Key.rule1b = [[([], 1)], [([0], 2), ([1], 2), ([2], 2)]] := by
  have children := carbon_child_rule1b occ4 8 2 7
    (step_real_of_not_mem absent_48) occ42_real (step_real_of_not_mem absent_47)
    (by simp [occ4_history])
  have merged := merge_three (·.rule1b) (leafKey (step occ4 8)) (leafKey occ42)
    (leafKey (step occ4 7)) 2 2 2 children.1 children.2.1 children.2.2
  simpa [rootCarbon4Key] using
    branch_rule1b occ4 _ 1 _ occ4_distance merged

private theorem carbon2_rule2 :
    rootCarbon2Key.rule2 =
      [[([], graph.atomMass 2)],
        [([0], graph.atomMass 3), ([1], graph.atomMass 4), ([2], graph.atomMass 6)]] := by
  have chlorine := leaf_rule2 (step occ2 3) 3 (step_current occ2 3)
    (step_real_of_not_mem absent_23)
  have other := leaf_rule2 occ24 4 (step_current occ2 4) occ24_real
  have hydrogen := leaf_rule2 (step occ2 6) 6 (step_current occ2 6)
    (step_real_of_not_mem absent_26)
  have merged := merge_three (·.rule2) (leafKey (step occ2 3)) (leafKey occ24)
    (leafKey (step occ2 6)) (graph.atomMass 3) (graph.atomMass 4) (graph.atomMass 6)
    chlorine other hydrogen
  have rootMass : (ofLex (graph.officialNodeAtomLabel occ2)).2 = graph.atomMass 2 :=
    node_mass occ2 2 (step_current rootNode 2) occ2_real
  simpa [rootCarbon2Key] using
    branch_rule2 occ2 _ (graph.atomMass 2) _ rootMass merged

private theorem carbon4_rule2 :
    rootCarbon4Key.rule2 =
      [[([], graph.atomMass 2)],
        [([0], graph.atomMass 3), ([1], graph.atomMass 4), ([2], graph.atomMass 6)]] := by
  have chlorine := leaf_rule2 (step occ4 8) 8 (step_current occ4 8)
    (step_real_of_not_mem absent_48)
  have other := leaf_rule2 occ42 2 (step_current occ4 2) occ42_real
  have hydrogen := leaf_rule2 (step occ4 7) 7 (step_current occ4 7)
    (step_real_of_not_mem absent_47)
  have merged := merge_three (·.rule2) (leafKey (step occ4 8)) (leafKey occ42)
    (leafKey (step occ4 7)) (graph.atomMass 8) (graph.atomMass 2) (graph.atomMass 7)
    chlorine other hydrogen
  rw [← mass_3_8, mass_2_4, ← mass_6_7] at merged
  have rootMass : (ofLex (graph.officialNodeAtomLabel occ4)).2 = graph.atomMass 2 := by
    rw [node_mass occ4 4 (step_current rootNode 4) occ4_real, ← mass_2_4]
  simpa [rootCarbon4Key] using
    branch_rule2 occ4 _ (graph.atomMass 2) _ rootMass merged

theorem root_carbon_constitutional_tie :
    compare rootCarbon2Key rootCarbon4Key = Ordering.eq :=
  compare_eq_of_projections (carbon2_rule1a.trans carbon4_rule1a.symm)
    (carbon2_rule1b.trans carbon4_rule1b.symm) (carbon2_rule2.trans carbon4_rule2.symm)

theorem root_constitutional_shell :
    compare rootFluorineKey rootCarbon2Key = Ordering.gt ∧
    compare rootFluorineKey rootCarbon4Key = Ordering.gt ∧
    compare rootCarbon2Key rootHydrogenKey = Ordering.gt ∧
    compare rootCarbon4Key rootHydrogenKey = Ordering.gt ∧
    compare rootCarbon2Key rootCarbon4Key = Ordering.eq := by
  refine ⟨?_, ?_, ?_, ?_, root_carbon_constitutional_tie⟩
  · exact compare_gt_of_heads (by rw [fluorine_rule1a]; rfl)
      (by rw [carbon2_rule1a]; rfl) (by decide)
  · exact compare_gt_of_heads (by rw [fluorine_rule1a]; rfl)
      (by rw [carbon4_rule1a]; rfl) (by decide)
  · exact compare_gt_of_heads (by rw [carbon2_rule1a]; rfl)
      (by rw [hydrogen_rule1a]; rfl) (by decide)
  · exact compare_gt_of_heads (by rw [carbon4_rule1a]; rfl)
      (by rw [hydrogen_rule1a]; rfl) (by decide)

/-! ## Auxiliary centers -/

private theorem one_step_rule1a {z : ℕ} (node : OfficialCIPNode (Fin 9)) (atom : Fin 9)
    (current : node.current? = some atom) (zEq : graph.atomZ atom = z)
    (chlorine other hydrogen : OfficialRuleMajorKey (Fin 9))
    (chlorineRule : chlorine.rule1a = [[([], 17)]])
    (otherRule : other.rule1a = [[([], 6)]])
    (hydrogenRule : hydrogen.rule1a = [[([], 1)]]) :
    (branchKey node [chlorine, other, hydrogen]).rule1a =
      [[([], z)], [([0], 17), ([1], 6), ([2], 1)]] := by
  have merged := merge_three (·.rule1a) chlorine other hydrogen 17 6 1 chlorineRule otherRule
    hydrogenRule
  have rootZ : (ofLex (graph.officialNodeAtomLabel node)).1 = z := by
    rw [node_z node atom current, zEq]
  exact branch_rule1a node [chlorine, other, hydrogen] z _ rootZ merged

def armDirectOther : OfficialRuleMajorKey (Fin 9) :=
  branchKey occ24 [leafKey (step occ24 8), leafKey (step occ24 0), leafKey (step occ24 7)]

def armDirectParent : OfficialRuleMajorKey (Fin 9) :=
  branchKey rootNode [leafKey (step rootNode 1), leafKey occ4, leafKey (step rootNode 5)]

def armViaParent : OfficialRuleMajorKey (Fin 9) :=
  branchKey occ4 [leafKey (step occ4 8), leafKey (step occ4 0), leafKey (step occ4 7)]

def closingDirectOther : OfficialRuleMajorKey (Fin 9) :=
  branchKey occ42 [leafKey (step occ42 3), leafKey (step occ42 0), leafKey (step occ42 6)]

def closingViaParent : OfficialRuleMajorKey (Fin 9) :=
  branchKey occ2 [leafKey (step occ2 3), leafKey (step occ2 0), leafKey (step occ2 6)]

private theorem duplicate_rule1a {z : ℕ} (node : OfficialCIPNode (Fin 9)) (atom : Fin 9)
    (zEq : graph.atomZ atom = z) :
    (leafKey (step node atom)).rule1a = [[([], z)]] := by
  simpa [zEq] using leaf_rule1a (step node atom) atom (step_current node atom)

private theorem arm_direct_other_rule :
    armDirectOther.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]] := by
  exact one_step_rule1a occ24 4 (step_current occ2 4) z4 (leafKey (step occ24 8))
    (leafKey (step occ24 0)) (leafKey (step occ24 7))
    (duplicate_rule1a occ24 8 z8) (duplicate_rule1a occ24 0 z0) (duplicate_rule1a occ24 7 z7)

private theorem arm_direct_parent_rule :
    armDirectParent.rule1a = [[([], 6)], [([0], 9), ([1], 6), ([2], 1)]] := by
  have merged := merge_three (·.rule1a) (leafKey (step rootNode 1)) (leafKey occ4)
    (leafKey (step rootNode 5)) 9 6 1
    (by simpa [z1] using leaf_rule1a (step rootNode 1) 1 (step_current rootNode 1))
    (by simpa [z4] using leaf_rule1a occ4 4 (step_current rootNode 4))
    (by simpa [z5] using leaf_rule1a (step rootNode 5) 5 (step_current rootNode 5))
  have rootZ : (ofLex (graph.officialNodeAtomLabel rootNode)).1 = 6 := by
    rw [node_z rootNode 0 root_current, z0]
  simpa [armDirectParent] using
    branch_rule1a rootNode _ 6 _ rootZ merged

private theorem arm_via_parent_rule :
    armViaParent.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]] :=
  one_step_rule1a occ4 4 (step_current rootNode 4) z4 (leafKey (step occ4 8))
    (leafKey (step occ4 0)) (leafKey (step occ4 7))
    (by simpa [z8] using leaf_rule1a (step occ4 8) 8 (step_current occ4 8))
    (duplicate_rule1a occ4 0 z0) (duplicate_rule1a occ4 7 z7)

private theorem closing_direct_other_rule :
    closingDirectOther.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]] :=
  one_step_rule1a occ42 2 (step_current occ4 2) z2 (leafKey (step occ42 3))
    (leafKey (step occ42 0)) (leafKey (step occ42 6))
    (duplicate_rule1a occ42 3 z3) (duplicate_rule1a occ42 0 z0) (duplicate_rule1a occ42 6 z6)

private theorem closing_via_parent_rule :
    closingViaParent.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]] :=
  one_step_rule1a occ2 2 (step_current rootNode 2) z2 (leafKey (step occ2 3))
    (leafKey (step occ2 0)) (leafKey (step occ2 6))
    (duplicate_rule1a occ2 3 z3) (duplicate_rule1a occ2 0 z0) (duplicate_rule1a occ2 6 z6)

private theorem chlorine_over_carbon (chlorine carbon : OfficialRuleMajorKey (Fin 9))
    (chlorineRule : chlorine.rule1a = [[([], 17)]])
    (carbonRule : carbon.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]]) :
    compare chlorine carbon = Ordering.gt :=
  compare_gt_of_heads (by rw [chlorineRule]; rfl) (by rw [carbonRule]; rfl) (by decide)

private theorem carbon_over_root (carbon rootCarbon : OfficialRuleMajorKey (Fin 9))
    (carbonRule : carbon.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]])
    (rootRule : rootCarbon.rule1a = [[([], 6)], [([0], 9), ([1], 6), ([2], 1)]]) :
    compare carbon rootCarbon = Ordering.gt :=
  compare_gt_of_rule1a carbonRule rootRule (second_gt 6 17 9 (by decide) [([1], 6), ([2], 1)]
    [([1], 6), ([2], 1)])

private theorem carbon_over_duplicate (carbon duplicate : OfficialRuleMajorKey (Fin 9))
    (carbonRule : carbon.rule1a = [[([], 6)], [([0], 17), ([1], 6), ([2], 1)]])
    (duplicateRule : duplicate.rule1a = [[([], 6)]]) :
    compare carbon duplicate = Ordering.gt :=
  compare_gt_of_rule1a carbonRule duplicateRule
    (second_against_leaf 6 [([0], 17), ([1], 6), ([2], 1)])

private theorem duplicate_over_hydrogen (duplicate hydrogen : OfficialRuleMajorKey (Fin 9))
    (duplicateRule : duplicate.rule1a = [[([], 6)]])
    (hydrogenRule : hydrogen.rule1a = [[([], 1)]]) :
    compare duplicate hydrogen = Ordering.gt :=
  compare_gt_of_heads (by rw [duplicateRule]; rfl) (by rw [hydrogenRule]; rfl) (by decide)

private theorem parent_over_hydrogen (parent hydrogen : OfficialRuleMajorKey (Fin 9))
    (parentRule : parent.rule1a.head? = some [([], 6)])
    (hydrogenRule : hydrogen.rule1a = [[([], 1)]]) :
    compare parent hydrogen = Ordering.gt :=
  compare_gt_of_heads parentRule (by rw [hydrogenRule]; rfl) (by decide)

theorem arm_direct_order :
    (step occ2 3).current? = some 3 ∧ occ24.current? = some 4 ∧
      rootNode.current? = some 0 ∧ (step occ2 6).current? = some 6 ∧
    compare (leafKey (step occ2 3)) armDirectOther = Ordering.gt ∧
    compare armDirectOther armDirectParent = Ordering.gt ∧
    compare armDirectParent (leafKey (step occ2 6)) = Ordering.gt := by
  refine ⟨step_current occ2 3, step_current occ2 4, root_current, step_current occ2 6, ?_, ?_, ?_⟩
  · exact chlorine_over_carbon _ _ (duplicate_rule1a occ2 3 z3) arm_direct_other_rule
  · exact carbon_over_root _ _ arm_direct_other_rule arm_direct_parent_rule
  · exact parent_over_hydrogen _ _ (by rw [arm_direct_parent_rule]; rfl)
      (duplicate_rule1a occ2 6 z6)

theorem arm_via_closing_order :
    (step occ42 3).current? = some 3 ∧ occ4.current? = some 4 ∧
      (step occ42 0).current? = some 0 ∧ (step occ42 6).current? = some 6 ∧
    (step occ42 0).provenance =
      OfficialCIPNodeProvenance.ringDuplicate (occ42.duplicateRootDistance 0) ∧
    compare (leafKey (step occ42 3)) armViaParent = Ordering.gt ∧
    compare armViaParent (leafKey (step occ42 0)) = Ordering.gt ∧
    compare (leafKey (step occ42 0)) (leafKey (step occ42 6)) = Ordering.gt := by
  refine ⟨step_current occ42 3, step_current rootNode 4, step_current occ42 0,
    step_current occ42 6, step_duplicate_of_mem mem_0_42, ?_, ?_, ?_⟩
  · exact chlorine_over_carbon _ _ (duplicate_rule1a occ42 3 z3) arm_via_parent_rule
  · exact carbon_over_duplicate _ _ arm_via_parent_rule (duplicate_rule1a occ42 0 z0)
  · exact duplicate_over_hydrogen _ _ (duplicate_rule1a occ42 0 z0) (duplicate_rule1a occ42 6 z6)

theorem closing_direct_order :
    (step occ4 8).current? = some 8 ∧ occ42.current? = some 2 ∧
      rootNode.current? = some 0 ∧ (step occ4 7).current? = some 7 ∧
    compare (leafKey (step occ4 8)) closingDirectOther = Ordering.gt ∧
    compare closingDirectOther armDirectParent = Ordering.gt ∧
    compare armDirectParent (leafKey (step occ4 7)) = Ordering.gt := by
  refine ⟨step_current occ4 8, step_current occ4 2, root_current, step_current occ4 7, ?_, ?_, ?_⟩
  · exact chlorine_over_carbon _ _ (duplicate_rule1a occ4 8 z8) closing_direct_other_rule
  · exact carbon_over_root _ _ closing_direct_other_rule arm_direct_parent_rule
  · exact parent_over_hydrogen _ _ (by rw [arm_direct_parent_rule]; rfl)
      (duplicate_rule1a occ4 7 z7)

theorem closing_via_arm_order :
    (step occ24 8).current? = some 8 ∧ occ2.current? = some 2 ∧
      (step occ24 0).current? = some 0 ∧ (step occ24 7).current? = some 7 ∧
    (step occ24 0).provenance =
      OfficialCIPNodeProvenance.ringDuplicate (occ24.duplicateRootDistance 0) ∧
    compare (leafKey (step occ24 8)) closingViaParent = Ordering.gt ∧
    compare closingViaParent (leafKey (step occ24 0)) = Ordering.gt ∧
    compare (leafKey (step occ24 0)) (leafKey (step occ24 7)) = Ordering.gt := by
  refine ⟨step_current occ24 8, step_current rootNode 2, step_current occ24 0,
    step_current occ24 7, step_duplicate_of_mem mem_0_24, ?_, ?_, ?_⟩
  · exact chlorine_over_carbon _ _ (duplicate_rule1a occ24 8 z8) closing_via_parent_rule
  · exact carbon_over_duplicate _ _ closing_via_parent_rule (duplicate_rule1a occ24 0 z0)
  · exact duplicate_over_hydrogen _ _ (duplicate_rule1a occ24 0 z0) (duplicate_rule1a occ24 7 z7)

theorem real_parent_above_backtrack :
    compare armViaParent (leafKey (step occ42 4)) = Ordering.gt ∧
    compare closingViaParent (leafKey (step occ24 2)) = Ordering.gt := by
  refine ⟨?_, ?_⟩
  · exact carbon_over_duplicate _ _ arm_via_parent_rule (duplicate_rule1a occ42 4 z4)
  · exact carbon_over_duplicate _ _ closing_via_parent_rule (duplicate_rule1a occ24 2 z2)

/-! ## Coordinates and geometric letters -/

private theorem spatial_atomCount :
    pseudoSpatialCertified.certified.input.molecule.atomCount = 9 := by
  have moleculeEq : pseudoSpatialCertified.certified.input.molecule = pseudoSource.molecule := by
    rw [show pseudoSpatialCertified.certified.input = pseudoSpatialSource from rfl, spatial_molecule]
  rw [moleculeEq]
  exact atomCount_eq

private def SA (i : Fin 9) : pseudoSpatialCertified.Atom :=
  ⟨i.val, by rw [spatial_atomCount]; exact i.isLt⟩

private theorem read_at (i : Fin 9) (point : CartesianPoint3)
    (lookup : positions[i.val]? = some point) :
    pseudoSpatialCertified.spatialPointAt? (SA i) = some point := by
  rw [spatialPointAt?_eq_some_iff]
  exact ⟨⟨positions⟩, rfl, lookup⟩

theorem spatial_readback :
    pseudoSpatialCertified.spatialPointAt? (SA 0) = some P0 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 1) = some P1 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 2) = some P2 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 3) = some P3 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 4) = some P4 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 5) = some P5 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 6) = some P6 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 7) = some P7 ∧
    pseudoSpatialCertified.spatialPointAt? (SA 8) = some P8 := by
  refine ⟨read_at 0 P0 rfl, read_at 1 P1 rfl, read_at 2 P2 rfl, read_at 3 P3 rfl,
    read_at 4 P4 rfl, read_at 5 P5 rfl, read_at 6 P6 rfl, read_at 7 P7 rfl, read_at 8 P8 rfl⟩

theorem orientedVolume_cycle123 (a b c d : CartesianPoint3) :
    orientedVolume b c a d = orientedVolume a b c d := by
  simp only [orientedVolume]
  ring

theorem orientedVolume_even_closing (a b c d : CartesianPoint3) :
    orientedVolume d b a c = orientedVolume a b c d := by
  simp only [orientedVolume]
  ring

theorem arm_descriptor :
    orientedVolume P3 P4 P0 P6 = orientedVolume P0 P3 P4 P6 ∧
    descriptorOfOrientedVolume? (orientedVolume P3 P4 P0 P6) = some RS.R := by
  refine ⟨orientedVolume_cycle123 P0 P3 P4 P6, ?_⟩
  rw [descriptorOfOrientedVolume?_eq_some_R_iff, orientedVolume_cycle123 P0 P3 P4 P6, arm_volume]
  norm_num

theorem closing_descriptor :
    orientedVolume P8 P2 P0 P7 = orientedVolume P0 P2 P7 P8 ∧
    descriptorOfOrientedVolume? (orientedVolume P8 P2 P0 P7) = some RS.S := by
  refine ⟨orientedVolume_even_closing P0 P2 P7 P8, ?_⟩
  rw [descriptorOfOrientedVolume?_eq_some_S_iff, orientedVolume_even_closing P0 P2 P7 P8,
    closing_volume]
  norm_num

end TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.spatial_readback
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.real_center_paths
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.backtrack_from_42_is_duplicate
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.backtrack_from_24_is_duplicate
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.root_center_children
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.no_further_center_from_24
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.no_further_center_from_42
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.root_carbon_constitutional_tie
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.root_constitutional_shell
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.arm_direct_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.arm_via_closing_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.closing_direct_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.closing_via_arm_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.real_parent_above_backtrack
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.arm_descriptor
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels.closing_descriptor
