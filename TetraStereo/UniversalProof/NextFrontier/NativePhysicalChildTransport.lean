import TetraStereo.UniversalProof.NextFrontier.NativeOriginFrame
import TetraStereo.OneCenter.ProductionCIPExactExpansion
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativePhysicalChildTransport

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.InteriorMethylDepthCounterexample

/-- Endpoint renaming preserves the physically written bond kind. -/
def mapBond (σ : Nat ≃ Nat) (b : RawBond) : RawBond :=
  { source := σ b.source, target := σ b.target, kind := b.kind }

def mapCopy (σ : Nat ≃ Nat) (c : Nat × Nat) : Nat × Nat := (σ c.1, c.2)

def mapNode (σ : Nat ≃ Nat) (n : CanonicalBranchNode) : CanonicalBranchNode :=
  { atom := σ n.atom, parent := σ n.parent, history := n.history.map σ,
    provenance := n.provenance }

def mapCursor (σ : Nat ≃ Nat) (c : CanonicalRerootCursor) : CanonicalRerootCursor :=
  { node := mapNode σ c.node, previous? := c.previous?.map (mapNode σ) }

/-- Independently checkable raw data. No child membership, metric, key, or output premise. -/
structure RawAutomorphism (mol : RawMolecule) (σ : Nat ≃ Nat) : Prop where
  atoms : ∀ a, mol.atomAt? (σ a) = mol.atomAt? a
  bonds : (mol.bonds.map (mapBond σ)).Perm mol.bonds

private def orderStep (u v : Nat) (acc : Nat) (b : RawBond) : Nat :=
  if b.directedConnects u v then max acc b.kind.order else acc

private theorem orderStep_comm (u v acc : Nat) (a b : RawBond) :
    orderStep u v (orderStep u v acc a) b =
      orderStep u v (orderStep u v acc b) a := by
  unfold orderStep
  split_ifs <;> simp [max_assoc, max_left_comm, max_comm]

private theorem orderStep_map (σ : Nat ≃ Nat) (u v acc : Nat) (b : RawBond) :
    orderStep (σ u) (σ v) acc (mapBond σ b) = orderStep u v acc b := by
  simp [orderStep, mapBond, RawBond.directedConnects, Bool.beq_eq_decide_eq, σ.injective.eq_iff]

private theorem fold_mapBond (σ : Nat ≃ Nat) (u v : Nat) (bs : List RawBond) :
    ∀ acc, (bs.map (mapBond σ)).foldl (orderStep (σ u) (σ v)) acc =
      bs.foldl (orderStep u v) acc := by
  induction bs with
  | nil => intro acc; rfl
  | cons b bs ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons, orderStep_map]
      exact ih _

theorem directedBondOrder_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (u v : Nat) :
    mol.directedBondOrder (σ u) (σ v) = mol.directedBondOrder u v := by
  have permFold := raw.bonds.foldl_eq' (fun a _ b _ acc =>
    orderStep_comm (σ u) (σ v) acc a b) 0
  change mol.bonds.foldl (orderStep (σ u) (σ v)) 0 =
    mol.bonds.foldl (orderStep u v) 0
  exact permFold.symm.trans (fold_mapBond σ u v mol.bonds 0)

theorem bondOrder_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (u v : Nat) :
    mol.bondOrder (σ u) (σ v) = mol.bondOrder u v := by
  simp [bondOrder, σ.injective.eq_iff, directedBondOrder_transport raw]

theorem oxido_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (u v : Nat) :
    mol.isTrigonalPyramidalOxidoRootEdge (σ u) (σ v) =
      mol.isTrigonalPyramidalOxidoRootEdge u v := by
  simp [isTrigonalPyramidalOxidoRootEdge, raw.atoms, bondOrder_transport raw]

theorem canonicalBondOrder_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (n : CanonicalBranchNode) (a : Nat) :
    mol.canonicalBondOrder (mapNode σ n) (σ a) = mol.canonicalBondOrder n a := by
  cases h : n.history with
  | nil => simp [canonicalBondOrder, mapNode, h, bondOrder_transport raw]
  | cons current tail =>
      cases tail with
      | nil => simp [canonicalBondOrder, mapNode, h, bondOrder_transport raw]
      | cons center rest =>
          cases rest with
          | nil => simp [canonicalBondOrder, mapNode, h, Bool.beq_eq_decide_eq, σ.injective.eq_iff,
              oxido_transport raw, bondOrder_transport raw]
          | cons x xs => simp [canonicalBondOrder, mapNode, h, bondOrder_transport raw]

private def seeds (mol : RawMolecule) (n : CanonicalBranchNode) (b : RawBond) :
    List (Nat × Nat) :=
  match (if b.source == n.atom then some b.target
    else if b.target == n.atom then some b.source else none) with
  | none => []
  | some next => (List.range (mol.canonicalBondOrder n next)).map fun i => (next, i)

private theorem seeds_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (n : CanonicalBranchNode) (b : RawBond) :
    seeds mol (mapNode σ n) (mapBond σ b) = (seeds mol n b).map (mapCopy σ) := by
  have sourceTest : ((mapBond σ b).source == (mapNode σ n).atom) =
      (b.source == n.atom) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    change (σ b.source = σ n.atom) ↔ b.source = n.atom
    exact σ.injective.eq_iff
  have targetTest : ((mapBond σ b).target == (mapNode σ n).atom) =
      (b.target == n.atom) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    change (σ b.target = σ n.atom) ↔ b.target = n.atom
    exact σ.injective.eq_iff
  unfold seeds
  rw [sourceTest, targetTest]
  by_cases source : b.source = n.atom
  · have present : (b.source == n.atom) = true := beq_iff_eq.mpr source
    simp only [if_pos present]
    change (List.range (mol.canonicalBondOrder (mapNode σ n) (σ b.target))).map
        (fun i => (σ b.target, i)) =
      ((List.range (mol.canonicalBondOrder n b.target)).map (fun i => (b.target, i))).map
        (mapCopy σ)
    rw [canonicalBondOrder_transport raw n b.target]
    simp only [List.map_map, mapCopy, Function.comp_def]
  · have absent : ¬ (b.source == n.atom) = true :=
      fun equal => source (beq_iff_eq.mp equal)
    by_cases target : b.target = n.atom
    · have present : (b.target == n.atom) = true := beq_iff_eq.mpr target
      simp only [if_neg absent, if_pos present]
      change (List.range (mol.canonicalBondOrder (mapNode σ n) (σ b.source))).map
          (fun i => (σ b.source, i)) =
        ((List.range (mol.canonicalBondOrder n b.source)).map (fun i => (b.source, i))).map
          (mapCopy σ)
      rw [canonicalBondOrder_transport raw n b.source]
      simp only [List.map_map, mapCopy, Function.comp_def]
    · have targetAbsent : ¬ (b.target == n.atom) = true :=
        fun equal => target (beq_iff_eq.mp equal)
      simp only [if_neg absent, if_neg targetAbsent, List.map_nil]

private theorem mapCopy_injective (σ : Nat ≃ Nat) : Function.Injective (mapCopy σ) := by
  intro a b equal
  have first : (mapCopy σ a).1 = (mapCopy σ b).1 :=
    congrArg (fun pair : Nat × Nat => pair.1) equal
  have second : (mapCopy σ a).2 = (mapCopy σ b).2 :=
    congrArg (fun pair : Nat × Nat => pair.2) equal
  exact Prod.ext (σ.injective first) second

theorem canonicalChildCopies_perm {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (n : CanonicalBranchNode) :
    ((mol.canonicalChildCopies n).map (mapCopy σ)).Perm
      (mol.canonicalChildCopies (mapNode σ n)) := by
  have seedEq : (mol.bonds.map (mapBond σ)).flatMap (seeds mol (mapNode σ n)) =
      (mol.bonds.flatMap (seeds mol n)).map (mapCopy σ) := by
    simp only [List.flatMap_map, List.map_flatMap]
    congr 1
    funext b
    exact seeds_transport raw n b
  have seedPerm := raw.bonds.flatMap_right (seeds mol (mapNode σ n))
  rw [seedEq] at seedPerm
  have erased := seedPerm.erase (σ n.parent, 0)
  simpa only [canonicalChildCopies, seeds, eraseCanonicalParentCopy_eq_erase,
    List.map_erase (mapCopy_injective σ), mapCopy, mapNode] using erased

theorem firstNatIndex_map (σ : Nat ≃ Nat) (a : Nat) (xs : List Nat) :
    firstNatIndex? (σ a) (xs.map σ) = firstNatIndex? a xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [firstNatIndex?, σ.injective.eq_iff, ih]

theorem historyDistance_transport (σ : Nat ≃ Nat) (n : CanonicalBranchNode) (a : Nat) :
    canonicalHistoryDistance (mapNode σ n) (σ a) = canonicalHistoryDistance n a := by
  change (firstNatIndex? (σ a) (n.history.map σ).reverse).getD
      ((n.history.map σ).length - 1 + 1) =
    (firstNatIndex? a n.history.reverse).getD (n.history.length - 1 + 1)
  rw [← List.map_reverse, firstNatIndex_map]
  simp only [List.length_map]

private def childOfCopy (n : CanonicalBranchNode) (copy : Nat × Nat) : CanonicalBranchNode :=
  { atom := copy.1, parent := n.atom, history := copy.1 :: n.history,
    provenance := if copy.2 != 0 then .multipleBondDuplicate n.depth
      else if n.history.contains copy.1 then .ringDuplicate (canonicalHistoryDistance n copy.1)
      else .realAtom }

private theorem contains_map (σ : Nat ≃ Nat) (xs : List Nat) (a : Nat) :
    (xs.map σ).contains (σ a) = xs.contains a := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map, σ.injective.eq_iff]
  constructor
  · rintro ⟨x, member, equal⟩
    exact equal ▸ member
  · intro member
    exact ⟨a, member, rfl⟩

private theorem childOfCopy_transport (σ : Nat ≃ Nat) (n : CanonicalBranchNode)
    (copy : Nat × Nat) :
    childOfCopy (mapNode σ n) (mapCopy σ copy) = mapNode σ (childOfCopy n copy) := by
  simp only [childOfCopy, mapCopy, historyDistance_transport]
  simp [mapNode, CanonicalBranchNode.depth]

theorem canonicalChildren_perm {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (n : CanonicalBranchNode) :
    ((mol.canonicalChildren n).map (mapNode σ)).Perm
      (mol.canonicalChildren (mapNode σ n)) := by
  have leaf : (mapNode σ n).forcedLeaf = n.forcedLeaf := rfl
  by_cases h : n.forcedLeaf = true
  · simp [canonicalChildren, leaf, h]
  · have cp := (canonicalChildCopies_perm raw n).map (childOfCopy (mapNode σ n))
    simp only [canonicalChildren, leaf, h]
    change (((mol.canonicalChildCopies n).map (childOfCopy n)).map (mapNode σ)).Perm
      ((mol.canonicalChildCopies (mapNode σ n)).map (childOfCopy (mapNode σ n)))
    have funEq : (fun c => childOfCopy (mapNode σ n) (mapCopy σ c)) =
        (fun c => mapNode σ (childOfCopy n c)) :=
      funext (childOfCopy_transport σ n)
    simpa only [List.map_map, Function.comp_def, funEq] using cp

theorem child_membership_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) (parent child : CanonicalBranchNode) :
    mapNode σ child ∈ mol.canonicalChildren (mapNode σ parent) ↔
      child ∈ mol.canonicalChildren parent := by
  rw [← (canonicalChildren_perm raw parent).mem_iff]
  constructor
  · intro member
    obtain ⟨source, hs, equal⟩ := List.mem_map.mp member
    have nodeInj : Function.Injective (mapNode σ) := by
      intro x y eq
      cases x; cases y
      simp only [mapNode, CanonicalBranchNode.mk.injEq] at eq
      obtain ⟨ha, hp, hh, hv⟩ := eq
      have histories := (List.map_injective_iff.mpr σ.injective) hh
      simp_all [σ.injective.eq_iff]
    exact nodeInj equal ▸ hs
  · intro member
    exact List.mem_map.mpr ⟨child, member, rfl⟩

theorem generated_node_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) {center : Nat} {node : CanonicalBranchNode}
    (generated : CanonicalCenterTreeNode mol center node) :
    CanonicalCenterTreeNode mol (σ center) (mapNode σ node) := by
  induction generated with
  | root => exact .root
  | @child parent child parentGenerated member ih =>
      exact .child ih ((child_membership_transport raw parent child).mpr member)

theorem generated_cursor_transport {mol : RawMolecule} {σ : Nat ≃ Nat}
    (raw : RawAutomorphism mol σ) {center : Nat} {cursor : CanonicalRerootCursor}
    (generated : CanonicalCenterRerootCursor mol center cursor) :
    CanonicalCenterRerootCursor mol (σ center) (mapCursor σ cursor) := by
  cases generated with
  | @descending parent node pg member =>
      exact .descending (generated_node_transport raw pg)
        ((child_membership_transport raw parent node).mpr member)
  | @ascending node child ng member =>
      exact .ascending (generated_node_transport raw ng)
        ((child_membership_transport raw node child).mpr member)

private theorem swap_fixed (a : Nat) (bound : 9 ≤ a) : swapMethyl a = a := by
  unfold swapMethyl
  split <;> omega

theorem swap_involutive (a : Nat) : swapMethyl (swapMethyl a) = a := by
  by_cases small : a < 9
  · interval_cases a <;> decide +kernel
  · have large : 9 ≤ a := by omega
    rw [swap_fixed a large, swap_fixed a large]

def methylEquiv : Nat ≃ Nat where
  toFun := swapMethyl
  invFun := swapMethyl
  left_inv := swap_involutive
  right_inv := swap_involutive

theorem fixture_raw_automorphism : RawAutomorphism molecule methylEquiv := by
  constructor
  · intro a
    by_cases small : a < 9
    · interval_cases a <;> decide +kernel
    · have large : 9 ≤ a := by omega
      change molecule.atomAt? (swapMethyl a) = molecule.atomAt? a
      rw [swap_fixed a large]
  · decide +kernel

theorem fixture_moves_root_fixes_center : methylEquiv 1 = 2 ∧ methylEquiv 0 = 0 := by
  decide +kernel

theorem fixture_admitted : molecule.WellFormed ∧ molecule.ValenceOK ∧
    molecule.Rule2MassesKnown := by
  refine ⟨raw_wellFormed, raw_valence, ?_⟩
  exact molecule.rule2MassesKnown?_eq_true_iff.mp (by decide +kernel)

theorem fixture_saturated_valences :
    (List.range 11).map molecule.usedValenceAt = [4,4,4,1,1,1,1,1,1,1,1] :=
  raw_saturated

theorem fixture_generated_node :
    CanonicalCenterTreeNode molecule 2 (mapNode methylEquiv tagOccurrence) :=
  generated_node_transport fixture_raw_automorphism actual_tag_generated

theorem fixture_generated_cursor :
    CanonicalCenterRerootCursor molecule 2 (mapCursor methylEquiv incoming) :=
  generated_cursor_transport fixture_raw_automorphism actual_incoming_generated

end TetraStereo.UniversalProof.NativePhysicalChildTransport
