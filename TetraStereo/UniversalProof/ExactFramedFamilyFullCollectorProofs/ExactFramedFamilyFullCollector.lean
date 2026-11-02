import TetraStereo.UniversalProof.NextFrontier.NativeGlobalProfileInventory
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalChildMultiplicity
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalGenerationCoverage
import TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
import TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ExactFramedFamilyFullCollectorProofs.ExactFramedFamilyFullCollector

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeGlobalProfileInventory
open TetraStereo.UniversalProof.NativeChronologicalChildMultiplicity
open TetraStereo.UniversalProof.NativeChronologicalGenerationCoverage
open TetraStereo.UniversalProof.WholeFamilyChronologicalTreeDomainProofs.WholeFamilyChronologicalTreeDomain
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords

/-!
Exact equality of the two maintained production collectors with the actual
canonical-child inventory on chronological trees.

`collectCanonicalTreeAuthoritative` (uncapped) and `collectCanonicalTree` (capped)
are the maintained public collectors in `TetraStereo.OneCenter`; neither is the
archived private `FrameRuntime.collect`.  This module proves, by induction on fuel,
that each collector returns exactly `TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate` (which is `inventoryFor`), the actual
breadth-first concatenation of `RawMolecule.canonicalChildren` levels, whenever its own
terminal/budget obligations hold.

The zero/empty boundary differs deliberately between the two collectors and is proved
here as a closed family of `rfl` equations:

* `collectCanonicalTree mol 0 cap frontier = none` for *every* frontier, including `[]`;
* `collectCanonicalTreeAuthoritative mol 0 [] = some []`, but
  `collectCanonicalTreeAuthoritative mol 0 (a :: rest) = none`.

Consequently the minimal sufficient fuel bounds are distinct: the authoritative
collector needs fuel `atomCount`, while the fast collector needs `atomCount + 1`
with cap `atomCount`.  No equality at the same minimal fuel is claimed.

The two structural inputs used throughout are local child-list multiplicity
(`childrenNodup`) and child provenance (`childrenReal`); collector success, an assumed
tree witness, an assumed coverage profile, or a profile-success hypothesis are never
inputs.  `ChronologicalPhysicalTree` plus a bounded root are the only raw-domain premises.
-/

/-- The fast capped collector refuses every frontier at fuel zero, even the empty one. -/
theorem fast_fuel_zero_none (mol : RawMolecule) (cap : Nat)
    (nodes : List CanonicalBranchNode) :
    collectCanonicalTree mol 0 cap nodes = none := rfl

/-- The authoritative collector accepts the empty frontier at fuel zero. -/
theorem authoritative_fuel_zero_nil (mol : RawMolecule) :
    collectCanonicalTreeAuthoritative mol 0 [] = some [] := rfl

/-- The authoritative collector refuses a nonempty frontier at fuel zero. -/
theorem authoritative_fuel_zero_cons (mol : RawMolecule) (a : CanonicalBranchNode)
    (rest : List CanonicalBranchNode) :
    collectCanonicalTreeAuthoritative mol 0 (a :: rest) = none := rfl

/-- At positive fuel the authoritative collector accepts the empty frontier. -/
theorem authoritative_succ_nil (mol : RawMolecule) (fuel : Nat) :
    collectCanonicalTreeAuthoritative mol (fuel + 1) [] = some [] := rfl

/-- The empty frontier enumerates to the empty list at every fuel. -/
theorem enumerate_nil (mol : RawMolecule) (fuel : Nat) : TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol fuel [] = [] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate, List.flatMap_nil, List.nil_append] using ih

/-- Generic executable collector equality for the uncapped authoritative collector.
Induction on fuel with the exact zero/empty boundary: the recursion bottoms out at an
empty frontier, at which point fuel zero yields `some []`. -/
theorem collectAuthoritative_terminal (mol : RawMolecule) (fuel : Nat)
    (nodes : List CanonicalBranchNode) (terminal : advance mol fuel nodes = []) :
    collectCanonicalTreeAuthoritative mol fuel nodes = some (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol fuel nodes) := by
  induction fuel generalizing nodes with
  | zero =>
      change nodes = [] at terminal
      subst nodes
      rfl
  | succ fuel ih =>
      cases nodes with
      | nil =>
          rw [enumerate_nil mol (fuel + 1)]
          rfl
      | cons first rest =>
          have tailTerminal : advance mol fuel ((first :: rest).flatMap mol.canonicalChildren) = [] :=
            terminal
          have tail := ih ((first :: rest).flatMap mol.canonicalChildren) tailTerminal
          simp only [collectCanonicalTreeAuthoritative, Bind.bind, Option.bind, tail, TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate]

/-- Generic executable collector equality for the fast capped collector.
Because fuel zero is always `none`, one extra fuel level is required relative to the
authoritative collector: with terminal `advance mol fuel nodes = []` and a cap covering
the whole enumeration, `collectCanonicalTree mol (fuel + 1) cap nodes` is exactly
`some (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol fuel nodes)`. -/
theorem collectFast_terminal (mol : RawMolecule) (fuel cap : Nat)
    (nodes : List CanonicalBranchNode)
    (terminal : advance mol fuel nodes = [])
    (budget : (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol fuel nodes).length ≤ cap) :
    collectCanonicalTree mol (fuel + 1) cap nodes = some (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol fuel nodes) := by
  induction fuel generalizing cap nodes with
  | zero =>
      change nodes = [] at terminal
      subst nodes
      rfl
  | succ fuel ih =>
      cases nodes with
      | nil =>
          rw [enumerate_nil mol (fuel + 1)]
          rfl
      | cons first rest =>
          have total : (first :: rest).length +
              (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol fuel ((first :: rest).flatMap mol.canonicalChildren)).length ≤ cap := by
            simpa only [TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate, List.length_append] using budget
          have fits : ¬ cap < (first :: rest).length := by omega
          have tailBudget :
              (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol fuel ((first :: rest).flatMap mol.canonicalChildren)).length ≤
                cap - (first :: rest).length := by omega
          have tailTerminal : advance mol fuel ((first :: rest).flatMap mol.canonicalChildren) = [] :=
            terminal
          have tail := ih (cap - (first :: rest).length)
            ((first :: rest).flatMap mol.canonicalChildren) tailTerminal tailBudget
          simp only [collectCanonicalTree, if_neg fits, Bind.bind, Option.bind, tail, TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate]

/-- `inventory` is seeded by exactly the accepted `canonicalCenterRoot`. -/
theorem inventory_seed_root (mol : RawMolecule) (root fuel : Nat) :
    inventory mol root fuel = inventoryFor mol [canonicalCenterRoot root] fuel := rfl

/-- The authoritative collector at minimal fuel `atomCount` returns exactly the accepted
`NativeGlobalProfileInventory.inventory` on a bounded chronological tree root. -/
theorem collectAuthoritative_root_eq_inventory (mol : RawMolecule)
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom) :
    collectCanonicalTreeAuthoritative mol mol.atomCount [canonicalCenterRoot root] =
      some (inventory mol root mol.atomCount) := by
  have _ := childrenNodup
  have terminal : advance mol mol.atomCount [canonicalCenterRoot root] = [] :=
    frontier_empty_at_atomCount tree rootBound childrenReal (Nat.le_refl _)
  have result := collectAuthoritative_terminal mol mol.atomCount [canonicalCenterRoot root] terminal
  rw [enumerate_eq_inventoryFor] at result
  exact result

/-- The fast capped collector at fuel `atomCount + 1` with cap `atomCount` returns exactly the
same accepted inventory. The extra fuel level is required because fast fuel zero is `none`. -/
theorem collectFast_root_eq_inventory (mol : RawMolecule)
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom) :
    collectCanonicalTree mol (mol.atomCount + 1) mol.atomCount [canonicalCenterRoot root] =
      some (inventory mol root mol.atomCount) := by
  have terminal : advance mol mol.atomCount [canonicalCenterRoot root] = [] :=
    frontier_empty_at_atomCount tree rootBound childrenReal (Nat.le_refl _)
  have budget : (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate mol mol.atomCount [canonicalCenterRoot root]).length ≤ mol.atomCount := by
    rw [enumerate_eq_inventoryFor]
    exact inventory_length_le_atomCount tree rootBound childrenNodup childrenReal mol.atomCount
  have result := collectFast_terminal mol mol.atomCount mol.atomCount
    [canonicalCenterRoot root] terminal budget
  rw [enumerate_eq_inventoryFor] at result
  exact result

/-- Coverage: every genuinely generated node, including the center root, is a member of the
accepted atom-count inventory returned by both collectors. -/
theorem collectAuthoritative_root_covers (mol : RawMolecule)
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom)
    {node : CanonicalBranchNode} (generated : CanonicalCenterTreeNode mol root node) :
    node ∈ inventory mol root mol.atomCount :=
  generated_mem_inventory tree rootBound childrenReal generated

/-- Atom uniqueness: the returned inventory maps to pairwise-distinct physical atoms. -/
theorem collectAuthoritative_root_atoms_nodup (mol : RawMolecule)
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom) :
    ((inventory mol root mol.atomCount).map CanonicalBranchNode.atom).Nodup :=
  inventory_atoms_nodup tree rootBound childrenNodup childrenReal mol.atomCount

/-- Size bound: the returned inventory has length at most the physical atom count. -/
theorem collectAuthoritative_root_length_le_atomCount (mol : RawMolecule)
    (tree : mol.ChronologicalPhysicalTree) {root : Nat} (rootBound : root < mol.atomCount)
    (childrenNodup : ∀ parent, CanonicalCenterTreeNode mol root parent →
      (mol.canonicalChildren parent).Nodup)
    (childrenReal : ∀ parent, CanonicalCenterTreeNode mol root parent →
      ∀ child ∈ mol.canonicalChildren parent, child.provenance = .realAtom) :
    (inventory mol root mol.atomCount).length ≤ mol.atomCount :=
  inventory_length_le_atomCount tree rootBound childrenNodup childrenReal mol.atomCount

/-! ## The missing family span premise

The accepted atom-count inventory of the maintained family maps to a permutation of the full
atom index range, for every parity list (including `[]`) and every bounded discovery root. The
domain and the two local structural facts (`childrenNodup`, `childrenReal`) are derived from the
independent physical family records, never supplied as premises. -/

/-- The single missing family span premise: the accepted atom-count inventory's atom image is a
permutation of the full atom index range. No collector-success, desired-span/output,
children-Nodup/real, coverage or length premise is supplied. -/
theorem family_inventory_atoms_perm_range
    (ps : List TetrahedralInputParity) {root : Nat}
    (rootBound : root < (familyRaw ps).atomCount) :
    ((inventory (familyRaw ps) root (familyRaw ps).atomCount).map CanonicalBranchNode.atom).Perm
        (List.range (familyRaw ps).atomCount) := by
  let tree : (familyRaw ps).ChronologicalPhysicalTree := familyRaw_chronologicalPhysicalTree ps
  let childrenNodup : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) root parent →
      ((familyRaw ps).canonicalChildren parent).Nodup :=
    fun parent _ => chronological_canonicalChildren_nodup tree parent
  let childrenReal : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) root parent →
      ∀ child ∈ (familyRaw ps).canonicalChildren parent, child.provenance = .realAtom :=
    fun parent generated child member =>
      chronological_children_real tree rootBound generated
        (chronological_generated_all_real tree rootBound generated) member
  have leftNodup : ((inventory (familyRaw ps) root (familyRaw ps).atomCount).map
      CanonicalBranchNode.atom).Nodup :=
    inventory_atoms_nodup tree rootBound childrenNodup childrenReal (familyRaw ps).atomCount
  apply (List.perm_ext_iff_of_nodup leftNodup List.nodup_range).mpr
  intro atom
  constructor
  · intro member
    obtain ⟨node, nodeMember, atomEq⟩ := List.mem_map.mp member
    have nodeFlat : node ∈ (List.range (familyRaw ps).atomCount).flatMap
        (fun level => frontier (familyRaw ps) root level) := by
      exact nodeMember
    obtain ⟨level, _levelMember, frontierMember⟩ := List.mem_flatMap.mp nodeFlat
    have generated : CanonicalCenterTreeNode (familyRaw ps) root node :=
      frontier_generated frontierMember
    have real : node.provenance = .realAtom :=
      chronological_generated_all_real tree rootBound generated
    have nodeAtomBound : node.atom < (familyRaw ps).atomCount :=
      (generated.real_history rootBound tree.wellFormed real).2 node.atom
        (List.mem_of_head? generated.history_head)
    rw [← atomEq]
    exact List.mem_range.mpr nodeAtomBound
  · intro member
    have atomBound : atom < (familyRaw ps).atomCount := List.mem_range.mp member
    obtain ⟨node, generated, same⟩ := family_generated_atom_exists ps rootBound atomBound
    have nodeMember : node ∈ inventory (familyRaw ps) root (familyRaw ps).atomCount :=
      generated_mem_inventory tree rootBound childrenReal generated
    exact List.mem_map.mpr ⟨node, nodeMember, same⟩

/-- Immediate cardinality corollary: the accepted atom-count inventory has length exactly the
physical atom count, derived from the permutation above via `Perm.length_eq`. -/
theorem family_inventory_length_eq_atomCount
    (ps : List TetrahedralInputParity) {root : Nat}
    (rootBound : root < (familyRaw ps).atomCount) :
    (inventory (familyRaw ps) root (familyRaw ps).atomCount).length = (familyRaw ps).atomCount := by
  have perm := family_inventory_atoms_perm_range ps rootBound
  simpa [List.length_map, List.length_range] using perm.length_eq

/-! ## Whole-family collector entrypoints

The two maintained collectors at the actual `analysisFuel` return exactly the accepted
atom-count inventory, for every parity list (including `[]`) and every bounded discovery root.
The terminal frontier fact is derived internally from the physical family records via
`frontier_empty_at_atomCount`; no collector success/output, supplied tree, local children fact,
or desired inventory is assumed. -/

/-- Generic inventory one-step identity: appending the next frontier level is the exact
successor-step of the actual `inventory` definition. No scientific premise. -/
theorem inventory_succ_eq_append_frontier (mol : RawMolecule) (root fuel : Nat) :
    inventory mol root (fuel + 1) =
      inventory mol root fuel ++ frontier mol root fuel := by
  unfold inventory inventoryFor TetraStereo.UniversalProof.NativeGlobalProfileInventory.frontier
  rw [List.range_succ, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Whole-family inventory stabilization: at or beyond the atom-count fuel the actual inventory
is already complete, so further frontier levels contribute nothing. `tree` and the local
`childrenReal` fact are derived internally from the physical family records. -/
theorem family_inventory_stable (ps : List TetrahedralInputParity) {root : Nat}
    (rootBound : root < (familyRaw ps).atomCount) (fuel : Nat)
    (enough : (familyRaw ps).atomCount ≤ fuel) :
    inventory (familyRaw ps) root fuel =
      inventory (familyRaw ps) root (familyRaw ps).atomCount := by
  let tree : (familyRaw ps).ChronologicalPhysicalTree := familyRaw_chronologicalPhysicalTree ps
  let childrenReal : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) root parent →
      ∀ child ∈ (familyRaw ps).canonicalChildren parent, child.provenance = .realAtom :=
    fun parent generated child member =>
      chronological_children_real tree rootBound generated
        (chronological_generated_all_real tree rootBound generated) member
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  clear enough
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [Nat.add_succ, inventory_succ_eq_append_frontier]
      rw [ih]
      rw [frontier_empty_at_atomCount tree rootBound childrenReal (by omega)]
      rw [List.append_nil]

/-- Whole-family exact fuel arithmetic: `analysisFuel` (exactly `2 * atomCount + 2`) is at least
`atomCount + 1`, and its predecessor re-adds one. Unfolds only the actual definition. -/
theorem family_analysisFuel_bounds (ps : List TetrahedralInputParity) :
    (familyRaw ps).atomCount ≤ analysisFuel (familyRaw ps) - 1 ∧
    (familyRaw ps).atomCount ≤ analysisFuel (familyRaw ps) ∧
    (analysisFuel (familyRaw ps) - 1) + 1 = analysisFuel (familyRaw ps) := by
  unfold analysisFuel
  refine ⟨by omega, by omega, by omega⟩

/-- Actual authoritative family entrypoint: the maintained uncapped collector at the actual
`analysisFuel` returns exactly the accepted atom-count inventory, for every parity list and
every bounded discovery root. `tree` and `childrenReal` are derived internally. -/
theorem family_collectAuthoritative_analysisFuel (ps : List TetrahedralInputParity)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount) :
    collectCanonicalTreeAuthoritative (familyRaw ps) (analysisFuel (familyRaw ps))
      [canonicalCenterRoot root] =
        some (inventory (familyRaw ps) root (familyRaw ps).atomCount) := by
  let tree : (familyRaw ps).ChronologicalPhysicalTree := familyRaw_chronologicalPhysicalTree ps
  let childrenReal : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) root parent →
      ∀ child ∈ (familyRaw ps).canonicalChildren parent, child.provenance = .realAtom :=
    fun parent generated child member =>
      chronological_children_real tree rootBound generated
        (chronological_generated_all_real tree rootBound generated) member
  have enough : (familyRaw ps).atomCount ≤ analysisFuel (familyRaw ps) :=
    (family_analysisFuel_bounds ps).2.1
  have terminal : advance (familyRaw ps) (analysisFuel (familyRaw ps))
      [canonicalCenterRoot root] = [] :=
    frontier_empty_at_atomCount tree rootBound childrenReal enough
  have result := collectAuthoritative_terminal (familyRaw ps) (analysisFuel (familyRaw ps))
    [canonicalCenterRoot root] terminal
  rw [TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate_eq_inventoryFor] at result
  change collectCanonicalTreeAuthoritative (familyRaw ps) (analysisFuel (familyRaw ps))
    [canonicalCenterRoot root] =
      some (inventory (familyRaw ps) root (analysisFuel (familyRaw ps))) at result
  rw [family_inventory_stable ps rootBound (analysisFuel (familyRaw ps)) enough] at result
  exact result

/-- Actual fast family entrypoint for any sufficient cap: the maintained capped collector at the
actual `analysisFuel` returns exactly the accepted atom-count inventory, for any cap at least
`atomCount`. Because fast fuel `0` is `none`, `collectFast_terminal` is applied with the
predecessor fuel `analysisFuel - 1` and re-identified with `analysisFuel` via the arithmetic. -/
theorem family_collectFast_analysisFuel (ps : List TetrahedralInputParity)
    {root : Nat} (rootBound : root < (familyRaw ps).atomCount) (cap : Nat)
    (capEnough : (familyRaw ps).atomCount ≤ cap) :
    collectCanonicalTree (familyRaw ps) (analysisFuel (familyRaw ps)) cap
      [canonicalCenterRoot root] =
        some (inventory (familyRaw ps) root (familyRaw ps).atomCount) := by
  let tree : (familyRaw ps).ChronologicalPhysicalTree := familyRaw_chronologicalPhysicalTree ps
  let childrenReal : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) root parent →
      ∀ child ∈ (familyRaw ps).canonicalChildren parent, child.provenance = .realAtom :=
    fun parent generated child member =>
      chronological_children_real tree rootBound generated
        (chronological_generated_all_real tree rootBound generated) member
  let f := analysisFuel (familyRaw ps) - 1
  have f_ge_N : (familyRaw ps).atomCount ≤ f := by
    unfold f
    exact (family_analysisFuel_bounds ps).1
  have f_succ : f + 1 = analysisFuel (familyRaw ps) := by
    unfold f
    exact (family_analysisFuel_bounds ps).2.2
  have stable : inventory (familyRaw ps) root f =
      inventory (familyRaw ps) root (familyRaw ps).atomCount :=
    family_inventory_stable ps rootBound f f_ge_N
  have terminal : advance (familyRaw ps) f [canonicalCenterRoot root] = [] :=
    frontier_empty_at_atomCount tree rootBound childrenReal f_ge_N
  have budget : (TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate
      (familyRaw ps) f [canonicalCenterRoot root]).length ≤ cap := by
    rw [TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate_eq_inventoryFor]
    change (inventory (familyRaw ps) root f).length ≤ cap
    rw [stable]
    rw [family_inventory_length_eq_atomCount ps rootBound]
    exact capEnough
  have result := collectFast_terminal (familyRaw ps) f cap [canonicalCenterRoot root]
    terminal budget
  rw [f_succ] at result
  rw [TetraStereo.UniversalProof.NativeGlobalProfileInventory.enumerate_eq_inventoryFor] at result
  change collectCanonicalTree (familyRaw ps) (analysisFuel (familyRaw ps)) cap
    [canonicalCenterRoot root] =
      some (inventory (familyRaw ps) root f) at result
  rw [stable] at result
  exact result

/-! ## The actual auxiliary filter length

The literal production auxiliary selector keeps exactly those real-atom inventory nodes whose
physical atom differs from the discovery root and carries a tetrahedral annotation.  Over the
maintained family this is exactly one node per parity block other than the root's own block: the
tag carbon written by every block `j ≠ i`.  Hence its length is `ps.length - 1`, for every parity
list and every root block index `i`.  No coverage/output/tree/annotation census is supplied; the
only premises are `ps` and `i`. -/

/-- `Option.any` with `isSome` is exactly `bind` followed by `isSome`; a closed `rfl` identity. -/
theorem option_any_isSome_eq_bind_isSome {α β : Type*} (o : Option α) (f : α → Option β) :
    o.any (fun x => (f x).isSome) = (o.bind f).isSome := by
  cases o <;> rfl

/-- The literal production auxiliary selector predicate, applied to an inventory node of the
maintained family.  `node.provenance == .realAtom` is the raw `Bool` comparison actually written;
the remaining conjuncts are `node.atom != root` and `(familyRaw ps).atomAt? node.atom` carrying a
tetrahedral annotation. -/
def familyAuxPredicate (ps : List TetrahedralInputParity) (root : Nat)
    (node : CanonicalBranchNode) : Bool :=
  node.provenance == .realAtom && node.atom != root &&
    ((familyRaw ps).atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome)

/-- The literal auxiliary filter applied to the accepted atom-count inventory at the root
`tagIndex i.val`, using the exact production predicate above. -/
def familyAuxFiltered (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    List CanonicalBranchNode :=
  (inventory (familyRaw ps) (tagIndex i.val) (familyRaw ps).atomCount).filter
    (familyAuxPredicate ps (tagIndex i.val))

/-- The candidate surviving atom indices: every block tag index except `i` itself. -/
def otherTagIndices (ps : List TetrahedralInputParity) (i : Fin ps.length) : List Nat :=
  List.map (fun j => tagIndex j.val)
    ((List.finRange ps.length).filter (fun j => j.val != i.val))

/-- On a real-atom node the predicate is exactly `atom != root` together with an observed tag. -/
theorem familyAuxPredicate_real_eq (ps : List TetrahedralInputParity) (root : Nat)
    (node : CanonicalBranchNode) (real : node.provenance = .realAtom) :
    familyAuxPredicate ps root node =
      (node.atom != root && (observedTag (familyRaw ps) node.atom).isSome) := by
  unfold familyAuxPredicate observedTag
  rw [real]
  rw [option_any_isSome_eq_bind_isSome ((familyRaw ps).atomAt? node.atom) AtomSpec.tetrahedral?]
  simp

/-- `tagIndex` is injective as a function on natural indices. -/
theorem tagIndex_injective {a b : Nat} (h : tagIndex a = tagIndex b) : a = b := by
  unfold tagIndex at h
  omega

/-- Every block tag index is a valid discovery root of the maintained family. -/
theorem family_tagIndex_root_bound (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    tagIndex i.val < (familyRaw ps).atomCount := by
  rw [familyRaw_atomCount]
  unfold tagIndex
  have hlt : i.val < ps.length := i.isLt
  omega

/-- An atom carries an observed tag exactly when it is the tag index of some block. -/
theorem family_observedTag_isSome_iff (ps : List TetrahedralInputParity) (a : Nat) :
    (observedTag (familyRaw ps) a).isSome = true ↔
      ∃ j : Fin ps.length, a = tagIndex j.val := by
  constructor
  · intro h
    cases o : observedTag (familyRaw ps) a with
    | none =>
        rw [o] at h
        cases h
    | some p =>
        obtain ⟨j, hj, _⟩ := (familyRaw_observedTag_iff ps a p).mp o
        exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    have obs : observedTag (familyRaw ps) a = some ps[j.val] :=
      (familyRaw_observedTag_iff ps a ps[j.val]).mpr ⟨j, hj, rfl⟩
    rw [obs]
    rfl

/-- Every node in the accepted atom-count inventory is genuinely generated from its root. -/
theorem family_inventory_mem_generated (ps : List TetrahedralInputParity) {root : Nat}
    {node : CanonicalBranchNode}
    (h : node ∈ inventory (familyRaw ps) root (familyRaw ps).atomCount) :
    CanonicalCenterTreeNode (familyRaw ps) root node := by
  obtain ⟨level, _levelMember, frontierMember⟩ := List.mem_flatMap.mp h
  exact frontier_generated frontierMember

/-- Membership in `otherTagIndices` is exactly "a block index distinct from `i` mapped by
`tagIndex`". -/
theorem mem_otherTagIndices_iff (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (a : Nat) :
    a ∈ otherTagIndices ps i ↔ ∃ j : Fin ps.length, (j.val != i.val) = true ∧ a = tagIndex j.val := by
  unfold otherTagIndices
  constructor
  · intro h
    obtain ⟨j, hj⟩ := List.mem_map.mp h
    have jmem : j ∈ (List.finRange ps.length).filter (fun j => j.val != i.val) := hj.1
    have hne : (j.val != i.val) = true := (List.mem_filter.mp jmem).2
    exact ⟨j, hne, hj.2.symm⟩
  · rintro ⟨j, hne, ha⟩
    have jmem : j ∈ (List.finRange ps.length).filter (fun j => j.val != i.val) :=
      List.mem_filter.mpr ⟨List.mem_finRange j, hne⟩
    exact List.mem_map.mpr ⟨j, jmem, ha.symm⟩

/-- Erasing one entry from the nodup `finRange` leaves a nodup list. -/
theorem finRange_erase_nodup (n : Nat) (i : Fin n) :
    ((List.finRange n).erase i).Nodup := by
  have consNodup : (i :: (List.finRange n).erase i).Nodup :=
    (List.perm_cons_erase (List.mem_finRange i)).nodup_iff.mp (List.nodup_finRange n)
  exact (List.nodup_cons.mp consNodup).2

/-- The length of `finRange n` with one entry erased is `n - 1`. -/
theorem finRange_erase_length (n : Nat) (i : Fin n) :
    ((List.finRange n).erase i).length = n - 1 := by
  have perm : (i :: (List.finRange n).erase i).Perm (List.finRange n) :=
    (List.perm_cons_erase (List.mem_finRange i)).symm
  have lenEq := perm.length_eq
  rw [List.length_cons, List.length_finRange] at lenEq
  omega

/-- Filtering `finRange n` to the entries distinct from `i` leaves exactly `n - 1` entries. -/
theorem finRange_filter_bne_length (n : Nat) (i : Fin n) :
    ((List.finRange n).filter (fun j => j.val != i.val)).length = n - 1 := by
  have perm :
      ((List.finRange n).filter (fun j => j.val != i.val)).Perm ((List.finRange n).erase i) := by
    apply (List.perm_ext_iff_of_nodup
      ((List.nodup_finRange n).filter (fun j => j.val != i.val))
      (finRange_erase_nodup n i)).mpr
    intro j
    rw [List.mem_filter]
    constructor
    · intro h
      have different : j ≠ i := fun same => (bne_iff_ne.mp h.2) (congrArg Fin.val same)
      exact (List.mem_erase_of_ne different).mpr h.1
    · intro h
      refine ⟨List.mem_of_mem_erase h, ?_⟩
      apply bne_iff_ne.mpr
      intro same
      have eq : j = i := Fin.ext same
      subst j
      exact (List.nodup_finRange n).not_mem_erase h
  have lenEq := perm.length_eq
  rw [finRange_erase_length n i] at lenEq
  exact lenEq

/-- The surviving tag indices number `ps.length - 1`: every block except the root's own. -/
theorem otherTagIndices_length (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (otherTagIndices ps i).length = ps.length - 1 := by
  unfold otherTagIndices
  rw [List.length_map]
  exact finRange_filter_bne_length ps.length i

/-- The atoms surviving the auxiliary filter are exactly the surviving tag indices. -/
theorem family_aux_filtered_atoms_mem_iff (ps : List TetrahedralInputParity)
    (i : Fin ps.length) (a : Nat) :
    a ∈ (familyAuxFiltered ps i).map CanonicalBranchNode.atom ↔ a ∈ otherTagIndices ps i := by
  let tree : (familyRaw ps).ChronologicalPhysicalTree := familyRaw_chronologicalPhysicalTree ps
  have rootBound : tagIndex i.val < (familyRaw ps).atomCount :=
    family_tagIndex_root_bound ps i
  let childrenReal : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) (tagIndex i.val) parent →
      ∀ child ∈ (familyRaw ps).canonicalChildren parent, child.provenance = .realAtom :=
    fun parent generated child member =>
      chronological_children_real tree rootBound generated
        (chronological_generated_all_real tree rootBound generated) member
  constructor
  · intro h
    obtain ⟨node, nodeMember, atomEq⟩ := List.mem_map.mp h
    rw [familyAuxFiltered] at nodeMember
    have nodeInFilter := List.mem_filter.mp nodeMember
    have nodeInInventory : node ∈ inventory (familyRaw ps) (tagIndex i.val)
        (familyRaw ps).atomCount := nodeInFilter.1
    have predTrue : familyAuxPredicate ps (tagIndex i.val) node = true := nodeInFilter.2
    have generated : CanonicalCenterTreeNode (familyRaw ps) (tagIndex i.val) node :=
      family_inventory_mem_generated ps nodeInInventory
    have real : node.provenance = .realAtom :=
      chronological_generated_all_real tree rootBound generated
    have predSimplified :
        (node.atom != tagIndex i.val && (observedTag (familyRaw ps) node.atom).isSome) = true := by
      rw [familyAuxPredicate_real_eq ps (tagIndex i.val) node real] at predTrue
      exact predTrue
    have atomNeRoot : (node.atom != tagIndex i.val) = true :=
      (Bool.and_eq_true_iff.mp predSimplified).1
    have observedSome : (observedTag (familyRaw ps) node.atom).isSome = true :=
      (Bool.and_eq_true_iff.mp predSimplified).2
    obtain ⟨j, atomIsTag⟩ := (family_observedTag_isSome_iff ps node.atom).mp observedSome
    have nodeAtomNeRoot : node.atom ≠ tagIndex i.val := bne_iff_ne.mp atomNeRoot
    have jNeI : j.val ≠ i.val := by
      intro same
      apply nodeAtomNeRoot
      exact atomIsTag.trans (by rw [same])
    have jNeIBool : (j.val != i.val) = true := bne_iff_ne.mpr jNeI
    have nodeAtomMem : node.atom ∈ otherTagIndices ps i :=
      (mem_otherTagIndices_iff ps i node.atom).mpr ⟨j, jNeIBool, atomIsTag⟩
    rw [← atomEq]
    exact nodeAtomMem
  · intro h
    obtain ⟨j, jNeIBool, aIsTag⟩ := (mem_otherTagIndices_iff ps i a).mp h
    have jNeI : j.val ≠ i.val := bne_iff_ne.mp jNeIBool
    obtain ⟨node, generated, nodeAtom⟩ :=
      family_written_tag_generated ps j rootBound
    have nodeMember : node ∈ inventory (familyRaw ps) (tagIndex i.val)
        (familyRaw ps).atomCount :=
      generated_mem_inventory tree rootBound childrenReal generated
    have real : node.provenance = .realAtom :=
      chronological_generated_all_real tree rootBound generated
    have nodeAtomNeRoot : node.atom ≠ tagIndex i.val := by
      intro same
      apply jNeI
      exact tagIndex_injective (nodeAtom.symm.trans same)
    have predSimplified :
        (node.atom != tagIndex i.val && (observedTag (familyRaw ps) node.atom).isSome) = true := by
      refine Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩
      · exact bne_iff_ne.mpr nodeAtomNeRoot
      · have obs : observedTag (familyRaw ps) node.atom = some ps[j.val] :=
          (familyRaw_observedTag_iff ps node.atom ps[j.val]).mpr ⟨j, nodeAtom, rfl⟩
        rw [obs]
        rfl
    have predTrue : familyAuxPredicate ps (tagIndex i.val) node = true := by
      rw [familyAuxPredicate_real_eq ps (tagIndex i.val) node real]
      exact predSimplified
    have nodeInFilter : node ∈ (inventory (familyRaw ps) (tagIndex i.val)
        (familyRaw ps).atomCount).filter (familyAuxPredicate ps (tagIndex i.val)) :=
      List.mem_filter.mpr ⟨nodeMember, predTrue⟩
    have nodeInAuxFiltered : node ∈ familyAuxFiltered ps i := by
      rw [familyAuxFiltered]
      exact nodeInFilter
    exact List.mem_map.mpr ⟨node, nodeInAuxFiltered, nodeAtom.trans aIsTag.symm⟩

/-- The auxiliary-filter atom image is a permutation of the surviving tag indices. -/
theorem family_aux_filtered_atoms_perm (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ((familyAuxFiltered ps i).map CanonicalBranchNode.atom).Perm (otherTagIndices ps i) := by
  let tree : (familyRaw ps).ChronologicalPhysicalTree := familyRaw_chronologicalPhysicalTree ps
  have rootBound : tagIndex i.val < (familyRaw ps).atomCount :=
    family_tagIndex_root_bound ps i
  let childrenNodup : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) (tagIndex i.val) parent →
      ((familyRaw ps).canonicalChildren parent).Nodup :=
    fun parent _ => chronological_canonicalChildren_nodup tree parent
  let childrenReal : ∀ parent, CanonicalCenterTreeNode (familyRaw ps) (tagIndex i.val) parent →
      ∀ child ∈ (familyRaw ps).canonicalChildren parent, child.provenance = .realAtom :=
    fun parent generated child member =>
      chronological_children_real tree rootBound generated
        (chronological_generated_all_real tree rootBound generated) member
  have leftNodup : ((familyAuxFiltered ps i).map CanonicalBranchNode.atom).Nodup := by
    unfold familyAuxFiltered
    have base : ((inventory (familyRaw ps) (tagIndex i.val) (familyRaw ps).atomCount).map
        CanonicalBranchNode.atom).Nodup :=
      inventory_atoms_nodup tree rootBound childrenNodup childrenReal (familyRaw ps).atomCount
    exact base.sublist (List.Sublist.map CanonicalBranchNode.atom List.filter_sublist)
  have rightNodup : (otherTagIndices ps i).Nodup := by
    unfold otherTagIndices
    apply (List.nodup_map_iff_inj_on
      ((List.nodup_finRange ps.length).filter (fun j => j.val != i.val))).mpr
    intro a ha b hb h
    exact Fin.ext (tagIndex_injective h)
  apply (List.perm_ext_iff_of_nodup leftNodup rightNodup).mpr
  intro a
  exact family_aux_filtered_atoms_mem_iff ps i a

/-- The actual auxiliary filter has length `ps.length - 1` for every parity list and root block. -/
theorem family_aux_filter_length (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyAuxFiltered ps i).length = ps.length - 1 := by
  have perm := family_aux_filtered_atoms_perm ps i
  have lenEq := perm.length_eq
  rw [List.length_map] at lenEq
  rw [otherTagIndices_length ps i] at lenEq
  exact lenEq

end TetraStereo.UniversalProof.ExactFramedFamilyFullCollectorProofs.ExactFramedFamilyFullCollector
