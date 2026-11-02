import Mathlib.Data.Finset.Image
import TetraStereo.OneCenter.IUPACP93MonocyclicAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93VonBaeyerAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoFiniteEncoding

set_option autoImplicit false

/-!
# Transport of P-93 cyclic physical carriers under injective atom reindexing

The existing P-93 family carriers (`P93AuthorityClosedCycle`, the von Baeyer bridge system and the
local spiro frame) are stated over concrete `Nat` atom indices of one
`AuthoritativeChemicalInput`.  This module isolates the purely combinatorial content of an
*atom reindexing* between two sources and proves that the mechanical skeleton of each family is
carried across it exactly.

An `P93AuthorityAtomReindexing` is an injective map on atom indices together with two explicit
source-indexed compatibility hypotheses:

* `bound_iff` accounts for source and target atom bounds: a source atom is in range exactly when
  its image is in range.  This is the only place where the carrier's bound condition is
  transported; no mapped-carrier validity is assumed.
* `bond_iff` is the exact reflection of `P93AuthorityBinaryBond` on source indices that are in
  range.  Because `P93AuthorityBinaryBond` is reused verbatim, the full binary interaction
  vocabulary (covalent of any order, aromatic, delocalized, coordinate) is preserved; no
  single-bond restriction is introduced.

The transported statements are:

* `P93AuthorityClosedCycle.map_iff` — closed monocyclic carriers, arbitrary ring length, both
  directions;
* `P93AuthorityVonBaeyerSystem.mechanicallyValidFor_reindex` — arbitrary-injection transport of
  the bridge system, normalizing the mapped bridgehead order (swap bridgeheads and reverse each
  bridge interior when the mapped order is reversed).  The order-reflecting conditional coproof
  `mechanicallyValidFor_rename_iff` is retained as a separate lemma;
* `P93AuthoritySpiroSystem.mechanicallyValidFor_rename_iff` — the shared spiro center and the two
  closed ring interiors, both directions.

Support lookup for physical units and the traversal-order/length lemmas are proved alongside.
`P93AuthorityAtomReindexing.ofEnumerationChange` constructs the reindexing data from two concrete
enumerations of the same finite interaction hypergraph, using the exact encoding/relabelling laws
of `OrganicStereoFiniteEncoding`.  Source-audited policy relations (`SystemObserved`, descriptor
authorization, and so on) are deliberately *not* transported: they are source-indexed
observations, and claiming their transport without a policy compatibility hypothesis would be an
assumption, not a result.
-/

namespace TetraStereo.OneCenter

/-! ## Reindexing data -/

/-- An injective reindexing of atom labels between two authoritative sources.

`bound_iff` and `bond_iff` are stated on source indices, so no carrier-level validity is assumed
anywhere.  The bond relation is the existing `P93AuthorityBinaryBond` of the source and target;
the reindexing only has to reflect it exactly. -/
structure P93AuthorityAtomReindexing
    (source target : AuthoritativeChemicalInput) where
  /-- The atom-label map.  It need not be surjective on the ambient natural numbers. -/
  map : Nat → Nat
  /-- Distinct source atoms receive distinct target labels. -/
  injective : Function.Injective map
  /-- A source atom is in range exactly when its image is a target atom.  This is the explicit
  accounting of source bounds used by every mechanical-validity transport below. -/
  bound_iff : ∀ atom,
    atom < source.molecule.atomCount ↔ map atom < target.molecule.atomCount
  /-- Exact reflection of the existing binary constitutional relation on source indices that are
  in range.  No interaction kind is weakened or strengthened. -/
  bond_iff : ∀ left right,
    left < source.molecule.atomCount →
      right < source.molecule.atomCount →
        (P93AuthorityBinaryBond source left right ↔
          P93AuthorityBinaryBond target (map left) (map right))

/-- A reindexing that additionally reflects the canonical atom order on in-range source atoms.

The von Baeyer mechanical skeleton stores its two bridgeheads in canonical increasing order.  An
arbitrary injective relabelling does not preserve that order, so an order-reflecting transport is
stated as a separate conditional result.  The unconditional transport below instead normalizes
the mapped bridgehead order. -/
structure P93AuthorityOrderedAtomReindexing
    (source target : AuthoritativeChemicalInput) where
  /-- The underlying atom reindexing. -/
  reindexing : P93AuthorityAtomReindexing source target
  /-- Canonical order is reflected on in-range source atoms. -/
  order_iff : ∀ left right,
    left < source.molecule.atomCount →
      right < source.molecule.atomCount →
        (left < right ↔ reindexing.map left < reindexing.map right)

namespace P93AuthorityAtomReindexing

variable {source target : AuthoritativeChemicalInput}

/-- Membership form of `bound_iff`: a source atom is in range exactly when its image is. -/
theorem map_mem_range_iff (r : P93AuthorityAtomReindexing source target) (atom : Nat) :
    atom < source.molecule.atomCount ↔ r.map atom < target.molecule.atomCount :=
  r.bound_iff atom

/-- The image of a bounded source atom is a bounded target atom. -/
theorem image_bounded (r : P93AuthorityAtomReindexing source target) {atom : Nat}
    (bound : atom < source.molecule.atomCount) :
    r.map atom < target.molecule.atomCount :=
  (r.bound_iff atom).mp bound

/-- A target-bounded image comes from a bounded source atom. -/
theorem source_bounded_of_image (r : P93AuthorityAtomReindexing source target) {atom : Nat}
    (bound : r.map atom < target.molecule.atomCount) :
    atom < source.molecule.atomCount :=
  (r.bound_iff atom).mpr bound

end P93AuthorityAtomReindexing

/-! ## Reindexing physical units

A physical unit stores atom indices.  Reindexing a unit is purely representational; the family
support predicates below then transform exactly.  Finite membership sets are transported by
`Finset.image`; the family support predicates inspect only the center or the listed atoms, so no
injectivity is required for those sets. -/

namespace P93AuthorityPhysicalUnit

/-- Reindex the atom-bearing fields of a decoration-free physical unit. -/
def rename (f : Nat → Nat) : P93AuthorityPhysicalUnit → P93AuthorityPhysicalUnit
  | .atomCenter center => .atomCenter (f center)
  | .bond first second => .bond (f first) (f second)
  | .axis path => .axis (path.map f)
  | .plane members => .plane (members.image f)
  | .helix path => .helix (path.map f)
  | .polyhedron center positions => .polyhedron (f center) (positions.image f)

end P93AuthorityPhysicalUnit

/-! ## Binary bond symmetry

`P93AuthorityBinaryBond` is symmetric because the participant list may be read in either order.
This is what makes reversal of a bridge traversal a connectivity-preserving operation. -/

theorem P93AuthorityBinaryBond.symm
    {source : AuthoritativeChemicalInput} {left right : Nat}
    (bond : P93AuthorityBinaryBond source left right) :
    P93AuthorityBinaryBond source right left := by
  rcases bond with ⟨distinct, interaction, membership, kind, pair⟩
  refine ⟨distinct.symm, interaction, membership, kind, ?_⟩
  rcases pair with pair | pair
  · exact Or.inr pair
  · exact Or.inl pair

/-! ## Connected constitutional paths

`P93AuthorityConnectedPath` is the list-shaped consecutive-bond relation used by all three family
carriers.  It is exactly `List.IsChain` of the existing binary bond relation; recording that
bridge once lets the transport reuse the `List.IsChain` map/reflection API instead of re-inducting
over every family path. -/

theorem P93AuthorityConnectedPath.isChain_iff
    (source : AuthoritativeChemicalInput) (path : List Nat) :
    P93AuthorityConnectedPath source path ↔
      path.IsChain (P93AuthorityBinaryBond source) := by
  induction path with
  | nil => exact ⟨fun _ => .nil, fun _ => trivial⟩
  | cons first rest ih =>
      cases rest with
      | nil => exact ⟨fun _ => .singleton first, fun _ => trivial⟩
      | cons second remaining =>
          constructor
          · intro connected
            simp only [P93AuthorityConnectedPath] at connected
            exact .cons_cons connected.1 (ih.mp connected.2)
          · intro chain
            simp only [P93AuthorityConnectedPath]
            exact ⟨chain.rel_head, ih.mpr chain.tail⟩

/-- Transport and reflection of a connected constitutional path under an injective reindexing.

The hypothesis `bounded` restricts the exact bond reflection to the atoms actually occurring on
the path; atoms outside the path are irrelevant and need not be in range. -/
theorem P93AuthorityConnectedPath.map_iff_of_bounded
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target) {path : List Nat}
    (bounded : ∀ atom ∈ path, atom < source.molecule.atomCount) :
    P93AuthorityConnectedPath source path ↔
      P93AuthorityConnectedPath target (path.map r.map) := by
  simp only [P93AuthorityConnectedPath.isChain_iff, List.isChain_map]
  exact List.IsChain.iff_of_mem_imp
    (fun left right leftMem rightMem =>
      r.bond_iff left right (bounded left leftMem) (bounded right rightMem))

/-- Forward transport of a connected path. -/
theorem P93AuthorityConnectedPath.map_of_bounded
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target) {path : List Nat}
    (connected : P93AuthorityConnectedPath source path)
    (bounded : ∀ atom ∈ path, atom < source.molecule.atomCount) :
    P93AuthorityConnectedPath target (path.map r.map) :=
  (P93AuthorityConnectedPath.map_iff_of_bounded r bounded).mp connected

/-- Reverse transport of a connected path. -/
theorem P93AuthorityConnectedPath.of_map_of_bounded
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target) {path : List Nat}
    (mapped : P93AuthorityConnectedPath target (path.map r.map))
    (bounded : ∀ atom ∈ path, atom < source.molecule.atomCount) :
    P93AuthorityConnectedPath source path :=
  (P93AuthorityConnectedPath.map_iff_of_bounded r bounded).mpr mapped

/-- A connected path reversed is still connected: every binary bond is symmetric. -/
theorem P93AuthorityConnectedPath.reverse
    (source : AuthoritativeChemicalInput) {path : List Nat}
    (connected : P93AuthorityConnectedPath source path) :
    P93AuthorityConnectedPath source path.reverse := by
  simp only [P93AuthorityConnectedPath.isChain_iff] at connected ⊢
  rw [List.isChain_reverse]
  exact connected.imp fun _ _ bond => bond.symm

/-! ## Closed monocyclic carriers

The monocyclic carrier stores an arbitrary-length closed ring as a nodup list whose closed
traversal (`ringAtoms ++ [first]`) is a consecutive-bond path.  Reindexing acts by `List.map`, so
length and traversal order are preserved definitionally. -/

/-- A closed-ring atom list transported by a reindexing. -/
def P93AuthorityClosedCycleRename
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target) (ringAtoms : List Nat) : List Nat :=
  ringAtoms.map r.map

/-- Reindexing preserves the number of ring atoms. -/
@[simp] theorem P93AuthorityClosedCycleRename.length
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target) (ringAtoms : List Nat) :
    (P93AuthorityClosedCycleRename r ringAtoms).length = ringAtoms.length := by
  simp [P93AuthorityClosedCycleRename]

/-- Exact transportation of the closed-cycle carrier.

Both directions are proved.  The forward direction uses `bound_iff` for the ring atoms and
`bond_iff` on the two endpoints of each consecutive ring bond; the reverse direction recovers
source bounds from target bounds and reflects the closed traversal.  The ring length is
arbitrary: no per-size bound appears. -/
theorem P93AuthorityClosedCycle.map_iff
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target) (ringAtoms : List Nat) :
    P93AuthorityClosedCycle source ringAtoms ↔
      P93AuthorityClosedCycle target (ringAtoms.map r.map) := by
  constructor
  · -- Source closed cycle gives a target closed cycle.
    intro valid
    rw [P93AuthorityClosedCycle] at valid ⊢
    rcases valid with ⟨length, nodup, bounded, first, remaining, decompose, connected⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using length
    · exact (List.nodup_map_iff r.injective).mpr nodup
    · intro atom member
      rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
      exact (r.bound_iff original).mp (bounded original originalMem)
    · refine ⟨r.map first, remaining.map r.map, ?_, ?_⟩
      · rw [decompose]; rfl
      · have pathBounded : ∀ atom ∈ ringAtoms ++ [first],
            atom < source.molecule.atomCount := by
          intro atom member
          rcases List.mem_append.mp member with inRing | inLast
          · exact bounded atom inRing
          · simp only [List.mem_singleton] at inLast
            subst atom
            exact bounded first (by rw [decompose]; simp)
        have mapped :=
          P93AuthorityConnectedPath.map_of_bounded r connected pathBounded
        simpa using mapped
  · -- Target closed cycle gives back a source closed cycle.
    intro valid
    cases ringAtoms with
    | nil =>
        rw [P93AuthorityClosedCycle] at valid
        simp at valid
    | cons first remaining =>
        rw [P93AuthorityClosedCycle] at valid ⊢
        rcases valid with ⟨length, nodup, bounded, first', remaining', decompose', connected'⟩
        have sourceBounded : ∀ atom ∈ first :: remaining,
            atom < source.molecule.atomCount := by
          intro atom member
          exact (r.bound_iff atom).mpr
            (bounded (r.map atom) (List.mem_map.mpr ⟨atom, member, rfl⟩))
        have headEq : first' = r.map first := by
          have heads := congrArg List.head? decompose'
          have : r.map first = first' := by simpa using heads
          exact this.symm
        have pathBounded : ∀ atom ∈ (first :: remaining) ++ [first],
            atom < source.molecule.atomCount := by
          intro atom member
          rcases List.mem_append.mp member with inRing | inLast
          · exact sourceBounded atom inRing
          · simp only [List.mem_singleton] at inLast
            subst atom
            exact sourceBounded first (by simp)
        have targetConnected : P93AuthorityConnectedPath target
            (((first :: remaining) ++ [first]).map r.map) := by
          have reconnected := connected'
          rw [headEq] at reconnected
          simpa using reconnected
        have sourceConnected : P93AuthorityConnectedPath source
            ((first :: remaining) ++ [first]) :=
          P93AuthorityConnectedPath.of_map_of_bounded r targetConnected pathBounded
        exact ⟨by simpa using length,
          List.Nodup.of_map r.map nodup, sourceBounded,
          first, remaining, rfl, sourceConnected⟩

/-! ## von Baeyer bridge systems

A plain `rename` pushes the atom map through both bridgeheads and all three bridge interiors.
It preserves lengths, dimensions, membership support and connectivity.  Because the canonical
condition `firstBridgehead < secondBridgehead` is not preserved by an arbitrary injection, the
unconditional transport uses `renameReversed`/`reindex`, which chooses the bridgehead order from
the mapped images and reverses each bridge traversal when the order flips. -/

namespace P93AuthorityVonBaeyerSystem

/-- Reindex both bridgeheads and the three bridge interiors, preserving traversal direction. -/
def rename (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    P93AuthorityVonBaeyerSystem where
  firstBridgehead := f system.firstBridgehead
  secondBridgehead := f system.secondBridgehead
  xBridgeInternal := system.xBridgeInternal.map f
  yBridgeInternal := system.yBridgeInternal.map f
  zBridgeInternal := system.zBridgeInternal.map f

@[simp] theorem rename_firstBridgehead (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).firstBridgehead = f system.firstBridgehead := rfl

@[simp] theorem rename_secondBridgehead (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).secondBridgehead = f system.secondBridgehead := rfl

@[simp] theorem rename_xBridgeInternal (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).xBridgeInternal = system.xBridgeInternal.map f := rfl

@[simp] theorem rename_yBridgeInternal (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).yBridgeInternal = system.yBridgeInternal.map f := rfl

@[simp] theorem rename_zBridgeInternal (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).zBridgeInternal = system.zBridgeInternal.map f := rfl

/-- Reindexing preserves support: the new atom list is exactly the mapped old atom list. -/
theorem rename_atoms (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).atoms = system.atoms.map f := by
  simp [atoms]

/-- A bridge path is carried to the mapped bridge path, preserving traversal order. -/
theorem rename_bridgePath (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem)
    (internal : List Nat) :
    (system.rename f).bridgePath (internal.map f) =
      (system.bridgePath internal).map f := by
  simp [bridgePath]

/-- The `x` bridge path of the renamed system is the mapped `x` bridge path. -/
theorem rename_bridgePath_x (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).bridgePath (system.rename f).xBridgeInternal =
      (system.bridgePath system.xBridgeInternal).map f :=
  rename_bridgePath f system system.xBridgeInternal

/-- The `y` bridge path of the renamed system is the mapped `y` bridge path. -/
theorem rename_bridgePath_y (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).bridgePath (system.rename f).yBridgeInternal =
      (system.bridgePath system.yBridgeInternal).map f :=
  rename_bridgePath f system system.yBridgeInternal

/-- The `z` bridge path of the renamed system is the mapped `z` bridge path. -/
theorem rename_bridgePath_z (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).bridgePath (system.rename f).zBridgeInternal =
      (system.bridgePath system.zBridgeInternal).map f :=
  rename_bridgePath f system system.zBridgeInternal

/-- The bridge dimensions depend only on lengths, so they are preserved exactly. -/
theorem rename_dimensions (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    (system.rename f).dimensions = system.dimensions := by
  simp [dimensions]

/-- Every atom of the `x` bridge path is an atom of the system. -/
theorem xBridgePath_subset_atoms (system : P93AuthorityVonBaeyerSystem) :
    system.bridgePath system.xBridgeInternal ⊆ system.atoms := by
  intro atom member
  simp only [bridgePath, atoms, List.mem_cons, List.mem_append, List.not_mem_nil] at member ⊢
  tauto

/-- Every atom of the `y` bridge path is an atom of the system. -/
theorem yBridgePath_subset_atoms (system : P93AuthorityVonBaeyerSystem) :
    system.bridgePath system.yBridgeInternal ⊆ system.atoms := by
  intro atom member
  simp only [bridgePath, atoms, List.mem_cons, List.mem_append, List.not_mem_nil] at member ⊢
  tauto

/-- Every atom of the `z` bridge path is an atom of the system. -/
theorem zBridgePath_subset_atoms (system : P93AuthorityVonBaeyerSystem) :
    system.bridgePath system.zBridgeInternal ⊆ system.atoms := by
  intro atom member
  simp only [bridgePath, atoms, List.mem_cons, List.mem_append, List.not_mem_nil] at member ⊢
  tauto

/-- Forward transport of von Baeyer mechanical validity when the mapped bridgehead order is the
canonical one.  The source canonical order is deliberately not used: the constructor supplies
the mapped order directly, which is what the reindexing normalization computes. -/
theorem mechanicallyValidFor_rename_of_mapped_headOrder
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthorityVonBaeyerSystem)
    (headOrder : r.map system.firstBridgehead < r.map system.secondBridgehead)
    (valid : system.MechanicallyValidFor source) :
    (system.rename r.map).MechanicallyValidFor target := by
  rcases valid with ⟨_sourceHeadOrder, nodup, bounded, yPositive, yLeX, zLeY,
    xConnected, yConnected, zConnected⟩
  refine ⟨headOrder, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rename_atoms]
    exact nodup.map r.injective
  · intro atom member
    rw [rename_atoms] at member
    rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
    exact (r.bound_iff original).mp (bounded original originalMem)
  · simpa [rename] using yPositive
  · simpa [rename] using yLeX
  · simpa [rename] using zLeY
  · have mapped := P93AuthorityConnectedPath.map_of_bounded r xConnected
      (fun atom member => bounded atom (xBridgePath_subset_atoms system member))
    simpa only [rename_bridgePath_x] using mapped
  · have mapped := P93AuthorityConnectedPath.map_of_bounded r yConnected
      (fun atom member => bounded atom (yBridgePath_subset_atoms system member))
    simpa only [rename_bridgePath_y] using mapped
  · have mapped := P93AuthorityConnectedPath.map_of_bounded r zConnected
      (fun atom member => bounded atom (zBridgePath_subset_atoms system member))
    simpa only [rename_bridgePath_z] using mapped

/-- Order-reflecting conditional von Baeyer transport, both directions.

This is the audited conditional form: an arbitrary injective reindexing does not preserve the
canonical bridgehead order, so this statement explicitly requires
`P93AuthorityOrderedAtomReindexing`.  The unconditional direction is
`mechanicallyValidFor_reindex`. -/
theorem mechanicallyValidFor_rename_iff
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityOrderedAtomReindexing source target)
    (system : P93AuthorityVonBaeyerSystem) :
    system.MechanicallyValidFor source ↔
      (system.rename r.reindexing.map).MechanicallyValidFor target := by
  constructor
  · intro valid
    exact mechanicallyValidFor_rename_of_mapped_headOrder r.reindexing system
      ((r.order_iff system.firstBridgehead system.secondBridgehead
        (valid.2.2.1 _ (by simp [atoms]))
        (valid.2.2.1 _ (by simp [atoms]))).mp valid.1)
      valid
  · rintro ⟨headOrder, nodup, bounded, yPositive, yLeX, zLeY,
      xConnected, yConnected, zConnected⟩
    have sourceBounded : ∀ atom ∈ system.atoms,
        atom < source.molecule.atomCount := by
      intro atom member
      exact (r.reindexing.bound_iff atom).mpr
        (bounded (r.reindexing.map atom) (by
          rw [rename_atoms]
          exact List.mem_map.mpr ⟨atom, member, rfl⟩))
    refine ⟨?_, ?_, sourceBounded, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (r.order_iff system.firstBridgehead system.secondBridgehead
        (sourceBounded _ (by simp [atoms]))
        (sourceBounded _ (by simp [atoms]))).mpr headOrder
    · rw [rename_atoms] at nodup
      exact List.Nodup.of_map r.reindexing.map nodup
    · simpa [rename] using yPositive
    · simpa [rename] using yLeX
    · simpa [rename] using zLeY
    · have reconnected : P93AuthorityConnectedPath target
          ((system.bridgePath system.xBridgeInternal).map r.reindexing.map) := by
        simpa only [rename_bridgePath_x] using xConnected
      exact P93AuthorityConnectedPath.of_map_of_bounded r.reindexing reconnected
        (fun atom member => sourceBounded atom (xBridgePath_subset_atoms system member))
    · have reconnected : P93AuthorityConnectedPath target
          ((system.bridgePath system.yBridgeInternal).map r.reindexing.map) := by
        simpa only [rename_bridgePath_y] using yConnected
      exact P93AuthorityConnectedPath.of_map_of_bounded r.reindexing reconnected
        (fun atom member => sourceBounded atom (yBridgePath_subset_atoms system member))
    · have reconnected : P93AuthorityConnectedPath target
          ((system.bridgePath system.zBridgeInternal).map r.reindexing.map) := by
        simpa only [rename_bridgePath_z] using zConnected
      exact P93AuthorityConnectedPath.of_map_of_bounded r.reindexing reconnected
        (fun atom member => sourceBounded atom (zBridgePath_subset_atoms system member))

/-- Reindex, swap the bridgeheads and reverse every bridge interior.  This is the representation
used when the mapped bridgehead order is the reverse of the source canonical order.  Reversal
preserves each bridge length, so the `x ≥ y ≥ z` dimension constraints are untouched. -/
def renameReversed (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    P93AuthorityVonBaeyerSystem where
  firstBridgehead := f system.secondBridgehead
  secondBridgehead := f system.firstBridgehead
  xBridgeInternal := (system.xBridgeInternal.map f).reverse
  yBridgeInternal := (system.yBridgeInternal.map f).reverse
  zBridgeInternal := (system.zBridgeInternal.map f).reverse

@[simp] theorem renameReversed_firstBridgehead (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).firstBridgehead = f system.secondBridgehead := rfl

@[simp] theorem renameReversed_secondBridgehead (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).secondBridgehead = f system.firstBridgehead := rfl

@[simp] theorem renameReversed_xBridgeInternal (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).xBridgeInternal =
      (system.xBridgeInternal.map f).reverse := rfl

@[simp] theorem renameReversed_yBridgeInternal (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).yBridgeInternal =
      (system.yBridgeInternal.map f).reverse := rfl

@[simp] theorem renameReversed_zBridgeInternal (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).zBridgeInternal =
      (system.zBridgeInternal.map f).reverse := rfl

/-- The `x` bridge path after reversal is the reverse of the mapped original path. -/
theorem renameReversed_bridgePath_x (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).bridgePath (system.renameReversed f).xBridgeInternal =
      ((system.bridgePath system.xBridgeInternal).map f).reverse := by
  simp [renameReversed, bridgePath, List.reverse_append]

/-- The `y` bridge path after reversal is the reverse of the mapped original path. -/
theorem renameReversed_bridgePath_y (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).bridgePath (system.renameReversed f).yBridgeInternal =
      ((system.bridgePath system.yBridgeInternal).map f).reverse := by
  simp [renameReversed, bridgePath, List.reverse_append]

/-- The `z` bridge path after reversal is the reverse of the mapped original path. -/
theorem renameReversed_bridgePath_z (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).bridgePath (system.renameReversed f).zBridgeInternal =
      ((system.bridgePath system.zBridgeInternal).map f).reverse := by
  simp [renameReversed, bridgePath, List.reverse_append]

/-- The reversed system has the same dimensions: reversal preserves lengths. -/
theorem renameReversed_dimensions (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    (system.renameReversed f).dimensions = system.dimensions := by
  simp [dimensions]

/-- Support atoms of the reversed system are exactly the mapped support atoms. -/
theorem renameReversed_atoms_perm (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    List.Perm (system.renameReversed f).atoms (system.atoms.map f) := by
  have swap : List.Perm
      ([f system.secondBridgehead, f system.firstBridgehead] : List Nat)
      [f system.firstBridgehead, f system.secondBridgehead] :=
    List.Perm.swap' (f system.firstBridgehead) (f system.secondBridgehead)
      (List.Perm.refl [])
  have xReverse : List.Perm (system.xBridgeInternal.map f).reverse
      (system.xBridgeInternal.map f) :=
    List.reverse_perm _
  have yReverse : List.Perm (system.yBridgeInternal.map f).reverse
      (system.yBridgeInternal.map f) :=
    List.reverse_perm _
  have zReverse : List.Perm (system.zBridgeInternal.map f).reverse
      (system.zBridgeInternal.map f) :=
    List.reverse_perm _
  have step : List.Perm
      (((([f system.secondBridgehead, f system.firstBridgehead] ++
              (system.xBridgeInternal.map f).reverse) ++
              (system.yBridgeInternal.map f).reverse) ++
              (system.zBridgeInternal.map f).reverse))
      (((([f system.firstBridgehead, f system.secondBridgehead] ++
              system.xBridgeInternal.map f) ++
              system.yBridgeInternal.map f) ++
              system.zBridgeInternal.map f)) :=
    ((swap.append xReverse).append yReverse).append zReverse
  simpa [renameReversed, atoms, List.map_append] using step

/-- Membership lookup for the reversed support list. -/
theorem mem_renameReversed_atoms_iff (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) (atom : Nat) :
    atom ∈ (system.renameReversed f).atoms ↔
      ∃ original ∈ system.atoms, f original = atom := by
  rw [List.Perm.mem_iff (renameReversed_atoms_perm f system), List.mem_map]

/-- Forward transport of von Baeyer mechanical validity when the mapped bridgehead order is
reversed.  Reversal of each bridge path is connectivity-preserving because
`P93AuthorityBinaryBond` is symmetric. -/
theorem mechanicallyValidFor_renameReversed
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthorityVonBaeyerSystem)
    (headOrder : r.map system.secondBridgehead < r.map system.firstBridgehead)
    (valid : system.MechanicallyValidFor source) :
    (system.renameReversed r.map).MechanicallyValidFor target := by
  rcases valid with ⟨_sourceHeadOrder, nodup, bounded, yPositive, yLeX, zLeY,
    xConnected, yConnected, zConnected⟩
  refine ⟨headOrder, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (List.Perm.nodup_iff (renameReversed_atoms_perm r.map system)).mpr
      (nodup.map r.injective)
  · intro atom member
    rw [mem_renameReversed_atoms_iff] at member
    rcases member with ⟨original, originalMem, rfl⟩
    exact (r.bound_iff original).mp (bounded original originalMem)
  · simpa [renameReversed] using yPositive
  · simpa [renameReversed] using yLeX
  · simpa [renameReversed] using zLeY
  · have mapped := P93AuthorityConnectedPath.map_of_bounded r xConnected
      (fun atom member => bounded atom (xBridgePath_subset_atoms system member))
    have reversed := P93AuthorityConnectedPath.reverse target mapped
    simpa only [renameReversed_bridgePath_x] using reversed
  · have mapped := P93AuthorityConnectedPath.map_of_bounded r yConnected
      (fun atom member => bounded atom (yBridgePath_subset_atoms system member))
    have reversed := P93AuthorityConnectedPath.reverse target mapped
    simpa only [renameReversed_bridgePath_y] using reversed
  · have mapped := P93AuthorityConnectedPath.map_of_bounded r zConnected
      (fun atom member => bounded atom (zBridgePath_subset_atoms system member))
    have reversed := P93AuthorityConnectedPath.reverse target mapped
    simpa only [renameReversed_bridgePath_z] using reversed

/-- Normalized reindexing: keep the mapped bridgehead order when it is increasing, otherwise swap
the bridgeheads and reverse all three bridge interiors.  No order hypothesis is needed. -/
def reindex (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    P93AuthorityVonBaeyerSystem :=
  if f system.firstBridgehead < f system.secondBridgehead then
    system.rename f
  else
    system.renameReversed f

/-- Dimensions are preserved by the normalized reindexing. -/
theorem reindex_dimensions (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    (system.reindex f).dimensions = system.dimensions := by
  by_cases order : f system.firstBridgehead < f system.secondBridgehead
  · simp only [reindex, if_pos order]
    exact rename_dimensions f system
  · simp only [reindex, if_neg order]
    exact renameReversed_dimensions f system

/-- The normalized support list is a permutation of the mapped original support list. -/
theorem reindex_atoms_perm (f : Nat → Nat) (system : P93AuthorityVonBaeyerSystem) :
    List.Perm (system.reindex f).atoms (system.atoms.map f) := by
  by_cases order : f system.firstBridgehead < f system.secondBridgehead
  · simp only [reindex, if_pos order]
    rw [rename_atoms]
  · simp only [reindex, if_neg order]
    exact renameReversed_atoms_perm f system

/-- Membership lookup for the normalized support list. -/
theorem mem_reindex_atoms_iff (f : Nat → Nat)
    (system : P93AuthorityVonBaeyerSystem) (atom : Nat) :
    atom ∈ (system.reindex f).atoms ↔
      ∃ original ∈ system.atoms, f original = atom := by
  rw [List.Perm.mem_iff (reindex_atoms_perm f system), List.mem_map]

/-- Support lookup for a mapped source atom under any injective reindexing. -/
theorem map_mem_reindex_atoms_iff
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthorityVonBaeyerSystem) (atom : Nat) :
    r.map atom ∈ (system.reindex r.map).atoms ↔ atom ∈ system.atoms := by
  rw [mem_reindex_atoms_iff]
  constructor
  · rintro ⟨original, originalMem, equal⟩
    exact (r.injective equal) ▸ originalMem
  · intro member
    exact ⟨atom, member, rfl⟩

/-- Unconditional transport of von Baeyer mechanical validity under an arbitrary injective
reindexing, using the normalized representation.  No bridgehead order is assumed on the map. -/
theorem mechanicallyValidFor_reindex
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthorityVonBaeyerSystem)
    (valid : system.MechanicallyValidFor source) :
    (system.reindex r.map).MechanicallyValidFor target := by
  by_cases order : r.map system.firstBridgehead < r.map system.secondBridgehead
  · simpa only [reindex, if_pos order] using
      mechanicallyValidFor_rename_of_mapped_headOrder r system order valid
  · have distinct : r.map system.firstBridgehead ≠ r.map system.secondBridgehead := by
      intro equal
      have same : system.firstBridgehead = system.secondBridgehead := r.injective equal
      have sourceOrder : system.firstBridgehead < system.secondBridgehead := valid.1
      omega
    have reverseOrder : r.map system.secondBridgehead < r.map system.firstBridgehead := by
      omega
    simpa only [reindex, if_neg order] using
      mechanicallyValidFor_renameReversed r system reverseOrder valid

/-- Support lookup for a von Baeyer unit under the normalized reindexing. -/
theorem P93VonBaeyerUnitSupported.reindex_iff
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthorityVonBaeyerSystem) (unit : P93AuthorityPhysicalUnit) :
    P93VonBaeyerUnitSupported system unit ↔
      P93VonBaeyerUnitSupported (system.reindex r.map) (unit.rename r.map) := by
  cases unit with
  | atomCenter center =>
      simp only [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
      exact (map_mem_reindex_atoms_iff r system center).symm
  | bond first second =>
      simp only [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
      exact ⟨fun supported =>
          ⟨(map_mem_reindex_atoms_iff r system first).mpr supported.1,
            (map_mem_reindex_atoms_iff r system second).mpr supported.2⟩,
        fun supported =>
          ⟨(map_mem_reindex_atoms_iff r system first).mp supported.1,
            (map_mem_reindex_atoms_iff r system second).mp supported.2⟩⟩
  | axis path =>
      simp only [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
      constructor
      · rintro ⟨nonempty, supported⟩
        refine ⟨?_, ?_⟩
        · intro mappedEmpty
          exact nonempty (List.map_eq_nil_iff.mp mappedEmpty)
        · intro atom member
          rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
          exact (map_mem_reindex_atoms_iff r system original).mpr
            (supported original originalMem)
      · rintro ⟨nonempty, supported⟩
        refine ⟨?_, ?_⟩
        · intro empty
          exact nonempty (by simp [empty])
        · intro atom member
          exact (map_mem_reindex_atoms_iff r system atom).mp
            (supported (r.map atom) (List.mem_map.mpr ⟨atom, member, rfl⟩))
  | plane members =>
      simp [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
  | helix path =>
      simp [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
  | polyhedron center positions =>
      simp [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]

end P93AuthorityVonBaeyerSystem

/-! ## Spiro ring frames -/

namespace P93AuthoritySpiroSystem

/-- Reindex the shared spiro center and both ring interiors. -/
def rename (f : Nat → Nat) (system : P93AuthoritySpiroSystem) :
    P93AuthoritySpiroSystem where
  center := f system.center
  firstRingInternal := system.firstRingInternal.map f
  secondRingInternal := system.secondRingInternal.map f

@[simp] theorem rename_center (f : Nat → Nat) (system : P93AuthoritySpiroSystem) :
    (system.rename f).center = f system.center := rfl

@[simp] theorem rename_firstRingInternal (f : Nat → Nat)
    (system : P93AuthoritySpiroSystem) :
    (system.rename f).firstRingInternal = system.firstRingInternal.map f := rfl

@[simp] theorem rename_secondRingInternal (f : Nat → Nat)
    (system : P93AuthoritySpiroSystem) :
    (system.rename f).secondRingInternal = system.secondRingInternal.map f := rfl

/-- Reindexing preserves support: the new atom list is exactly the mapped old atom list. -/
theorem rename_atoms (f : Nat → Nat) (system : P93AuthoritySpiroSystem) :
    (system.rename f).atoms = system.atoms.map f := by
  simp [atoms]

/-- A spiro ring is carried to the mapped ring, preserving traversal order. -/
theorem rename_firstRing (f : Nat → Nat) (system : P93AuthoritySpiroSystem) :
    (system.rename f).firstRing = system.firstRing.map f := by
  simp [firstRing]

/-- A spiro ring is carried to the mapped ring, preserving traversal order. -/
theorem rename_secondRing (f : Nat → Nat) (system : P93AuthoritySpiroSystem) :
    (system.rename f).secondRing = system.secondRing.map f := by
  simp [secondRing]

/-- A closed spiro ring traversal is carried to the mapped traversal. -/
theorem rename_closedPath (f : Nat → Nat) (system : P93AuthoritySpiroSystem)
    (internal : List Nat) :
    (system.rename f).closedPath (internal.map f) =
      (system.closedPath internal).map f := by
  simp [closedPath]

/-- The first closed ring traversal of the renamed system is the mapped traversal. -/
theorem rename_closedPath_first (f : Nat → Nat) (system : P93AuthoritySpiroSystem) :
    (system.rename f).closedPath (system.rename f).firstRingInternal =
      (system.closedPath system.firstRingInternal).map f :=
  rename_closedPath f system system.firstRingInternal

/-- The second closed ring traversal of the renamed system is the mapped traversal. -/
theorem rename_closedPath_second (f : Nat → Nat) (system : P93AuthoritySpiroSystem) :
    (system.rename f).closedPath (system.rename f).secondRingInternal =
      (system.closedPath system.secondRingInternal).map f :=
  rename_closedPath f system system.secondRingInternal

/-- Every atom of the first closed ring interior is an atom of the system. -/
theorem firstClosedPath_subset_atoms (system : P93AuthoritySpiroSystem) :
    system.closedPath system.firstRingInternal ⊆ system.atoms := by
  intro atom member
  simp only [closedPath, atoms, List.mem_cons, List.mem_append, List.not_mem_nil] at member ⊢
  tauto

/-- Every atom of the second closed ring interior is an atom of the system. -/
theorem secondClosedPath_subset_atoms (system : P93AuthoritySpiroSystem) :
    system.closedPath system.secondRingInternal ⊆ system.atoms := by
  intro atom member
  simp only [closedPath, atoms, List.mem_cons, List.mem_append, List.not_mem_nil] at member ⊢
  tauto

/-- Exact transport of spiro mechanical validity.

The `Nodup` clause is what expresses that the two ring interiors meet only in the shared center;
it is transported through injectivity.  Both ring lengths are preserved by `List.length_map`, and
both closed traversals are reflected endpoint-by-endpoint through `bond_iff`. -/
theorem mechanicallyValidFor_rename_iff
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthoritySpiroSystem) :
    system.MechanicallyValidFor source ↔
      (system.rename r.map).MechanicallyValidFor target := by
  constructor
  · rintro ⟨nodup, bounded, firstLength, secondLength,
      firstConnected, secondConnected⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rename_atoms]
      exact nodup.map r.injective
    · intro atom member
      rw [rename_atoms] at member
      rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
      exact (r.bound_iff original).mp (bounded original originalMem)
    · simpa [rename] using firstLength
    · simpa [rename] using secondLength
    · have mapped := P93AuthorityConnectedPath.map_of_bounded r firstConnected
        (fun atom member => bounded atom (firstClosedPath_subset_atoms system member))
      simpa only [rename_closedPath_first] using mapped
    · have mapped := P93AuthorityConnectedPath.map_of_bounded r secondConnected
        (fun atom member => bounded atom (secondClosedPath_subset_atoms system member))
      simpa only [rename_closedPath_second] using mapped
  · rintro ⟨nodup, bounded, firstLength, secondLength,
      firstConnected, secondConnected⟩
    have sourceBounded : ∀ atom ∈ system.atoms,
        atom < source.molecule.atomCount := by
      intro atom member
      exact (r.bound_iff atom).mpr
        (bounded (r.map atom) (by
          rw [rename_atoms]
          exact List.mem_map.mpr ⟨atom, member, rfl⟩))
    refine ⟨?_, sourceBounded, ?_, ?_, ?_, ?_⟩
    · rw [rename_atoms] at nodup
      exact List.Nodup.of_map r.map nodup
    · simpa [rename] using firstLength
    · simpa [rename] using secondLength
    · have reconnected : P93AuthorityConnectedPath target
          ((system.closedPath system.firstRingInternal).map r.map) := by
        simpa only [rename_closedPath_first] using firstConnected
      exact P93AuthorityConnectedPath.of_map_of_bounded r reconnected
        (fun atom member => sourceBounded atom (firstClosedPath_subset_atoms system member))
    · have reconnected : P93AuthorityConnectedPath target
          ((system.closedPath system.secondRingInternal).map r.map) := by
        simpa only [rename_closedPath_second] using secondConnected
      exact P93AuthorityConnectedPath.of_map_of_bounded r reconnected
        (fun atom member => sourceBounded atom (secondClosedPath_subset_atoms system member))

end P93AuthoritySpiroSystem

/-! ## Support lookup under reindexing

A physical unit stores atom indices.  Reindexing a unit is purely representational; the family
support predicates then transform exactly.  These lemmas are the "support lookup" interface used
when the next layer matches units between a source carrier and its reindexed image. -/

/-- Support lookup for a von Baeyer system: a unit is supported by the original system exactly
when the reindexed unit is supported by the renamed system.  The cases `.plane`, `.helix` and
`.polyhedron` are rejected by the family support predicate on both sides. -/
theorem P93VonBaeyerUnitSupported.rename_iff
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthorityVonBaeyerSystem) (unit : P93AuthorityPhysicalUnit) :
    P93VonBaeyerUnitSupported system unit ↔
      P93VonBaeyerUnitSupported (system.rename r.map) (unit.rename r.map) := by
  cases unit with
  | atomCenter center =>
      simp only [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
      rw [P93AuthorityVonBaeyerSystem.rename_atoms]
      exact (List.mem_map_of_injective r.injective).symm
  | bond first second =>
      simp only [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
      rw [P93AuthorityVonBaeyerSystem.rename_atoms]
      exact ⟨fun supported =>
          ⟨(List.mem_map_of_injective r.injective).mpr supported.1,
            (List.mem_map_of_injective r.injective).mpr supported.2⟩,
        fun supported =>
          ⟨(List.mem_map_of_injective r.injective).mp supported.1,
            (List.mem_map_of_injective r.injective).mp supported.2⟩⟩
  | axis path =>
      simp only [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
      rw [P93AuthorityVonBaeyerSystem.rename_atoms]
      constructor
      · rintro ⟨nonempty, supported⟩
        refine ⟨?_, ?_⟩
        · intro mappedEmpty
          exact nonempty (List.map_eq_nil_iff.mp mappedEmpty)
        · intro atom member
          rcases List.mem_map.mp member with ⟨original, originalMem, rfl⟩
          exact (List.mem_map_of_injective r.injective).mpr
            (supported original originalMem)
      · rintro ⟨nonempty, supported⟩
        refine ⟨?_, ?_⟩
        · intro empty
          exact nonempty (by simp [empty])
        · intro atom member
          exact (List.mem_map_of_injective r.injective).mp
            (supported (r.map atom) (List.mem_map.mpr ⟨atom, member, rfl⟩))
  | plane members =>
      simp [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
  | helix path =>
      simp [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]
  | polyhedron center positions =>
      simp [P93VonBaeyerUnitSupported, P93AuthorityPhysicalUnit.rename]

/-- Support lookup for a spiro system.  The `.polyhedron` case inspects only the shared center,
which is matched through injectivity. -/
theorem P93SpiroUnitSupported.rename_iff
    {source target : AuthoritativeChemicalInput}
    (r : P93AuthorityAtomReindexing source target)
    (system : P93AuthoritySpiroSystem) (unit : P93AuthorityPhysicalUnit) :
    P93SpiroUnitSupported system unit ↔
      P93SpiroUnitSupported (system.rename r.map) (unit.rename r.map) := by
  cases unit with
  | atomCenter center =>
      simp only [P93SpiroUnitSupported, P93AuthorityPhysicalUnit.rename]
      rw [P93AuthoritySpiroSystem.rename_atoms]
      exact (List.mem_map_of_injective r.injective).symm
  | bond first second =>
      simp only [P93SpiroUnitSupported, P93AuthorityPhysicalUnit.rename]
      rw [P93AuthoritySpiroSystem.rename_atoms]
      exact ⟨fun supported =>
          ⟨(List.mem_map_of_injective r.injective).mpr supported.1,
            (List.mem_map_of_injective r.injective).mpr supported.2⟩,
        fun supported =>
          ⟨(List.mem_map_of_injective r.injective).mp supported.1,
            (List.mem_map_of_injective r.injective).mp supported.2⟩⟩
  | axis path =>
      simp [P93SpiroUnitSupported, P93AuthorityPhysicalUnit.rename]
  | plane members =>
      simp [P93SpiroUnitSupported, P93AuthorityPhysicalUnit.rename]
  | helix path =>
      simp [P93SpiroUnitSupported, P93AuthorityPhysicalUnit.rename]
  | polyhedron center positions =>
      simp only [P93SpiroUnitSupported, P93AuthorityPhysicalUnit.rename]
      change center = system.center ↔ r.map center = r.map system.center
      exact ⟨fun equal => congrArg r.map equal, fun equal => r.injective equal⟩

/-! ## Concrete construction from finite-encoding enumeration changes

The finite encoder maps one independent finite interaction hypergraph into `SemanticMolecule`
under a chosen enumeration of its atom type.  Changing the enumeration only renames atom indices.
The following construction turns that fact into an `P93AuthorityAtomReindexing` between the two
encoded authoritative inputs, so the transport theorems above are applicable without assuming the
bound/bond compatibility data.

The permutation is `first.symm.trans second`: a target index `i` names the same source atom as
source index `(first.symm.trans second) i`.  The total map below therefore sends a source index to
its target index, and sends out-of-range indices to a disjoint range. -/

/-- The total atom-index map induced by changing the encoding enumeration from `first` to
`second`.  Out-of-range indices are shifted by the atom count, which keeps the map injective and
makes the range reflection `bound_iff` hold. -/
def P93AuthorityAtomReindexing.mapOfEnumerationChange
    {V : Type*} [DecidableEq V] [Fintype V]
    (first second : V ≃ Fin (Fintype.card V)) (index : Nat) : Nat :=
  if bound : index < Fintype.card V then
    ((first.symm.trans second) ⟨index, bound⟩).val
  else
    index + Fintype.card V

namespace P93AuthorityAtomReindexing

/-- Value of the enumeration-change map inside the atom range. -/
theorem mapOfEnumerationChange_of_lt
    {V : Type*} [DecidableEq V] [Fintype V]
    (first second : V ≃ Fin (Fintype.card V)) {index : Nat}
    (bound : index < Fintype.card V) :
    mapOfEnumerationChange first second index =
      ((first.symm.trans second) ⟨index, bound⟩).val := by
  unfold mapOfEnumerationChange
  rw [dif_pos bound]

/-- Value of the enumeration-change map outside the atom range. -/
theorem mapOfEnumerationChange_of_not_lt
    {V : Type*} [DecidableEq V] [Fintype V]
    (first second : V ≃ Fin (Fintype.card V)) {index : Nat}
    (bound : ¬ index < Fintype.card V) :
    mapOfEnumerationChange first second index = index + Fintype.card V := by
  unfold mapOfEnumerationChange
  rw [dif_neg bound]

/-- The enumeration-change map reflects the atom range exactly. -/
theorem mapOfEnumerationChange_bound_iff
    {V : Type*} [DecidableEq V] [Fintype V]
    (first second : V ≃ Fin (Fintype.card V)) (index : Nat) :
    index < Fintype.card V ↔
      mapOfEnumerationChange first second index < Fintype.card V := by
  by_cases bound : index < Fintype.card V
  · have imageBound : mapOfEnumerationChange first second index < Fintype.card V := by
      rw [mapOfEnumerationChange_of_lt first second bound]
      exact ((first.symm.trans second) ⟨index, bound⟩).isLt
    exact ⟨fun _ => imageBound, fun _ => bound⟩
  · have imageNotBound : ¬ mapOfEnumerationChange first second index < Fintype.card V := by
      rw [mapOfEnumerationChange_of_not_lt first second bound]
      omega
    exact ⟨fun inside => absurd inside bound, fun inside => absurd inside imageNotBound⟩

/-- The enumeration-change map is injective. -/
theorem mapOfEnumerationChange_injective
    {V : Type*} [DecidableEq V] [Fintype V]
    (first second : V ≃ Fin (Fintype.card V)) :
    Function.Injective (mapOfEnumerationChange first second) := by
  intro left right equal
  by_cases leftBound : left < Fintype.card V
  · by_cases rightBound : right < Fintype.card V
    · rw [mapOfEnumerationChange_of_lt first second leftBound,
        mapOfEnumerationChange_of_lt first second rightBound] at equal
      have finEqual : (⟨left, leftBound⟩ : Fin (Fintype.card V)) =
          ⟨right, rightBound⟩ :=
        (first.symm.trans second).injective (Fin.ext equal)
      exact congrArg Fin.val finEqual
    · rw [mapOfEnumerationChange_of_lt first second leftBound,
        mapOfEnumerationChange_of_not_lt first second rightBound] at equal
      have imageBound : ((first.symm.trans second) ⟨left, leftBound⟩).val <
          Fintype.card V := ((first.symm.trans second) ⟨left, leftBound⟩).isLt
      omega
  · by_cases rightBound : right < Fintype.card V
    · rw [mapOfEnumerationChange_of_not_lt first second leftBound,
        mapOfEnumerationChange_of_lt first second rightBound] at equal
      have imageBound : ((first.symm.trans second) ⟨right, rightBound⟩).val <
          Fintype.card V := ((first.symm.trans second) ⟨right, rightBound⟩).isLt
      omega
    · rw [mapOfEnumerationChange_of_not_lt first second leftBound,
        mapOfEnumerationChange_of_not_lt first second rightBound] at equal
      omega

/-- The stored label at a target index is the stored label at the corresponding source index. -/
theorem symm_mapOfEnumerationChange
    {V : Type*} [DecidableEq V] [Fintype V]
    (first second : V ≃ Fin (Fintype.card V))
    (index : Fin (Fintype.card V))
    (imageBound : mapOfEnumerationChange first second index.val < Fintype.card V) :
    second.symm ⟨mapOfEnumerationChange first second index.val, imageBound⟩ =
      first.symm index := by
  have hmap : mapOfEnumerationChange first second index.val =
      (second (first.symm index)).val := by
    rw [mapOfEnumerationChange_of_lt first second index.isLt]
    rfl
  exact second.injective (by
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    simpa using hmap)

end P93AuthorityAtomReindexing

namespace FiniteAtomInteractionHypergraph

/-- A list whose pointwise image is a two-element list is itself a two-element list, and the
preimages are the listed values. -/
private theorem eq_pair_of_map_eq_pair
    {α : Type*} {f : α → Nat} {values : List α} {left right : Nat}
    (equal : values.map f = [left, right]) :
    ∃ first second, values = [first, second] ∧ f first = left ∧ f second = right := by
  rcases List.map_eq_cons_iff.mp equal with ⟨first, rest, valuesEq, firstEq, restMap⟩
  rcases List.map_eq_singleton_iff.mp restMap with ⟨second, restEq, secondEq⟩
  subst values
  subst rest
  exact ⟨first, second, rfl, firstEq, secondEq⟩

/-- Exact binary-bond characterization of an encoded molecule in terms of the source hyperedges
and the labels named by the enumeration indices.

No family algorithm is duplicated: the statement only unfolds `P93AuthorityBinaryBond` on the
encoded interaction list and reads the encoded participant list back. -/
theorem encode_binaryBond_iff
    {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (left right : Nat)
    (leftBound : left < Fintype.card V)
    (rightBound : right < Fintype.card V) :
    P93AuthorityBinaryBond (source.encodeAuthoritative enumeration) left right ↔
      ∃ edge ∈ source.interactions,
        P93AuthorityBinaryInteractionKind edge.2 ∧
          (edge.1 = [enumeration.symm ⟨left, leftBound⟩,
                     enumeration.symm ⟨right, rightBound⟩] ∨
           edge.1 = [enumeration.symm ⟨right, rightBound⟩,
                     enumeration.symm ⟨left, leftBound⟩]) := by
  constructor
  · intro bond
    rw [P93AuthorityBinaryBond] at bond
    rcases bond with ⟨_distinct, interaction, interactionMem, kind, pair⟩
    rw [show (source.encodeAuthoritative enumeration).molecule =
          source.encode enumeration from rfl] at interactionMem
    rw [show (source.encode enumeration).interactions =
          source.interactions.map (encodeInteraction enumeration) from rfl] at interactionMem
    rcases List.mem_map.mp interactionMem with ⟨edge, edgeMem, interactionEq⟩
    subst interaction
    refine ⟨edge, edgeMem, ?_, ?_⟩
    · simpa [encodeInteraction] using kind
    · simp only [encodeInteraction] at pair
      rcases pair with pair | pair
      · rcases eq_pair_of_map_eq_pair pair with
          ⟨first, second, edgeEq, firstEq, secondEq⟩
        have firstIdentity : first = enumeration.symm ⟨left, leftBound⟩ := by
          have finEqual : enumeration first = ⟨left, leftBound⟩ := Fin.ext firstEq
          simpa using congrArg enumeration.symm finEqual
        have secondIdentity : second = enumeration.symm ⟨right, rightBound⟩ := by
          have finEqual : enumeration second = ⟨right, rightBound⟩ := Fin.ext secondEq
          simpa using congrArg enumeration.symm finEqual
        subst first
        subst second
        exact Or.inl edgeEq
      · rcases eq_pair_of_map_eq_pair pair with
          ⟨first, second, edgeEq, firstEq, secondEq⟩
        have firstIdentity : first = enumeration.symm ⟨right, rightBound⟩ := by
          have finEqual : enumeration first = ⟨right, rightBound⟩ := Fin.ext firstEq
          simpa using congrArg enumeration.symm finEqual
        have secondIdentity : second = enumeration.symm ⟨left, leftBound⟩ := by
          have finEqual : enumeration second = ⟨left, leftBound⟩ := Fin.ext secondEq
          simpa using congrArg enumeration.symm finEqual
        subst first
        subst second
        exact Or.inr edgeEq
  · rintro ⟨edge, edgeMem, kind, edgeEq | edgeEq⟩
    · have participantNodup := source.participants_nodup edge edgeMem
      rw [edgeEq] at participantNodup
      have distinct : left ≠ right := by
        intro equal
        have labelsNe : enumeration.symm ⟨left, leftBound⟩ ≠
            enumeration.symm ⟨right, rightBound⟩ := by
          have avoids : enumeration.symm ⟨left, leftBound⟩ ∉
              [enumeration.symm ⟨right, rightBound⟩] :=
            (List.nodup_cons.mp participantNodup).1
          simpa using avoids
        exact labelsNe (congrArg enumeration.symm (Fin.ext equal))
      refine ⟨distinct, encodeInteraction enumeration edge, ?_, ?_, ?_⟩
      · simp only [encodeAuthoritative]
        exact List.mem_map.mpr ⟨edge, edgeMem, rfl⟩
      · simpa [encodeInteraction] using kind
      · left
        simp only [encodeInteraction]
        rw [edgeEq]
        simp
    · have participantNodup := source.participants_nodup edge edgeMem
      rw [edgeEq] at participantNodup
      have distinct : left ≠ right := by
        intro equal
        have labelsNe : enumeration.symm ⟨right, rightBound⟩ ≠
            enumeration.symm ⟨left, leftBound⟩ := by
          have avoids : enumeration.symm ⟨right, rightBound⟩ ∉
              [enumeration.symm ⟨left, leftBound⟩] :=
            (List.nodup_cons.mp participantNodup).1
          simpa using avoids
        exact labelsNe (congrArg enumeration.symm (Fin.ext equal.symm))
      refine ⟨distinct, encodeInteraction enumeration edge, ?_, ?_, ?_⟩
      · simp only [encodeAuthoritative]
        exact List.mem_map.mpr ⟨edge, edgeMem, rfl⟩
      · simpa [encodeInteraction] using kind
      · right
        simp only [encodeInteraction]
        rw [edgeEq]
        simp

end FiniteAtomInteractionHypergraph

/-- The atom reindexing between two encodings of the same finite interaction hypergraph under
different enumerations.  Its atom map is the induced index permutation; the bound and bond
reflection fields are proved from the exact encoding laws, not assumed. -/
def P93AuthorityAtomReindexing.ofEnumerationChange
    {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (first second : V ≃ Fin (Fintype.card V)) :
    P93AuthorityAtomReindexing
      (source.encodeAuthoritative first) (source.encodeAuthoritative second) where
  map := P93AuthorityAtomReindexing.mapOfEnumerationChange first second
  injective := P93AuthorityAtomReindexing.mapOfEnumerationChange_injective first second
  bound_iff := by
    intro index
    have sourceCount : (source.encodeAuthoritative first).molecule.atomCount =
        Fintype.card V := source.encode_atomCount first
    have targetCount : (source.encodeAuthoritative second).molecule.atomCount =
        Fintype.card V := source.encode_atomCount second
    rw [sourceCount, targetCount]
    exact P93AuthorityAtomReindexing.mapOfEnumerationChange_bound_iff first second index
  bond_iff := by
    intro left right leftBound rightBound
    have sourceCount : (source.encodeAuthoritative first).molecule.atomCount =
        Fintype.card V := source.encode_atomCount first
    have targetCount : (source.encodeAuthoritative second).molecule.atomCount =
        Fintype.card V := source.encode_atomCount second
    rw [sourceCount] at leftBound rightBound
    have imageBoundLeft : P93AuthorityAtomReindexing.mapOfEnumerationChange first second left <
        Fintype.card V :=
      (P93AuthorityAtomReindexing.mapOfEnumerationChange_bound_iff first second left).mp leftBound
    have imageBoundRight : P93AuthorityAtomReindexing.mapOfEnumerationChange first second right <
        Fintype.card V :=
      (P93AuthorityAtomReindexing.mapOfEnumerationChange_bound_iff first second right).mp rightBound
    have leftLabel : second.symm
        ⟨P93AuthorityAtomReindexing.mapOfEnumerationChange first second left,
          imageBoundLeft⟩ = first.symm ⟨left, leftBound⟩ :=
      P93AuthorityAtomReindexing.symm_mapOfEnumerationChange first second
        ⟨left, leftBound⟩ imageBoundLeft
    have rightLabel : second.symm
        ⟨P93AuthorityAtomReindexing.mapOfEnumerationChange first second right,
          imageBoundRight⟩ = first.symm ⟨right, rightBound⟩ :=
      P93AuthorityAtomReindexing.symm_mapOfEnumerationChange first second
        ⟨right, rightBound⟩ imageBoundRight
    rw [FiniteAtomInteractionHypergraph.encode_binaryBond_iff source first left right
          leftBound rightBound,
        FiniteAtomInteractionHypergraph.encode_binaryBond_iff source second
          (P93AuthorityAtomReindexing.mapOfEnumerationChange first second left)
          (P93AuthorityAtomReindexing.mapOfEnumerationChange first second right)
          imageBoundLeft imageBoundRight,
        leftLabel, rightLabel]

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93AuthorityBinaryBond.symm
assert_kernel_only TetraStereo.OneCenter.P93AuthorityConnectedPath.isChain_iff
assert_kernel_only TetraStereo.OneCenter.P93AuthorityConnectedPath.map_iff_of_bounded
assert_kernel_only TetraStereo.OneCenter.P93AuthorityConnectedPath.reverse
assert_kernel_only TetraStereo.OneCenter.P93AuthorityClosedCycle.map_iff
assert_kernel_only
  TetraStereo.OneCenter.P93AuthorityVonBaeyerSystem.mechanicallyValidFor_reindex
assert_kernel_only
  TetraStereo.OneCenter.P93AuthorityVonBaeyerSystem.mechanicallyValidFor_rename_iff
assert_kernel_only
  TetraStereo.OneCenter.P93AuthoritySpiroSystem.mechanicallyValidFor_rename_iff
assert_kernel_only TetraStereo.OneCenter.P93VonBaeyerUnitSupported.rename_iff
assert_kernel_only
  TetraStereo.OneCenter.P93AuthorityVonBaeyerSystem.P93VonBaeyerUnitSupported.reindex_iff
assert_kernel_only TetraStereo.OneCenter.P93SpiroUnitSupported.rename_iff
assert_kernel_only TetraStereo.OneCenter.FiniteAtomInteractionHypergraph.encode_binaryBond_iff
assert_kernel_only TetraStereo.OneCenter.P93AuthorityAtomReindexing.ofEnumerationChange
