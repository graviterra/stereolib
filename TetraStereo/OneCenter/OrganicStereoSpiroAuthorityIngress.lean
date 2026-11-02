import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress
import TetraStereo.OneCenter.OrganicStereoCyclicCarrierTransport

set_option autoImplicit false

/-!
# Lossless native ingress for the five P-93 spiro authority rows

This module builds a native, finite-vertex representation of the existing spiro authority carriers
and proves exact recovery.  It does not introduce a second chemical semantics:

* the spiro skeleton is the existing `P93AuthoritySpiroSystem`, with its shared center and two
  ordered ring interiors relabelled onto an arbitrary finite vertex type `V`;
* each of the five existing observation structures (`Xabcd`, `Xabab`, double bond, polyhedral,
  axial) is mirrored field for field.  Citations, descriptor families, occurrence records,
  geometries, contexts, coordination/knowledge data and optional descriptors are copied
  literally; only atom references are relabelled;
* physical units (including the polyhedral `Finset` of positions) use the existing
  `SuppliedPhysicalUnit` codec, and ordered ring/path data use the existing ordered-list codec.

The source binding is the accepted `PhysicalFrameSourceBinding`, whose graph equality is an
actual equality of encoded interaction hypergraphs.  The native system's two closed ring
traversals are therefore connected paths in that same graph, stated as
`NativeSpiroConnectedPath`; the source-side `P93AuthorityConnectedPath` is transported and
recovered exactly.

All atom bounds used by the relabelling are derived from the existing mechanical validity and
physical-unit validity predicates.  The only additional source property needed by the polyhedral
case is `SpatialIndicesWellFormed`, which is exactly the property already stored by the accepted
source binding.  No policy relation is assumed to be invariant under relabelling: validity is
recovered only at the original source and the original policy.

The result is a representation-completeness statement, not a chemical classification or a
descriptor-correctness claim.
-/

namespace TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress

open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress
open BlueBookP93
open BlueBookP93.Cyclic

/-! ## Native spiro skeleton -/

/-- The spiro skeleton over an arbitrary finite vertex type.  The field layout and the definitions
of the two rings and of the closed traversals are exactly those of the source carrier. -/
structure NativeSpiroSystem (V : Type*) where
  center : V
  firstRingInternal : List V
  secondRingInternal : List V
  deriving DecidableEq, Repr

namespace NativeSpiroSystem

variable {V : Type*}

def atoms (system : NativeSpiroSystem V) : List V :=
  system.center :: system.firstRingInternal ++ system.secondRingInternal

def firstRing (system : NativeSpiroSystem V) : List V :=
  system.center :: system.firstRingInternal

def secondRing (system : NativeSpiroSystem V) : List V :=
  system.center :: system.secondRingInternal

def closedPath (system : NativeSpiroSystem V) (internal : List V) : List V :=
  system.center :: internal ++ [system.center]

end NativeSpiroSystem

/-! ## Bounds on a source spiro system -/

/-- Every atom reference of a source spiro system is below `n`. -/
structure SpiroSystemBoundedIn (n : Nat) (system : P93AuthoritySpiroSystem) : Prop where
  centerBound : system.center < n
  firstRingBound : ∀ atom ∈ system.firstRingInternal, atom < n
  secondRingBound : ∀ atom ∈ system.secondRingInternal, atom < n

/-- The bound follows from the existing mechanical validity predicate, never from an assumption. -/
theorem spiroSystemBoundedIn_of_mechanicallyValidFor
    {source : AuthoritativeChemicalInput} {system : P93AuthoritySpiroSystem}
    (valid : system.MechanicallyValidFor source) :
    SpiroSystemBoundedIn source.molecule.atomCount system := by
  rcases valid with ⟨_nodup, atomsBounded, _firstLength, _secondLength,
    _firstConnected, _secondConnected⟩
  refine ⟨?_, ?_, ?_⟩
  · exact atomsBounded system.center (by
      rw [P93AuthoritySpiroSystem.mem_atoms_iff]
      exact Or.inl rfl)
  · intro atom hmem
    exact atomsBounded atom (by
      rw [P93AuthoritySpiroSystem.mem_atoms_iff]
      exact Or.inr (Or.inl hmem))
  · intro atom hmem
    exact atomsBounded atom (by
      rw [P93AuthoritySpiroSystem.mem_atoms_iff]
      exact Or.inr (Or.inr hmem))

/-- Membership consequence of a spiro-system bound. -/
theorem spiroSystemBoundedIn_atoms {n : Nat} {system : P93AuthoritySpiroSystem}
    (bounded : SpiroSystemBoundedIn n system) :
    ∀ atom ∈ system.atoms, atom < n := by
  intro atom hmem
  rw [P93AuthoritySpiroSystem.mem_atoms_iff] at hmem
  rcases hmem with rfl | hfirst | hsecond
  · exact bounded.centerBound
  · exact bounded.firstRingBound atom hfirst
  · exact bounded.secondRingBound atom hsecond

/-! ## Relabelling and decoding the spiro system -/

def relabelSpiroSystem {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (system : P93AuthoritySpiroSystem)
    (bounded : SpiroSystemBoundedIn n system) : NativeSpiroSystem V where
  center := decodeAtom enumeration system.center bounded.centerBound
  firstRingInternal :=
    relabelList enumeration system.firstRingInternal bounded.firstRingBound
  secondRingInternal :=
    relabelList enumeration system.secondRingInternal bounded.secondRingBound

def decodeSpiroSystem {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (native : NativeSpiroSystem V) : P93AuthoritySpiroSystem where
  center := encodeAtom enumeration native.center
  firstRingInternal := unrelabelList enumeration native.firstRingInternal
  secondRingInternal := unrelabelList enumeration native.secondRingInternal

@[simp] theorem relabelSpiroSystem_center {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (system : P93AuthoritySpiroSystem)
    (bounded : SpiroSystemBoundedIn n system) :
    (relabelSpiroSystem enumeration system bounded).center =
      decodeAtom enumeration system.center bounded.centerBound := rfl

@[simp] theorem relabelSpiroSystem_firstRingInternal {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (system : P93AuthoritySpiroSystem)
    (bounded : SpiroSystemBoundedIn n system) :
    (relabelSpiroSystem enumeration system bounded).firstRingInternal =
      relabelList enumeration system.firstRingInternal bounded.firstRingBound := rfl

@[simp] theorem relabelSpiroSystem_secondRingInternal {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (system : P93AuthoritySpiroSystem)
    (bounded : SpiroSystemBoundedIn n system) :
    (relabelSpiroSystem enumeration system bounded).secondRingInternal =
      relabelList enumeration system.secondRingInternal bounded.secondRingBound := rfl

@[simp] theorem decodeSpiroSystem_center {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (native : NativeSpiroSystem V) :
    (decodeSpiroSystem enumeration native).center =
      encodeAtom enumeration native.center := rfl

@[simp] theorem decodeSpiroSystem_firstRingInternal {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (native : NativeSpiroSystem V) :
    (decodeSpiroSystem enumeration native).firstRingInternal =
      unrelabelList enumeration native.firstRingInternal := rfl

@[simp] theorem decodeSpiroSystem_secondRingInternal {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (native : NativeSpiroSystem V) :
    (decodeSpiroSystem enumeration native).secondRingInternal =
      unrelabelList enumeration native.secondRingInternal := rfl

def decodeSpiroSystemBounded {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (native : NativeSpiroSystem V) :
    SpiroSystemBoundedIn n (decodeSpiroSystem enumeration native) where
  centerBound := encodeAtom_lt enumeration native.center
  firstRingBound := unrelabelList_bounded enumeration native.firstRingInternal
  secondRingBound := unrelabelList_bounded enumeration native.secondRingInternal

@[simp] theorem decodeSpiroSystem_relabelSpiroSystem {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (system : P93AuthoritySpiroSystem)
    (bounded : SpiroSystemBoundedIn n system) :
    decodeSpiroSystem enumeration (relabelSpiroSystem enumeration system bounded) = system := by
  obtain ⟨center, firstRingInternal, secondRingInternal⟩ := system
  simp [decodeSpiroSystem, relabelSpiroSystem, encodeAtom_decodeAtom,
    unrelabelList_relabelList]

@[simp] theorem relabelSpiroSystem_decodeSpiroSystem {V : Type*} {n : Nat}
    (enumeration : V ≃ Fin n) (native : NativeSpiroSystem V) :
    relabelSpiroSystem enumeration (decodeSpiroSystem enumeration native)
        (decodeSpiroSystemBounded enumeration native) = native := by
  obtain ⟨center, firstRingInternal, secondRingInternal⟩ := native
  simp [decodeSpiroSystem, relabelSpiroSystem, decodeAtom_encodeAtom,
    relabelList_unrelabelList]

theorem relabelSpiroSystem_injective {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (first second : P93AuthoritySpiroSystem)
    (firstBounded : SpiroSystemBoundedIn n first)
    (secondBounded : SpiroSystemBoundedIn n second)
    (equal : relabelSpiroSystem enumeration first firstBounded =
      relabelSpiroSystem enumeration second secondBounded) :
    first = second := by
  have mapped := congrArg (decodeSpiroSystem enumeration) equal
  simpa only [decodeSpiroSystem_relabelSpiroSystem] using mapped

theorem unrelabelList_injective {V : Type*} {n : Nat} (enumeration : V ≃ Fin n) :
    Function.Injective (unrelabelList enumeration) :=
  List.map_injective_iff.mpr (encodeAtom_injective enumeration)

theorem decodeSpiroSystem_injective {V : Type*} {n : Nat} (enumeration : V ≃ Fin n) :
    Function.Injective (decodeSpiroSystem enumeration) := by
  intro first second equal
  have centerEqual := congrArg P93AuthoritySpiroSystem.center equal
  have firstEqual := congrArg P93AuthoritySpiroSystem.firstRingInternal equal
  have secondEqual := congrArg P93AuthoritySpiroSystem.secondRingInternal equal
  simp only [decodeSpiroSystem] at centerEqual firstEqual secondEqual
  have centerEq := encodeAtom_injective enumeration centerEqual
  have firstEq := unrelabelList_injective enumeration firstEqual
  have secondEq := unrelabelList_injective enumeration secondEqual
  cases first
  cases second
  simp_all

/-! ## The shared source graph -/

/-- One binary bond of the shared finite source, read through the enumeration. -/
def NativeSpiroBinaryBond {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (left right : V) : Prop :=
  P93AuthorityBinaryBond binding.source
    (encodeAtom binding.enumeration left) (encodeAtom binding.enumeration right)

/-- Connected-path predicate for the shared source graph.  This is the exact native image of
`P93AuthorityConnectedPath`, with the same list shape and the same endpoints. -/
def NativeSpiroConnectedPath {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) : List V → Prop
  | [] => True
  | [_] => True
  | first :: second :: remaining =>
      NativeSpiroBinaryBond binding first second ∧
        NativeSpiroConnectedPath binding (second :: remaining)

theorem nativeSpiroConnectedPath_isChain_iff {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (path : List V) :
    NativeSpiroConnectedPath binding path ↔
      path.IsChain (NativeSpiroBinaryBond binding) := by
  induction path with
  | nil => exact ⟨fun _ => .nil, fun _ => trivial⟩
  | cons first rest ih =>
      cases rest with
      | nil => exact ⟨fun _ => .singleton first, fun _ => trivial⟩
      | cons second remaining =>
          constructor
          · intro connected
            simp only [NativeSpiroConnectedPath] at connected
            exact .cons_cons connected.1 (ih.mp connected.2)
          · intro chain
            simp only [NativeSpiroConnectedPath]
            exact ⟨chain.rel_head, ih.mpr chain.tail⟩

/-! ## Ordered-list relabelling lemmas -/

section OrderedListRelabel

variable {V : Type*} {n : Nat}

/-- The pmap normal form of `relabelList`; this is the form used by the Mathlib chain API. -/
theorem relabelList_eq_pmap (enumeration : V ≃ Fin n) (values : List Nat)
    (bounded : ∀ value ∈ values, value < n) :
    relabelList enumeration values bounded =
      values.pmap
        (fun value h => decodeAtom enumeration value (bounded value h))
        (fun _ => id) :=
  List.map_attach_eq_pmap

/-- The decoded atom depends only on the value, not on the particular proof of its range. -/
theorem decodeAtom_proof_irrel (enumeration : V ≃ Fin n) (value : Nat)
    (first second : value < n) :
    decodeAtom enumeration value first = decodeAtom enumeration value second := by
  simp [decodeAtom]

@[simp] theorem relabelList_cons (enumeration : V ≃ Fin n) (value : Nat)
    (values : List Nat) (bounded : ∀ atom ∈ value :: values, atom < n) :
    relabelList enumeration (value :: values) bounded =
      decodeAtom enumeration value (bounded value (List.mem_cons_self ..)) ::
        relabelList enumeration values
          (fun atom hmem => bounded atom (List.mem_cons_of_mem value hmem)) := by
  simp only [relabelList, List.attach_cons, List.map_cons, List.map_map]
  apply congrArg (List.cons _)
  apply List.map_congr_left
  intro value _
  rfl

@[simp] theorem relabelList_append (enumeration : V ≃ Fin n)
    (first second : List Nat) (bounded : ∀ atom ∈ first ++ second, atom < n) :
    relabelList enumeration (first ++ second) bounded =
      relabelList enumeration first
          (fun atom hmem => bounded atom (List.mem_append_left second hmem)) ++
        relabelList enumeration second
          (fun atom hmem => bounded atom (List.mem_append_right first hmem)) := by
  simp only [relabelList, List.attach_append, List.map_append, List.map_map]
  exact congrArg₂ List.append
    (List.map_congr_left (fun value _ => rfl))
    (List.map_congr_left (fun value _ => rfl))

@[simp] theorem relabelList_nil (enumeration : V ≃ Fin n)
    (bounded : ∀ atom ∈ ([] : List Nat), atom < n) :
    relabelList enumeration [] bounded = [] := rfl

/-- Changing the bound proofs of a list relabelling does not change the result. -/
theorem relabelList_congr (enumeration : V ≃ Fin n) (values : List Nat)
    (first second : ∀ value ∈ values, value < n) :
    relabelList enumeration values first = relabelList enumeration values second := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      exact (relabelList_cons enumeration value rest first).trans
        ((congrArg
          (List.cons
            (decodeAtom enumeration value
              (first value (List.mem_cons_self ..))))
          (ih (fun atom hmem => first atom (List.mem_cons_of_mem value hmem))
            (fun atom hmem => second atom (List.mem_cons_of_mem value hmem)))).trans
          (relabelList_cons enumeration value rest second).symm)

theorem decodeAtom_injective_on (enumeration : V ≃ Fin n) {first second : Nat}
    (firstBound : first < n) (secondBound : second < n)
    (equal : decodeAtom enumeration first firstBound =
      decodeAtom enumeration second secondBound) :
    first = second := by
  have encoded := congrArg (encodeAtom enumeration) equal
  simpa only [encodeAtom_decodeAtom] using encoded

theorem relabelList_nodup_iff (enumeration : V ≃ Fin n) (values : List Nat)
    (bounded : ∀ value ∈ values, value < n) :
    (relabelList enumeration values bounded).Nodup ↔ values.Nodup := by
  unfold relabelList
  constructor
  · intro nodup
    exact List.Nodup.of_attach
      (List.Nodup.of_map
        (fun value : { value // value ∈ values } =>
          decodeAtom enumeration value.1 (bounded value.1 value.2)) nodup)
  · intro nodup
    have attached : values.attach.Nodup := List.nodup_attach.mpr nodup
    exact List.Nodup.map_on
      (f := fun value : { value // value ∈ values } =>
        decodeAtom enumeration value.1 (bounded value.1 value.2))
      (fun first _ second _ equal =>
        Subtype.ext
          (decodeAtom_injective_on enumeration
            (bounded first.1 first.2) (bounded second.1 second.2) equal))
      attached

end OrderedListRelabel

/-! ## Connectivity transport through the enumeration -/

theorem nativeSpiroConnectedPath_relabelList_iff {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (values : List Nat)
    (bounded : ∀ value ∈ values, value < Fintype.card V) :
    NativeSpiroConnectedPath binding
        (relabelList binding.enumeration values bounded) ↔
      P93AuthorityConnectedPath binding.source values := by
  rw [relabelList_eq_pmap]
  rw [nativeSpiroConnectedPath_isChain_iff,
    P93AuthorityConnectedPath.isChain_iff]
  rw [List.isChain_pmap
    (f := fun value h =>
      decodeAtom binding.enumeration value (bounded value h))
    (hl := fun _ => id)]
  exact List.IsChain.iff_of_mem_imp
    (fun left right leftMem rightMem => by
      constructor
      · rintro ⟨_leftProof, _rightProof, bond⟩
        simpa [NativeSpiroBinaryBond] using bond
      · intro bond
        exact ⟨leftMem, rightMem, by
          simpa [NativeSpiroBinaryBond] using bond⟩)

theorem nativeSpiroConnectedPath_unrelabelList_iff {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (values : List V) :
    NativeSpiroConnectedPath binding values ↔
      P93AuthorityConnectedPath binding.source
        (unrelabelList binding.enumeration values) := by
  rw [nativeSpiroConnectedPath_isChain_iff,
    P93AuthorityConnectedPath.isChain_iff]
  rw [unrelabelList, List.isChain_map (encodeAtom binding.enumeration)]
  rfl

/-! ## Skeleton recovery and graph validity -/

theorem relabelSpiroSystem_atoms {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (system : P93AuthoritySpiroSystem) (bounded : SpiroSystemBoundedIn n system) :
    (relabelSpiroSystem enumeration system bounded).atoms =
      relabelList enumeration system.atoms
        (spiroSystemBoundedIn_atoms bounded) := by
  simp only [NativeSpiroSystem.atoms, P93AuthoritySpiroSystem.atoms,
    relabelSpiroSystem, relabelList, List.attach_append, List.attach_cons,
    List.map_append, List.map_cons, List.map_map]
  apply congrArg (List.cons _)
  exact congrArg₂ List.append
    (List.map_congr_left (fun value _ => rfl))
    (List.map_congr_left (fun value _ => rfl))

theorem decodeSpiroSystem_atoms {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (native : NativeSpiroSystem V) :
    (decodeSpiroSystem enumeration native).atoms =
      unrelabelList enumeration native.atoms := by
  simp [P93AuthoritySpiroSystem.atoms, NativeSpiroSystem.atoms,
    decodeSpiroSystem, unrelabelList]

theorem relabelSpiroSystem_closedPath {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (system : P93AuthoritySpiroSystem) (bounded : SpiroSystemBoundedIn n system)
    (internal : List Nat) (internalBounded : ∀ atom ∈ internal, atom < n)
    (closedBounded : ∀ atom ∈ system.closedPath internal, atom < n) :
    (relabelSpiroSystem enumeration system bounded).closedPath
        (relabelList enumeration internal internalBounded) =
      relabelList enumeration (system.closedPath internal) closedBounded := by
  simp only [NativeSpiroSystem.closedPath, P93AuthoritySpiroSystem.closedPath,
    relabelSpiroSystem]
  rw [relabelList_append, relabelList_cons, relabelList_cons, relabelList_nil]

theorem decodeSpiroSystem_closedPath {V : Type*} {n : Nat} (enumeration : V ≃ Fin n)
    (native : NativeSpiroSystem V) (internal : List V) :
    (decodeSpiroSystem enumeration native).closedPath
        (unrelabelList enumeration internal) =
      unrelabelList enumeration (native.closedPath internal) := by
  simp [P93AuthoritySpiroSystem.closedPath, NativeSpiroSystem.closedPath,
    decodeSpiroSystem, unrelabelList]

/-- Native mechanical validity of a spiro skeleton, stated entirely against the shared source
graph.  The two closed ring traversals must be actual connected paths of that graph. -/
def NativeSpiroSystem.GraphValid {V : Type*} [DecidableEq V] [Fintype V]
    (system : NativeSpiroSystem V) (binding : PhysicalFrameSourceBinding V) : Prop :=
  system.atoms.Nodup ∧
    2 ≤ system.firstRingInternal.length ∧
    2 ≤ system.secondRingInternal.length ∧
    NativeSpiroConnectedPath binding
      (system.closedPath system.firstRingInternal) ∧
    NativeSpiroConnectedPath binding
      (system.closedPath system.secondRingInternal)

theorem spiroSystemBoundedIn_of_mechanicallyValidFor_card {V : Type*}
    [DecidableEq V] [Fintype V] (binding : PhysicalFrameSourceBinding V)
    (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor binding.source) :
    SpiroSystemBoundedIn (Fintype.card V) system := by
  rcases valid with ⟨_nodup, atomsBounded, _firstLength, _secondLength,
    _firstConnected, _secondConnected⟩
  have atomsBounded' : ∀ atom ∈ system.atoms, atom < Fintype.card V := by
    intro atom hmem
    rw [← binding.atomCount_eq]
    exact atomsBounded atom hmem
  refine ⟨?_, ?_, ?_⟩
  · exact atomsBounded' system.center (by
      rw [P93AuthoritySpiroSystem.mem_atoms_iff]
      exact Or.inl rfl)
  · intro atom hmem
    exact atomsBounded' atom (by
      rw [P93AuthoritySpiroSystem.mem_atoms_iff]
      exact Or.inr (Or.inl hmem))
  · intro atom hmem
    exact atomsBounded' atom (by
      rw [P93AuthoritySpiroSystem.mem_atoms_iff]
      exact Or.inr (Or.inr hmem))

/-- Forward transport: a mechanically valid source system becomes a graph-valid native system. -/
theorem relabelSpiroSystem_graphValid {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (system : P93AuthoritySpiroSystem)
    (valid : system.MechanicallyValidFor binding.source) :
    (relabelSpiroSystem binding.enumeration system
      (spiroSystemBoundedIn_of_mechanicallyValidFor_card binding system valid)).GraphValid
      binding := by
  have systemBounded :=
    spiroSystemBoundedIn_of_mechanicallyValidFor_card binding system valid
  change (relabelSpiroSystem binding.enumeration system systemBounded).GraphValid binding
  have atomsBounded : ∀ atom ∈ system.atoms, atom < Fintype.card V :=
    spiroSystemBoundedIn_atoms systemBounded
  have firstClosedBounded :
      ∀ atom ∈ system.closedPath system.firstRingInternal, atom < Fintype.card V :=
    fun atom hmem =>
      atomsBounded atom
        (P93AuthoritySpiroSystem.firstClosedPath_subset_atoms system hmem)
  have secondClosedBounded :
      ∀ atom ∈ system.closedPath system.secondRingInternal, atom < Fintype.card V :=
    fun atom hmem =>
      atomsBounded atom
        (P93AuthoritySpiroSystem.secondClosedPath_subset_atoms system hmem)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [relabelSpiroSystem_atoms binding.enumeration system systemBounded]
    exact (relabelList_nodup_iff binding.enumeration system.atoms
      (spiroSystemBoundedIn_atoms systemBounded)).mpr valid.1
  · simpa [relabelSpiroSystem] using valid.2.2.1
  · simpa [relabelSpiroSystem] using valid.2.2.2.1
  · rw [relabelSpiroSystem_firstRingInternal]
    rw [relabelSpiroSystem_closedPath binding.enumeration system systemBounded
      system.firstRingInternal systemBounded.firstRingBound firstClosedBounded]
    exact (nativeSpiroConnectedPath_relabelList_iff binding
      (system.closedPath system.firstRingInternal) firstClosedBounded).mpr
        valid.2.2.2.2.1
  · rw [relabelSpiroSystem_secondRingInternal]
    rw [relabelSpiroSystem_closedPath binding.enumeration system systemBounded
      system.secondRingInternal systemBounded.secondRingBound secondClosedBounded]
    exact (nativeSpiroConnectedPath_relabelList_iff binding
      (system.closedPath system.secondRingInternal) secondClosedBounded).mpr
        valid.2.2.2.2.2

/-- Recovery: a graph-valid native skeleton decodes to a mechanically valid source system. -/
theorem decodeSpiroSystem_mechanicallyValidFor {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (native : NativeSpiroSystem V)
    (valid : native.GraphValid binding) :
    (decodeSpiroSystem binding.enumeration native).MechanicallyValidFor binding.source := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [decodeSpiroSystem_atoms]
    exact valid.1.map (encodeAtom_injective binding.enumeration)
  · intro atom hmem
    rw [decodeSpiroSystem_atoms] at hmem
    rw [binding.atomCount_eq]
    exact unrelabelList_bounded binding.enumeration native.atoms atom hmem
  · simpa [decodeSpiroSystem] using valid.2.1
  · simpa [decodeSpiroSystem] using valid.2.2.1
  · rw [decodeSpiroSystem_firstRingInternal]
    rw [decodeSpiroSystem_closedPath binding.enumeration native
      native.firstRingInternal]
    exact (nativeSpiroConnectedPath_unrelabelList_iff binding
      (native.closedPath native.firstRingInternal)).mp valid.2.2.2.1
  · rw [decodeSpiroSystem_secondRingInternal]
    rw [decodeSpiroSystem_closedPath binding.enumeration native
      native.secondRingInternal]
    exact (nativeSpiroConnectedPath_unrelabelList_iff binding
      (native.closedPath native.secondRingInternal)).mp valid.2.2.2.2

/-! ## Bounds for physical units -/

/-- Every atom reference of a valid physical unit is below the shared vertex count.  The
polyhedral case uses the existing frame bound theorem together with the source's spatial
well-formedness, which is exactly the property carried by the accepted source binding. -/
theorem physicalUnitBoundedIn_of_validFor_card {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93AuthorityPhysicalObservationPolicy)
    (binding : PhysicalFrameSourceBinding V)
    (unit : P93AuthorityPhysicalUnit)
    (valid : unit.ValidFor policy binding.source) :
    P93AuthorityPhysicalUnit.BoundedIn (Fintype.card V) unit := by
  cases unit with
  | atomCenter center =>
      exact show center < Fintype.card V by
        rw [← binding.atomCount_eq]
        exact valid.1
  | bond first second =>
      exact
        ⟨show first < Fintype.card V by
            rw [← binding.atomCount_eq]
            exact valid.1,
          show second < Fintype.card V by
            rw [← binding.atomCount_eq]
            exact valid.2.1⟩
  | axis path =>
      intro atom hmem
      rw [← binding.atomCount_eq]
      exact valid.2.1 atom hmem
  | plane members =>
      rcases valid with ⟨frame, frameValid, _observed⟩
      have bounded :=
        planeFrameBoundedIn_of_validFor binding.source members frame frameValid
      intro atom hmem
      have listMem : atom ∈ frame.record.planeAtoms := by
        rw [← List.mem_toFinset, frameValid.1]
        exact hmem
      rw [← binding.atomCount_eq]
      exact bounded.planeAtomsBound atom listMem
  | helix path =>
      rcases valid with ⟨frame, frameValid, _observed⟩
      have bounded :=
        helixFrameBoundedIn_of_validFor binding.source path frame frameValid
      intro atom hmem
      rw [← binding.atomCount_eq]
      rw [← frameValid.1] at hmem
      exact bounded.pathBound atom hmem
  | polyhedron center positions =>
      rcases valid with ⟨geometry, frame, frameValid, _observed⟩
      have bounded :=
        polyhedralFrameBoundedIn_of_validFor binding.source center positions
          geometry frame frameValid binding.spatial_wellFormed
      refine ⟨?_, ?_⟩
      · rw [← binding.atomCount_eq]
        rw [← frameValid.1]
        exact bounded.centerBound
      · intro atom hmem
        have listMem : atom ∈ frame.record.ligands := by
          rw [← List.mem_toFinset, frameValid.2.1]
          exact hmem
        rw [← binding.atomCount_eq]
        exact bounded.ligandsBound atom listMem

/-! ## Native mirrors of the five authority observations -/

structure NativeSpiroXabcdObservation (policy : P93SpiroAuthorityPolicy) (V : Type*) where
  system : NativeSpiroSystem V
  citation : P93AuthorityCitationToken
  descriptor : BlueBookP93.Acyclic.Descriptor

structure NativeSpiroXababObservation (policy : P93SpiroAuthorityPolicy) (V : Type*) where
  system : NativeSpiroSystem V
  citation : P93AuthorityCitationToken
  family : SpiroDescriptorFamily
  occurrenceOrder : XababOccurrenceOrder
  descriptor : BlueBookP93.Acyclic.Descriptor

structure NativeSpiroDoubleBondObservation (policy : P93SpiroAuthorityPolicy) (V : Type*) where
  system : NativeSpiroSystem V
  unit : SuppliedPhysicalUnit V
  ring : List V
  citation : P93AuthorityCitationToken
  geometry : MonocyclicSeniorLigandGeometry
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

structure NativeSpiroPolyhedralObservation (policy : P93SpiroAuthorityPolicy) (V : Type*) where
  system : NativeSpiroSystem V
  unit : SuppliedPhysicalUnit V
  citation : P93AuthorityCitationToken
  coordination : SpiroCenterCoordination
  knowledge : ConfigurationKnowledge
  descriptor : PolyhedralChiralitySymbol

structure NativeSpiroAxialObservation (policy : P93SpiroAuthorityPolicy) (V : Type*) where
  system : NativeSpiroSystem V
  citation : P93AuthorityCitationToken
  centerDescriptor : BlueBookP93.Acyclic.Descriptor
  axialDescriptor : BlueBookP93.Acyclic.Descriptor

/-! ## Bounds for the source observation mirrors -/

structure XabcdObservationBoundedIn {policy : P93SpiroAuthorityPolicy} (n : Nat)
    (observation : P93SpiroXabcdAuthorityObservation policy) : Prop where
  systemBound : SpiroSystemBoundedIn n observation.system

structure XababObservationBoundedIn {policy : P93SpiroAuthorityPolicy} (n : Nat)
    (observation : P93SpiroXababAuthorityObservation policy) : Prop where
  systemBound : SpiroSystemBoundedIn n observation.system

structure DoubleBondObservationBoundedIn {policy : P93SpiroAuthorityPolicy} (n : Nat)
    (observation : P93SpiroDoubleBondAuthorityObservation policy) : Prop where
  systemBound : SpiroSystemBoundedIn n observation.system
  unitBound : P93AuthorityPhysicalUnit.BoundedIn n observation.unit
  ringBound : ∀ atom ∈ observation.ring, atom < n

structure PolyhedralObservationBoundedIn {policy : P93SpiroAuthorityPolicy} (n : Nat)
    (observation : P93SpiroPolyhedralAuthorityObservation policy) : Prop where
  systemBound : SpiroSystemBoundedIn n observation.system
  unitBound : P93AuthorityPhysicalUnit.BoundedIn n observation.unit

structure AxialObservationBoundedIn {policy : P93SpiroAuthorityPolicy} (n : Nat)
    (observation : P93SpiroAxialAuthorityObservation policy) : Prop where
  systemBound : SpiroSystemBoundedIn n observation.system

/-! ## Per-form relabelling, decoding and exact inverses -/

def relabelXabcdObservation {V : Type*} {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (observation : P93SpiroXabcdAuthorityObservation policy)
    (bounded : XabcdObservationBoundedIn n observation) :
    NativeSpiroXabcdObservation policy V where
  system := relabelSpiroSystem enumeration observation.system bounded.systemBound
  citation := observation.citation
  descriptor := observation.descriptor

def decodeXabcdObservation {V : Type*} {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (native : NativeSpiroXabcdObservation policy V) :
    P93SpiroXabcdAuthorityObservation policy where
  system := decodeSpiroSystem enumeration native.system
  citation := native.citation
  descriptor := native.descriptor

def decodeXabcdObservationBounded {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (native : NativeSpiroXabcdObservation policy V) :
    XabcdObservationBoundedIn n (decodeXabcdObservation enumeration native) where
  systemBound := decodeSpiroSystemBounded enumeration native.system

theorem decodeXabcdObservation_relabelXabcdObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93SpiroXabcdAuthorityObservation policy)
    (bounded : XabcdObservationBoundedIn n observation) :
    decodeXabcdObservation enumeration
        (relabelXabcdObservation enumeration observation bounded) = observation := by
  obtain ⟨system, citation, descriptor⟩ := observation
  simp [decodeXabcdObservation, relabelXabcdObservation,
    decodeSpiroSystem_relabelSpiroSystem]

theorem relabelXabcdObservation_decodeXabcdObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (native : NativeSpiroXabcdObservation policy V) :
    relabelXabcdObservation enumeration (decodeXabcdObservation enumeration native)
        (decodeXabcdObservationBounded enumeration native) = native := by
  obtain ⟨system, citation, descriptor⟩ := native
  simp [decodeXabcdObservation, relabelXabcdObservation,
    relabelSpiroSystem_decodeSpiroSystem]

def relabelXababObservation {V : Type*} {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (observation : P93SpiroXababAuthorityObservation policy)
    (bounded : XababObservationBoundedIn n observation) :
    NativeSpiroXababObservation policy V where
  system := relabelSpiroSystem enumeration observation.system bounded.systemBound
  citation := observation.citation
  family := observation.family
  occurrenceOrder := observation.occurrenceOrder
  descriptor := observation.descriptor

def decodeXababObservation {V : Type*} {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (native : NativeSpiroXababObservation policy V) :
    P93SpiroXababAuthorityObservation policy where
  system := decodeSpiroSystem enumeration native.system
  citation := native.citation
  family := native.family
  occurrenceOrder := native.occurrenceOrder
  descriptor := native.descriptor

def decodeXababObservationBounded {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (native : NativeSpiroXababObservation policy V) :
    XababObservationBoundedIn n (decodeXababObservation enumeration native) where
  systemBound := decodeSpiroSystemBounded enumeration native.system

theorem decodeXababObservation_relabelXababObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93SpiroXababAuthorityObservation policy)
    (bounded : XababObservationBoundedIn n observation) :
    decodeXababObservation enumeration
        (relabelXababObservation enumeration observation bounded) = observation := by
  obtain ⟨system, citation, family, occurrenceOrder, descriptor⟩ := observation
  simp [decodeXababObservation, relabelXababObservation,
    decodeSpiroSystem_relabelSpiroSystem]

theorem relabelXababObservation_decodeXababObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (native : NativeSpiroXababObservation policy V) :
    relabelXababObservation enumeration (decodeXababObservation enumeration native)
        (decodeXababObservationBounded enumeration native) = native := by
  obtain ⟨system, citation, family, occurrenceOrder, descriptor⟩ := native
  simp [decodeXababObservation, relabelXababObservation,
    relabelSpiroSystem_decodeSpiroSystem]

def relabelDoubleBondObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93SpiroDoubleBondAuthorityObservation policy)
    (bounded : DoubleBondObservationBoundedIn n observation) :
    NativeSpiroDoubleBondObservation policy V where
  system := relabelSpiroSystem enumeration observation.system bounded.systemBound
  unit := relabelUnit enumeration observation.unit bounded.unitBound
  ring := relabelList enumeration observation.ring bounded.ringBound
  citation := observation.citation
  geometry := observation.geometry
  context := observation.context
  descriptor? := observation.descriptor?

def decodeDoubleBondObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeSpiroDoubleBondObservation policy V) :
    P93SpiroDoubleBondAuthorityObservation policy where
  system := decodeSpiroSystem enumeration native.system
  unit := unrelabelUnit enumeration native.unit
  ring := unrelabelList enumeration native.ring
  citation := native.citation
  geometry := native.geometry
  context := native.context
  descriptor? := native.descriptor?

def decodeDoubleBondObservationBounded {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeSpiroDoubleBondObservation policy V) :
    DoubleBondObservationBoundedIn n
      (decodeDoubleBondObservation enumeration native) where
  systemBound := decodeSpiroSystemBounded enumeration native.system
  unitBound := unrelabelUnitBounded enumeration native.unit
  ringBound := unrelabelList_bounded enumeration native.ring

theorem decodeDoubleBondObservation_relabelDoubleBondObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93SpiroDoubleBondAuthorityObservation policy)
    (bounded : DoubleBondObservationBoundedIn n observation) :
    decodeDoubleBondObservation enumeration
        (relabelDoubleBondObservation enumeration observation bounded) = observation := by
  obtain ⟨system, unit, ring, citation, geometry, context, descriptor?⟩ := observation
  simp [decodeDoubleBondObservation, relabelDoubleBondObservation,
    decodeSpiroSystem_relabelSpiroSystem, unrelabelUnit_relabelUnit,
    unrelabelList_relabelList]

theorem relabelDoubleBondObservation_decodeDoubleBondObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeSpiroDoubleBondObservation policy V) :
    relabelDoubleBondObservation enumeration
        (decodeDoubleBondObservation enumeration native)
        (decodeDoubleBondObservationBounded enumeration native) = native := by
  obtain ⟨system, unit, ring, citation, geometry, context, descriptor?⟩ := native
  simp [decodeDoubleBondObservation, relabelDoubleBondObservation,
    relabelSpiroSystem_decodeSpiroSystem, relabelUnit_unrelabelUnit,
    relabelList_unrelabelList]

def relabelPolyhedralObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93SpiroPolyhedralAuthorityObservation policy)
    (bounded : PolyhedralObservationBoundedIn n observation) :
    NativeSpiroPolyhedralObservation policy V where
  system := relabelSpiroSystem enumeration observation.system bounded.systemBound
  unit := relabelUnit enumeration observation.unit bounded.unitBound
  citation := observation.citation
  coordination := observation.coordination
  knowledge := observation.knowledge
  descriptor := observation.descriptor

def decodePolyhedralObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeSpiroPolyhedralObservation policy V) :
    P93SpiroPolyhedralAuthorityObservation policy where
  system := decodeSpiroSystem enumeration native.system
  unit := unrelabelUnit enumeration native.unit
  citation := native.citation
  coordination := native.coordination
  knowledge := native.knowledge
  descriptor := native.descriptor

def decodePolyhedralObservationBounded {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeSpiroPolyhedralObservation policy V) :
    PolyhedralObservationBoundedIn n
      (decodePolyhedralObservation enumeration native) where
  systemBound := decodeSpiroSystemBounded enumeration native.system
  unitBound := unrelabelUnitBounded enumeration native.unit

theorem decodePolyhedralObservation_relabelPolyhedralObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93SpiroPolyhedralAuthorityObservation policy)
    (bounded : PolyhedralObservationBoundedIn n observation) :
    decodePolyhedralObservation enumeration
        (relabelPolyhedralObservation enumeration observation bounded) = observation := by
  obtain ⟨system, unit, citation, coordination, knowledge, descriptor⟩ := observation
  simp [decodePolyhedralObservation, relabelPolyhedralObservation,
    decodeSpiroSystem_relabelSpiroSystem, unrelabelUnit_relabelUnit]

theorem relabelPolyhedralObservation_decodePolyhedralObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeSpiroPolyhedralObservation policy V) :
    relabelPolyhedralObservation enumeration
        (decodePolyhedralObservation enumeration native)
        (decodePolyhedralObservationBounded enumeration native) = native := by
  obtain ⟨system, unit, citation, coordination, knowledge, descriptor⟩ := native
  simp [decodePolyhedralObservation, relabelPolyhedralObservation,
    relabelSpiroSystem_decodeSpiroSystem, relabelUnit_unrelabelUnit]

def relabelAxialObservation {V : Type*} {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (observation : P93SpiroAxialAuthorityObservation policy)
    (bounded : AxialObservationBoundedIn n observation) :
    NativeSpiroAxialObservation policy V where
  system := relabelSpiroSystem enumeration observation.system bounded.systemBound
  citation := observation.citation
  centerDescriptor := observation.centerDescriptor
  axialDescriptor := observation.axialDescriptor

def decodeAxialObservation {V : Type*} {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n)
    (native : NativeSpiroAxialObservation policy V) :
    P93SpiroAxialAuthorityObservation policy where
  system := decodeSpiroSystem enumeration native.system
  citation := native.citation
  centerDescriptor := native.centerDescriptor
  axialDescriptor := native.axialDescriptor

def decodeAxialObservationBounded {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (native : NativeSpiroAxialObservation policy V) :
    AxialObservationBoundedIn n (decodeAxialObservation enumeration native) where
  systemBound := decodeSpiroSystemBounded enumeration native.system

theorem decodeAxialObservation_relabelAxialObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observation : P93SpiroAxialAuthorityObservation policy)
    (bounded : AxialObservationBoundedIn n observation) :
    decodeAxialObservation enumeration
        (relabelAxialObservation enumeration observation bounded) = observation := by
  obtain ⟨system, citation, centerDescriptor, axialDescriptor⟩ := observation
  simp [decodeAxialObservation, relabelAxialObservation,
    decodeSpiroSystem_relabelSpiroSystem]

theorem relabelAxialObservation_decodeAxialObservation {V : Type*} {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (native : NativeSpiroAxialObservation policy V) :
    relabelAxialObservation enumeration (decodeAxialObservation enumeration native)
        (decodeAxialObservationBounded enumeration native) = native := by
  obtain ⟨system, citation, centerDescriptor, axialDescriptor⟩ := native
  simp [decodeAxialObservation, relabelAxialObservation,
    relabelSpiroSystem_decodeSpiroSystem]

/-! ## The tagged sum over the five rows -/

/-- One authority observation, tagged by its source row.  The constructor order is fixed, and the
tagged sum retains interleaving and multiplicity when placed in a list. -/
inductive SourceSpiroAuthorityObservation (policy : P93SpiroAuthorityPolicy) where
  | xabcd (observation : P93SpiroXabcdAuthorityObservation policy)
  | xabab (observation : P93SpiroXababAuthorityObservation policy)
  | doubleBond (observation : P93SpiroDoubleBondAuthorityObservation policy)
  | polyhedral (observation : P93SpiroPolyhedralAuthorityObservation policy)
  | axial (observation : P93SpiroAxialAuthorityObservation policy)

/-- The native image of the tagged sum. -/
inductive NativeSpiroAuthorityObservation (policy : P93SpiroAuthorityPolicy) (V : Type*) where
  | xabcd (observation : NativeSpiroXabcdObservation policy V)
  | xabab (observation : NativeSpiroXababObservation policy V)
  | doubleBond (observation : NativeSpiroDoubleBondObservation policy V)
  | polyhedral (observation : NativeSpiroPolyhedralObservation policy V)
  | axial (observation : NativeSpiroAxialObservation policy V)

namespace SourceSpiroAuthorityObservation

/-- Row-dispatched source validity. -/
def ValidFor {policy : P93SpiroAuthorityPolicy} (source : AuthoritativeChemicalInput) :
    SourceSpiroAuthorityObservation policy → Prop
  | .xabcd observation =>
      P93SpiroXabcdAuthorityObservation.ValidFor policy source observation
  | .xabab observation =>
      P93SpiroXababAuthorityObservation.ValidFor policy source observation
  | .doubleBond observation =>
      P93SpiroDoubleBondAuthorityObservation.ValidFor policy source observation
  | .polyhedral observation =>
      P93SpiroPolyhedralAuthorityObservation.ValidFor policy source observation
  | .axial observation =>
      P93SpiroAxialAuthorityObservation.ValidFor policy source observation

/-- Row-dispatched bounds. -/
def BoundedIn {policy : P93SpiroAuthorityPolicy} (n : Nat) :
    SourceSpiroAuthorityObservation policy → Prop
  | .xabcd observation => XabcdObservationBoundedIn n observation
  | .xabab observation => XababObservationBoundedIn n observation
  | .doubleBond observation => DoubleBondObservationBoundedIn n observation
  | .polyhedral observation => PolyhedralObservationBoundedIn n observation
  | .axial observation => AxialObservationBoundedIn n observation

/-- Row-dispatched source mechanical validity of the carried spiro skeleton. -/
def SystemMechanicallyValidFor {policy : P93SpiroAuthorityPolicy}
    (source : AuthoritativeChemicalInput) :
    SourceSpiroAuthorityObservation policy → Prop
  | .xabcd observation => observation.system.MechanicallyValidFor source
  | .xabab observation => observation.system.MechanicallyValidFor source
  | .doubleBond observation => observation.system.MechanicallyValidFor source
  | .polyhedral observation => observation.system.MechanicallyValidFor source
  | .axial observation => observation.system.MechanicallyValidFor source

end SourceSpiroAuthorityObservation

namespace NativeSpiroAuthorityObservation

/-- Row-dispatched native graph validity of the carried spiro skeleton. -/
def SystemGraphValid {V : Type*} [DecidableEq V] [Fintype V]
    {policy : P93SpiroAuthorityPolicy}
    (binding : PhysicalFrameSourceBinding V) :
    NativeSpiroAuthorityObservation policy V → Prop
  | .xabcd observation => observation.system.GraphValid binding
  | .xabab observation => observation.system.GraphValid binding
  | .doubleBond observation => observation.system.GraphValid binding
  | .polyhedral observation => observation.system.GraphValid binding
  | .axial observation => observation.system.GraphValid binding

end NativeSpiroAuthorityObservation

/-! ## Tagged relabelling and decoding -/

def relabelObservation {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n) :
    (observation : SourceSpiroAuthorityObservation policy) →
      SourceSpiroAuthorityObservation.BoundedIn n observation →
        NativeSpiroAuthorityObservation policy V
  | .xabcd observation, bounded =>
      .xabcd (relabelXabcdObservation enumeration observation bounded)
  | .xabab observation, bounded =>
      .xabab (relabelXababObservation enumeration observation bounded)
  | .doubleBond observation, bounded =>
      .doubleBond (relabelDoubleBondObservation enumeration observation bounded)
  | .polyhedral observation, bounded =>
      .polyhedral (relabelPolyhedralObservation enumeration observation bounded)
  | .axial observation, bounded =>
      .axial (relabelAxialObservation enumeration observation bounded)

def decodeObservation {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n) :
    NativeSpiroAuthorityObservation policy V → SourceSpiroAuthorityObservation policy
  | .xabcd observation => .xabcd (decodeXabcdObservation enumeration observation)
  | .xabab observation => .xabab (decodeXababObservation enumeration observation)
  | .doubleBond observation =>
      .doubleBond (decodeDoubleBondObservation enumeration observation)
  | .polyhedral observation =>
      .polyhedral (decodePolyhedralObservation enumeration observation)
  | .axial observation => .axial (decodeAxialObservation enumeration observation)

def decodeObservationBounded {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n) :
    (native : NativeSpiroAuthorityObservation policy V) →
      SourceSpiroAuthorityObservation.BoundedIn n
        (decodeObservation enumeration native)
  | .xabcd native => decodeXabcdObservationBounded enumeration native
  | .xabab native => decodeXababObservationBounded enumeration native
  | .doubleBond native => decodeDoubleBondObservationBounded enumeration native
  | .polyhedral native => decodePolyhedralObservationBounded enumeration native
  | .axial native => decodeAxialObservationBounded enumeration native

theorem decodeObservation_relabelObservation {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n) :
    (observation : SourceSpiroAuthorityObservation policy) →
      (bounded : SourceSpiroAuthorityObservation.BoundedIn n observation) →
        decodeObservation enumeration
          (relabelObservation enumeration observation bounded) = observation
  | .xabcd observation, bounded =>
      congrArg SourceSpiroAuthorityObservation.xabcd
        (decodeXabcdObservation_relabelXabcdObservation enumeration observation bounded)
  | .xabab observation, bounded =>
      congrArg SourceSpiroAuthorityObservation.xabab
        (decodeXababObservation_relabelXababObservation enumeration observation bounded)
  | .doubleBond observation, bounded =>
      congrArg SourceSpiroAuthorityObservation.doubleBond
        (decodeDoubleBondObservation_relabelDoubleBondObservation enumeration
          observation bounded)
  | .polyhedral observation, bounded =>
      congrArg SourceSpiroAuthorityObservation.polyhedral
        (decodePolyhedralObservation_relabelPolyhedralObservation enumeration
          observation bounded)
  | .axial observation, bounded =>
      congrArg SourceSpiroAuthorityObservation.axial
        (decodeAxialObservation_relabelAxialObservation enumeration observation bounded)

theorem relabelObservation_decodeObservation {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (native : NativeSpiroAuthorityObservation policy V) :
    relabelObservation enumeration (decodeObservation enumeration native)
        (decodeObservationBounded enumeration native) = native := by
  cases native with
  | xabcd native =>
      exact congrArg NativeSpiroAuthorityObservation.xabcd
        (relabelXabcdObservation_decodeXabcdObservation enumeration native)
  | xabab native =>
      exact congrArg NativeSpiroAuthorityObservation.xabab
        (relabelXababObservation_decodeXababObservation enumeration native)
  | doubleBond native =>
      exact congrArg NativeSpiroAuthorityObservation.doubleBond
        (relabelDoubleBondObservation_decodeDoubleBondObservation enumeration native)
  | polyhedral native =>
      exact congrArg NativeSpiroAuthorityObservation.polyhedral
        (relabelPolyhedralObservation_decodePolyhedralObservation enumeration native)
  | axial native =>
      exact congrArg NativeSpiroAuthorityObservation.axial
        (relabelAxialObservation_decodeAxialObservation enumeration native)

/-! ## Bounds derived from source validity -/

/-- Every bound needed by the tagged codec follows from the row validity predicate and the
accepted source binding. -/
def SourceSpiroAuthorityObservation.boundedIn_of_validFor {V : Type*}
    [DecidableEq V] [Fintype V] (policy : P93SpiroAuthorityPolicy)
    (binding : PhysicalFrameSourceBinding V) :
    (observation : SourceSpiroAuthorityObservation policy) →
      SourceSpiroAuthorityObservation.ValidFor binding.source observation →
        SourceSpiroAuthorityObservation.BoundedIn (Fintype.card V) observation
  | .xabcd observation, valid =>
      { systemBound :=
          spiroSystemBoundedIn_of_mechanicallyValidFor_card binding
            observation.system valid.1.1 }
  | .xabab observation, valid =>
      { systemBound :=
          spiroSystemBoundedIn_of_mechanicallyValidFor_card binding
            observation.system valid.1.1 }
  | .doubleBond observation, valid =>
      { systemBound :=
          spiroSystemBoundedIn_of_mechanicallyValidFor_card binding
            observation.system valid.1.1
        unitBound :=
          physicalUnitBoundedIn_of_validFor_card policy.physicalObservation
            binding observation.unit valid.2.1
        ringBound := by
          have systemBounded :=
            spiroSystemBoundedIn_of_mechanicallyValidFor_card binding
              observation.system valid.1.1
          have atomsBounded := spiroSystemBoundedIn_atoms systemBounded
          intro atom hmem
          have belongs : observation.ring = observation.system.firstRing ∨
              observation.ring = observation.system.secondRing :=
            valid.2.2.2.2.1
          rcases belongs with ringEq | ringEq
          · rw [ringEq] at hmem
            exact atomsBounded atom
              (P93AuthoritySpiroSystem.firstRing_subset_atoms observation.system hmem)
          · rw [ringEq] at hmem
            exact atomsBounded atom
              (P93AuthoritySpiroSystem.secondRing_subset_atoms observation.system hmem) }
  | .polyhedral observation, valid =>
      { systemBound :=
          spiroSystemBoundedIn_of_mechanicallyValidFor_card binding
            observation.system valid.1.1
        unitBound :=
          physicalUnitBoundedIn_of_validFor_card policy.physicalObservation
            binding observation.unit valid.2.1 }
  | .axial observation, valid =>
      { systemBound :=
          spiroSystemBoundedIn_of_mechanicallyValidFor_card binding
            observation.system valid.1.1 }

/-! ## Graph validity of the carried skeleton -/

theorem relabelObservation_systemGraphValid {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93SpiroAuthorityPolicy) (binding : PhysicalFrameSourceBinding V)
    (observation : SourceSpiroAuthorityObservation policy)
    (valid : SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
    NativeSpiroAuthorityObservation.SystemGraphValid binding
      (relabelObservation binding.enumeration observation
        (SourceSpiroAuthorityObservation.boundedIn_of_validFor policy binding
          observation valid)) := by
  cases observation with
  | xabcd observation =>
      exact relabelSpiroSystem_graphValid binding observation.system valid.1.1
  | xabab observation =>
      exact relabelSpiroSystem_graphValid binding observation.system valid.1.1
  | doubleBond observation =>
      exact relabelSpiroSystem_graphValid binding observation.system valid.1.1
  | polyhedral observation =>
      exact relabelSpiroSystem_graphValid binding observation.system valid.1.1
  | axial observation =>
      exact relabelSpiroSystem_graphValid binding observation.system valid.1.1

theorem decodeObservation_systemMechanicallyValidFor {V : Type*}
    [DecidableEq V] [Fintype V] (policy : P93SpiroAuthorityPolicy)
    (binding : PhysicalFrameSourceBinding V)
    (native : NativeSpiroAuthorityObservation policy V)
    (graphs : NativeSpiroAuthorityObservation.SystemGraphValid binding native) :
    SourceSpiroAuthorityObservation.SystemMechanicallyValidFor binding.source
      (decodeObservation binding.enumeration native) := by
  cases native with
  | xabcd native =>
      exact decodeSpiroSystem_mechanicallyValidFor binding native.system graphs
  | xabab native =>
      exact decodeSpiroSystem_mechanicallyValidFor binding native.system graphs
  | doubleBond native =>
      exact decodeSpiroSystem_mechanicallyValidFor binding native.system graphs
  | polyhedral native =>
      exact decodeSpiroSystem_mechanicallyValidFor binding native.system graphs
  | axial native =>
      exact decodeSpiroSystem_mechanicallyValidFor binding native.system graphs

/-! ## Ordered observation lists -/

def relabelObservationList {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    List (NativeSpiroAuthorityObservation policy V) :=
  observations.attach.map fun observation =>
    relabelObservation enumeration observation.1
      (bounded observation.1 observation.2)

def decodeObservationList {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observations : List (NativeSpiroAuthorityObservation policy V)) :
    List (SourceSpiroAuthorityObservation policy) :=
  observations.map (decodeObservation enumeration)

def decodeObservationListBounded {V : Type*} [DecidableEq V] {n : Nat}
    {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observations : List (NativeSpiroAuthorityObservation policy V)) :
    ∀ observation ∈ decodeObservationList enumeration observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation := by
  intro observation hmem
  rw [decodeObservationList, List.mem_map] at hmem
  rcases hmem with ⟨native, _nativeMem, rfl⟩
  exact decodeObservationBounded enumeration native

theorem decodeObservationList_relabelObservationList {V : Type*} [DecidableEq V]
    {n : Nat} {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    decodeObservationList enumeration
        (relabelObservationList enumeration observations bounded) = observations := by
  unfold relabelObservationList decodeObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact decodeObservation_relabelObservation enumeration observation.1
      (bounded observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

theorem relabelObservationList_decodeObservationList {V : Type*} [DecidableEq V]
    {n : Nat} {policy : P93SpiroAuthorityPolicy} (enumeration : V ≃ Fin n)
    (observations : List (NativeSpiroAuthorityObservation policy V)) :
    relabelObservationList enumeration
        (decodeObservationList enumeration observations)
        (decodeObservationListBounded enumeration observations) = observations := by
  unfold relabelObservationList decodeObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelObservation_decodeObservation enumeration observation.1
  · exact List.attach_map_subtype_val observations

/-! ## The raw source, the satellite and exact recovery -/

/-- A raw spiro authority source: one accepted source binding and an ordered list of tagged
source observations, each certified valid against the bound source. -/
structure RawSpiroAuthoritySource (policy : P93SpiroAuthorityPolicy) (V : Type*)
    [DecidableEq V] [Fintype V] where
  binding : PhysicalFrameSourceBinding V
  observations : List (SourceSpiroAuthorityObservation policy)
  valid : ∀ observation ∈ observations,
    SourceSpiroAuthorityObservation.ValidFor binding.source observation

/-- The composable satellite channel.  The graph and both optional evidence channels are one
independent finite source; `observations` is the ordered native payload list. -/
structure SpiroAuthoritySatellite (policy : P93SpiroAuthorityPolicy) (V : Type*)
    [DecidableEq V] [Fintype V] where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (NativeSpiroAuthorityObservation policy V)

namespace SpiroAuthoritySatellite

/-- The satellite's shared finite source, with the observations intentionally excluded. -/
def toFiniteSource {policy : P93SpiroAuthorityPolicy} {V : Type*}
    [DecidableEq V] [Fintype V] (satellite : SpiroAuthoritySatellite policy V) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end SpiroAuthoritySatellite

/-- Adapt a raw source into the satellite: the shared finite source is retained verbatim, and each
validated source observation is relabelled into the native payload. -/
def adaptSpiroSource {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93SpiroAuthorityPolicy) (raw : RawSpiroAuthoritySource policy V) :
    SpiroAuthoritySatellite policy V where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations :=
    relabelObservationList raw.binding.enumeration raw.observations
      (fun observation hmem =>
        SourceSpiroAuthorityObservation.boundedIn_of_validFor policy raw.binding
          observation (raw.valid observation hmem))

/-- The recovered source record: the exact authoritative input together with the ordered list of
tagged source observations. -/
@[ext] structure RecoveredSpiroAuthoritySource (policy : P93SpiroAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceSpiroAuthorityObservation policy)

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; the observation list is decoded entry by entry with the
explicit enumeration. -/
def decodeSpiroSource {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93SpiroAuthorityPolicy) (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : SpiroAuthoritySatellite policy V) :
    RecoveredSpiroAuthoritySource policy where
  source := satellite.toFiniteSource.encode enumeration
  observations := decodeObservationList enumeration satellite.observations

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input and the exact ordered observation list, including order and multiplicity.
The source equality is the genuine encode equality of the binding; the observation equality is
the exact native inverse of the tagged codec. -/
theorem decodeSpiroSource_adaptSpiroSource {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93SpiroAuthorityPolicy) (raw : RawSpiroAuthoritySource policy V) :
    decodeSpiroSource policy raw.binding.enumeration (adaptSpiroSource policy raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredSpiroAuthoritySource.ext
  · exact raw.binding.encode_shared
  · simp only [decodeSpiroSource, adaptSpiroSource]
    exact decodeObservationList_relabelObservationList raw.binding.enumeration
      raw.observations
      (fun observation hmem =>
        SourceSpiroAuthorityObservation.boundedIn_of_validFor policy raw.binding
          observation (raw.valid observation hmem))

/-! ## Validity at the same source and policy -/

/-- A valid source observation remains valid after exact relabelling and decoding.  This is a
recovery statement at the original source and policy; it is not a claim that an arbitrary
relabelling preserves the source-indexed policy relations. -/
theorem decodeObservation_validFor {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93SpiroAuthorityPolicy) (binding : PhysicalFrameSourceBinding V)
    (observation : SourceSpiroAuthorityObservation policy)
    (valid : SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
    SourceSpiroAuthorityObservation.ValidFor binding.source
      (decodeObservation binding.enumeration
        (relabelObservation binding.enumeration observation
          (SourceSpiroAuthorityObservation.boundedIn_of_validFor policy binding
            observation valid))) := by
  rw [decodeObservation_relabelObservation]
  exact valid

/-- The ordered observation list decoded after adaptation is valid at the same source and policy,
entry for entry. -/
theorem decodedObservationList_validFor {V : Type*} [DecidableEq V] [Fintype V]
    (policy : P93SpiroAuthorityPolicy) (binding : PhysicalFrameSourceBinding V)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
    ∀ observation ∈ decodeObservationList binding.enumeration
        (relabelObservationList binding.enumeration observations
          (fun observation hmem =>
            SourceSpiroAuthorityObservation.boundedIn_of_validFor policy binding
              observation (valid observation hmem))),
      SourceSpiroAuthorityObservation.ValidFor binding.source observation := by
  intro observation hmem
  rw [decodeObservationList_relabelObservationList] at hmem
  exact valid observation hmem

/-! ## The five row tags -/

/-- The five authority rows, in the fixed constructor order of the tagged sums. -/
inductive SpiroAuthorityRow where
  | xabcd
  | xabab
  | doubleBond
  | polyhedral
  | axial
  deriving DecidableEq, Repr

namespace SourceSpiroAuthorityObservation

/-- The source row tag of a tagged observation. -/
def row {policy : P93SpiroAuthorityPolicy} :
    SourceSpiroAuthorityObservation policy → SpiroAuthorityRow
  | .xabcd _ => .xabcd
  | .xabab _ => .xabab
  | .doubleBond _ => .doubleBond
  | .polyhedral _ => .polyhedral
  | .axial _ => .axial

end SourceSpiroAuthorityObservation

namespace NativeSpiroAuthorityObservation

/-- The native row tag of a tagged observation. -/
def row {policy : P93SpiroAuthorityPolicy} {V : Type*} :
    NativeSpiroAuthorityObservation policy V → SpiroAuthorityRow
  | .xabcd _ => .xabcd
  | .xabab _ => .xabab
  | .doubleBond _ => .doubleBond
  | .polyhedral _ => .polyhedral
  | .axial _ => .axial

end NativeSpiroAuthorityObservation

/-- Decoding preserves the row tag, and therefore the variant. -/
@[simp] theorem SourceSpiroAuthorityObservation.row_decodeObservation
    {V : Type*} [DecidableEq V] {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n) (native : NativeSpiroAuthorityObservation policy V) :
    (decodeObservation enumeration native).row = native.row := by
  cases native <;> rfl

/-- Relabelling preserves the row tag, and therefore the variant. -/
@[simp] theorem NativeSpiroAuthorityObservation.row_relabelObservation
    {V : Type*} [DecidableEq V] {n : Nat} {policy : P93SpiroAuthorityPolicy}
    (enumeration : V ≃ Fin n) (observation : SourceSpiroAuthorityObservation policy)
    (bounded : SourceSpiroAuthorityObservation.BoundedIn n observation) :
    (relabelObservation enumeration observation bounded).row = observation.row := by
  cases observation <;> rfl

/-! ## Arbitrary correlated sets of tagged observations

The set codec below uses the actual `relabelObservation` and `decodeObservation` of the accepted
five-form codec, with a bound function correlated with set membership.  No arbitrary codec or
arbitrary inverse is introduced, and no global bound is assumed: the bounds are those of each
member, and the concrete instance `decodeObservationSet_relabelObservationSet_of_validFor` derives
them from the existing row validity predicates. -/

section CorrelatedObservationSets

variable {V : Type*} [DecidableEq V] {n : Nat} {policy : P93SpiroAuthorityPolicy}

/-- Relabelling does not inspect the particular proof of boundedness. -/
theorem relabelObservation_bound_irrel (enumeration : V ≃ Fin n)
    (observation : SourceSpiroAuthorityObservation policy)
    (first second : SourceSpiroAuthorityObservation.BoundedIn n observation) :
    relabelObservation enumeration observation first =
      relabelObservation enumeration observation second := by
  cases observation <;> rfl

/-- Relabelling respects equality of the source observation, independently of how the two
boundedness proofs were obtained. -/
theorem relabelObservation_congr (enumeration : V ≃ Fin n)
    {first second : SourceSpiroAuthorityObservation policy} (equal : first = second)
    (firstBounded : SourceSpiroAuthorityObservation.BoundedIn n first)
    (secondBounded : SourceSpiroAuthorityObservation.BoundedIn n second) :
    relabelObservation enumeration first firstBounded =
      relabelObservation enumeration second secondBounded := by
  cases equal
  exact relabelObservation_bound_irrel enumeration _ firstBounded secondBounded

/-- Image of a set of source observations under the actual tagged codec.  The bound is a function
of the member, so the correlated data of each tagged observation is preserved whole. -/
def relabelObservationSet (enumeration : V ≃ Fin n)
    (observations : Set (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    Set (NativeSpiroAuthorityObservation policy V) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelObservation enumeration observation (bounded observation member) = presented

/-- Preimage of a set of native observations under the actual tagged codec. -/
def decodeObservationSet (enumeration : V ≃ Fin n)
    (observations : Set (NativeSpiroAuthorityObservation policy V)) :
    Set (SourceSpiroAuthorityObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      decodeObservation enumeration presented = recovered

/-- Every decoded member of a native set satisfies the explicit bounds at the same enumeration
arity.  These are the bounds actually used by the source-side relabelling inverse. -/
def decodeObservationSetBounded (enumeration : V ≃ Fin n)
    (observations : Set (NativeSpiroAuthorityObservation policy V)) :
    ∀ observation ∈ decodeObservationSet enumeration observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation := by
  rintro recovered ⟨presented, _member, rfl⟩
  exact decodeObservationBounded enumeration presented

@[simp] theorem mem_relabelObservationSet_iff (enumeration : V ≃ Fin n)
    (observations : Set (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation)
    (presented : NativeSpiroAuthorityObservation policy V) :
    presented ∈ relabelObservationSet enumeration observations bounded ↔
      ∃ observation, ∃ member : observation ∈ observations,
        relabelObservation enumeration observation (bounded observation member) = presented :=
  Iff.rfl

@[simp] theorem mem_decodeObservationSet_iff (enumeration : V ≃ Fin n)
    (observations : Set (NativeSpiroAuthorityObservation policy V))
    (recovered : SourceSpiroAuthorityObservation policy) :
    recovered ∈ decodeObservationSet enumeration observations ↔
      ∃ presented ∈ observations,
        decodeObservation enumeration presented = recovered :=
  Iff.rfl

/-- The set codec is literally an image of the actual relabelling map on the subtype of members. -/
theorem relabelObservationSet_eq_image (enumeration : V ≃ Fin n)
    (observations : Set (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    relabelObservationSet enumeration observations bounded =
      (fun observation : { observation // observation ∈ observations } =>
        relabelObservation enumeration observation.1
          (bounded observation.1 observation.2)) '' Set.univ := by
  ext presented
  change (∃ observation, ∃ member : observation ∈ observations,
      relabelObservation enumeration observation (bounded observation member) = presented) ↔
    presented ∈ (fun observation : { observation // observation ∈ observations } =>
      relabelObservation enumeration observation.1
        (bounded observation.1 observation.2)) '' Set.univ
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨observation, member, relabelEq⟩
    exact ⟨⟨observation, member⟩, relabelEq⟩
  · rintro ⟨observation, relabelEq⟩
    exact ⟨observation.1, observation.2, relabelEq⟩

/-- The decoded set codec is literally an image of the actual decoding map on the subtype of
members. -/
theorem decodeObservationSet_eq_image (enumeration : V ≃ Fin n)
    (observations : Set (NativeSpiroAuthorityObservation policy V)) :
    decodeObservationSet enumeration observations =
      (fun presented : { presented // presented ∈ observations } =>
        decodeObservation enumeration presented.1) '' Set.univ := by
  ext recovered
  change (∃ presented ∈ observations,
      decodeObservation enumeration presented = recovered) ↔
    recovered ∈ (fun presented : { presented // presented ∈ observations } =>
      decodeObservation enumeration presented.1) '' Set.univ
  simp only [Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨presented, member, decodeEq⟩
    exact ⟨⟨presented, member⟩, decodeEq⟩
  · rintro ⟨presented, decodeEq⟩
    exact ⟨presented.1, presented.2, decodeEq⟩

/-- **Correlated-set recovery from the source side.**  Decoding the image of a set of tagged
source observations returns exactly that set, for an arbitrary bound function correlated with set
membership and the actual codec maps. -/
theorem decodeObservationSet_relabelObservationSet (enumeration : V ≃ Fin n)
    (observations : Set (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    decodeObservationSet enumeration
        (relabelObservationSet enumeration observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [decodeObservation_relabelObservation] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelObservation enumeration recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      decodeObservation_relabelObservation enumeration recovered (bounded recovered member)⟩

/-- **Correlated-set recovery from the native side.**  Relabelling the decoding of an arbitrary
set of native observations returns exactly that set.  The bound is derived from the actual
decoding, never assumed. -/
theorem relabelObservationSet_decodeObservationSet (enumeration : V ≃ Fin n)
    (observations : Set (NativeSpiroAuthorityObservation policy V)) :
    relabelObservationSet enumeration (decodeObservationSet enumeration observations)
        (decodeObservationSetBounded enumeration observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have obsEq : decodeObservation enumeration presented = observation := by
      have mapped := congrArg (decodeObservation enumeration) relabelEq.symm
      rwa [decodeObservation_relabelObservation] at mapped
    have decodeEq' : decodeObservation enumeration presented₀ =
        decodeObservation enumeration presented := by
      rw [decodeEq, ← obsEq]
    have key : relabelObservation enumeration
        (decodeObservation enumeration presented₀)
        (decodeObservationBounded enumeration presented₀) = presented := by
      calc
        relabelObservation enumeration (decodeObservation enumeration presented₀)
            (decodeObservationBounded enumeration presented₀) =
          relabelObservation enumeration (decodeObservation enumeration presented)
            (decodeObservationBounded enumeration presented) :=
          relabelObservation_congr enumeration decodeEq' _ _
        _ = presented := relabelObservation_decodeObservation enumeration presented
    have presentedEq : presented = presented₀ := by
      rw [← key]
      exact relabelObservation_decodeObservation enumeration presented₀
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨decodeObservation enumeration presented,
      ⟨presented, member, rfl⟩,
      relabelObservation_decodeObservation enumeration presented⟩

/-- **Correlated validity for a set.**  A native member of the image set is valid at the source
exactly when it is the relabelling of a valid source member.  Validity is therefore correlated with
the actual member, not with a product of channel-wise statements. -/
theorem validFor_mem_relabelObservationSet_iff (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observations : Set (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation)
    (presented : NativeSpiroAuthorityObservation policy V)
    (member : presented ∈ relabelObservationSet enumeration observations bounded) :
    SourceSpiroAuthorityObservation.ValidFor source
        (decodeObservation enumeration presented) ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelObservation enumeration observation
            (bounded observation observationMember) = presented ∧
          SourceSpiroAuthorityObservation.ValidFor source observation := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [decodeObservation_relabelObservation] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [decodeObservation_relabelObservation]

/-- The concrete correlated-set recovery with the actual bounds derived from the existing row
validity predicates: no bound is postulated. -/
theorem decodeObservationSet_relabelObservationSet_of_validFor {V : Type*}
    [DecidableEq V] [Fintype V] (policy : P93SpiroAuthorityPolicy)
    (binding : PhysicalFrameSourceBinding V)
    (observations : Set (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
    decodeObservationSet binding.enumeration
        (relabelObservationSet binding.enumeration observations
          (fun observation member =>
            SourceSpiroAuthorityObservation.boundedIn_of_validFor policy binding
              observation (valid observation member))) = observations :=
  decodeObservationSet_relabelObservationSet binding.enumeration observations _

end CorrelatedObservationSets

/-! ## Explicit list order for all five variants -/

section ObservationListOrder

variable {V : Type*} [DecidableEq V] {n : Nat} {policy : P93SpiroAuthorityPolicy}

/-- The ordered list relabelling is the membership-indexed map of the actual tagged codec. -/
theorem relabelObservationList_eq_pmap (enumeration : V ≃ Fin n)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    relabelObservationList enumeration observations bounded =
      observations.pmap
        (fun observation member =>
          relabelObservation enumeration observation (bounded observation member))
        (fun _ member => member) := by
  unfold relabelObservationList
  exact (List.pmap_eq_map_attach (l := observations)
    (f := fun observation member =>
      relabelObservation enumeration observation (bounded observation member))
    (H := fun _ member => member)).symm

/-- Relabelling preserves the list length, hence the number of occurrences of every variant. -/
@[simp] theorem length_relabelObservationList (enumeration : V ≃ Fin n)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    (relabelObservationList enumeration observations bounded).length =
      observations.length := by
  simp [relabelObservationList]

/-- Decoding preserves the list length. -/
@[simp] theorem length_decodeObservationList (enumeration : V ≃ Fin n)
    (observations : List (NativeSpiroAuthorityObservation policy V)) :
    (decodeObservationList enumeration observations).length = observations.length := by
  simp [decodeObservationList]

/-- The decoded list carries exactly the source row tags, in the same order. -/
@[simp] theorem decodeObservationList_rows (enumeration : V ≃ Fin n)
    (observations : List (NativeSpiroAuthorityObservation policy V)) :
    (decodeObservationList enumeration observations).map
        SourceSpiroAuthorityObservation.row =
      observations.map NativeSpiroAuthorityObservation.row := by
  unfold decodeObservationList
  rw [List.map_map]
  exact List.map_congr_left
    (fun native _ =>
      SourceSpiroAuthorityObservation.row_decodeObservation enumeration native)

/-- The relabelled list carries exactly the source row tags, in the same order.  Together with
`decodeObservationList_relabelObservationList` this states that all five variants, their order and
their multiplicity are preserved by the actual list codec. -/
@[simp] theorem relabelObservationList_rows (enumeration : V ≃ Fin n)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.BoundedIn n observation) :
    (relabelObservationList enumeration observations bounded).map
        NativeSpiroAuthorityObservation.row =
      observations.map SourceSpiroAuthorityObservation.row := by
  calc
    (relabelObservationList enumeration observations bounded).map
        NativeSpiroAuthorityObservation.row =
      (decodeObservationList enumeration
        (relabelObservationList enumeration observations bounded)).map
          SourceSpiroAuthorityObservation.row := by
        unfold decodeObservationList
        rw [List.map_map]
        exact (List.map_congr_left
          (fun native _ =>
            SourceSpiroAuthorityObservation.row_decodeObservation
              enumeration native)).symm
    _ = observations.map SourceSpiroAuthorityObservation.row :=
        congrArg (List.map SourceSpiroAuthorityObservation.row)
          (decodeObservationList_relabelObservationList enumeration observations bounded)

/-- The concrete ordered-list inverse with the actual bounds derived from row validity. -/
theorem decodeObservationList_relabelObservationList_of_validFor {V : Type*}
    [DecidableEq V] [Fintype V] (policy : P93SpiroAuthorityPolicy)
    (binding : PhysicalFrameSourceBinding V)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor binding.source observation) :
    decodeObservationList binding.enumeration
        (relabelObservationList binding.enumeration observations
          (fun observation member =>
            SourceSpiroAuthorityObservation.boundedIn_of_validFor policy binding
              observation (valid observation member))) = observations :=
  decodeObservationList_relabelObservationList binding.enumeration observations _

end ObservationListOrder

/-! ## Concrete certified-source adapter

The adapter below is the explicit `CertifiedAuthoritativeChemicalInput` instance of the accepted
binding: `PhysicalFrameSourceBinding.ofCertified` supplies the actual reconstructed graph, the
actual optional coordinate function and the actual optional drawing source, and its exact round
trip supplies all three binding equalities.  No reconstruction or additional hypothesis is added
here. -/

/-- The accepted binding derived from a certified authoritative input. -/
def certifiedSpiroBinding (certified : CertifiedAuthoritativeChemicalInput) :
    PhysicalFrameSourceBinding (Fin certified.input.molecule.atomCount) :=
  PhysicalFrameSourceBinding.ofCertified certified

@[simp] theorem certifiedSpiroBinding_source
    (certified : CertifiedAuthoritativeChemicalInput) :
    (certifiedSpiroBinding certified).source = certified.input := rfl

@[simp] theorem certifiedSpiroBinding_shared
    (certified : CertifiedAuthoritativeChemicalInput) :
    (certifiedSpiroBinding certified).shared = certified.decode := rfl

@[simp] theorem certifiedSpiroBinding_enumeration
    (certified : CertifiedAuthoritativeChemicalInput) :
    (certifiedSpiroBinding certified).enumeration =
      identityEnumeration certified.input.molecule.atomCount := rfl

namespace RawSpiroAuthoritySource

/-- A raw spiro source whose binding is derived from a certified input.  The observations are the
ordered tagged source rows, each certified valid at the certified input. -/
def ofCertified (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    RawSpiroAuthoritySource policy (Fin certified.input.molecule.atomCount) where
  binding := certifiedSpiroBinding certified
  observations := observations
  valid := valid

@[simp] theorem ofCertified_binding (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (ofCertified policy certified observations valid).binding =
      certifiedSpiroBinding certified := rfl

@[simp] theorem ofCertified_observations (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (ofCertified policy certified observations valid).observations = observations := rfl

@[simp] theorem ofCertified_source (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (ofCertified policy certified observations valid).binding.source = certified.input := rfl

@[simp] theorem ofCertified_enumeration (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (ofCertified policy certified observations valid).binding.enumeration =
      identityEnumeration certified.input.molecule.atomCount := rfl

@[simp] theorem ofCertified_shared_graph (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (ofCertified policy certified observations valid).binding.shared.graph =
      certified.decode.graph := rfl

@[simp] theorem ofCertified_shared_spatial? (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (ofCertified policy certified observations valid).binding.shared.spatial? =
      certified.decode.spatial? := rfl

@[simp] theorem ofCertified_shared_diagram? (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (ofCertified policy certified observations valid).binding.shared.diagram? =
      certified.decode.diagram? := rfl

end RawSpiroAuthoritySource

/-- Adapt a certified input and its ordered validated observations into the satellite.  The shared
source is exactly the certified ingress source; the observations are the actual relabelling of the
ordered source rows under the derived bounds. -/
def adaptSpiroCertified (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    SpiroAuthoritySatellite policy (Fin certified.input.molecule.atomCount) :=
  adaptSpiroSource policy
    (RawSpiroAuthoritySource.ofCertified policy certified observations valid)

@[simp] theorem adaptSpiroCertified_graph (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (adaptSpiroCertified policy certified observations valid).graph =
      certified.decode.graph := rfl

@[simp] theorem adaptSpiroCertified_spatial? (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (adaptSpiroCertified policy certified observations valid).spatial? =
      certified.decode.spatial? := rfl

@[simp] theorem adaptSpiroCertified_diagram? (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (adaptSpiroCertified policy certified observations valid).diagram? =
      certified.decode.diagram? := rfl

/-- The adapted graph encodes to exactly the certified molecule. -/
theorem adaptSpiroCertified_graph_encode (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (adaptSpiroCertified policy certified observations valid).graph.encode
        (identityEnumeration certified.input.molecule.atomCount) =
      certified.input.molecule := by
  rw [adaptSpiroCertified_graph]
  exact CertifiedAuthoritativeChemicalInput.encode_decode_molecule certified

/-- The adapted coordinate channel encodes to exactly the certified optional spatial channel,
including absence. -/
theorem adaptSpiroCertified_spatial?_encode (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    OrganicFiniteSource.encodeSpatial?
        (identityEnumeration certified.input.molecule.atomCount)
        (adaptSpiroCertified policy certified observations valid).spatial? =
      certified.input.spatial? := by
  rw [adaptSpiroCertified_spatial?]
  exact CertifiedAuthoritativeChemicalInput.encode_decode_spatial? certified

/-- The adapted drawing channel encodes to exactly the certified optional diagram channel,
including absence. -/
theorem adaptSpiroCertified_diagram?_encode (policy : P93SpiroAuthorityPolicy)
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    ((adaptSpiroCertified policy certified observations valid).diagram?).map
        (OrganicDiagramSource.encodeDiagram
          (identityEnumeration certified.input.molecule.atomCount)) =
      certified.input.diagram? := by
  rw [adaptSpiroCertified_diagram?]
  exact CertifiedAuthoritativeChemicalInput.encode_decode_diagram? certified

/-- **Exact recovery from a certified input.**  Decoding the adapted satellite returns the exact
certified authoritative input together with the exact ordered observation list, including the
order, multiplicity and variant of every row. -/
theorem decodeSpiroSource_adaptSpiroCertified {policy : P93SpiroAuthorityPolicy}
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    decodeSpiroSource policy (identityEnumeration certified.input.molecule.atomCount)
        (adaptSpiroCertified policy certified observations valid) =
      { source := certified.input, observations := observations } := by
  simpa [adaptSpiroCertified, RawSpiroAuthoritySource.ofCertified,
    certifiedSpiroBinding, PhysicalFrameSourceBinding.ofCertified] using
    decodeSpiroSource_adaptSpiroSource policy
      (RawSpiroAuthoritySource.ofCertified policy certified observations valid)

/-- The source component of certified recovery is exactly the certified input. -/
theorem decodeSpiroSource_adaptSpiroCertified_source {policy : P93SpiroAuthorityPolicy}
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (decodeSpiroSource policy (identityEnumeration certified.input.molecule.atomCount)
        (adaptSpiroCertified policy certified observations valid)).source =
      certified.input := by
  simpa using congrArg RecoveredSpiroAuthoritySource.source
    (decodeSpiroSource_adaptSpiroCertified (policy := policy)
      certified observations valid)

/-- The observation component of certified recovery is exactly the supplied ordered list. -/
theorem decodeSpiroSource_adaptSpiroCertified_observations
    {policy : P93SpiroAuthorityPolicy}
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    (decodeSpiroSource policy (identityEnumeration certified.input.molecule.atomCount)
        (adaptSpiroCertified policy certified observations valid)).observations =
      observations := by
  simpa using congrArg RecoveredSpiroAuthoritySource.observations
    (decodeSpiroSource_adaptSpiroCertified (policy := policy)
      certified observations valid)

/-- Every decoded observation of the certified adapter is valid at the certified input, at the same
row policy, entry for entry. -/
theorem decodedObservations_adaptSpiroCertified_validFor {policy : P93SpiroAuthorityPolicy}
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceSpiroAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation) :
    ∀ observation ∈ (decodeSpiroSource policy
        (identityEnumeration certified.input.molecule.atomCount)
        (adaptSpiroCertified policy certified observations valid)).observations,
      SourceSpiroAuthorityObservation.ValidFor certified.input observation := by
  intro observation member
  simpa [adaptSpiroCertified, RawSpiroAuthoritySource.ofCertified,
    certifiedSpiroBinding, PhysicalFrameSourceBinding.ofCertified, decodeSpiroSource] using
    decodedObservationList_validFor policy
      (PhysicalFrameSourceBinding.ofCertified certified)
      observations valid observation member

/-- A certified authoritative input together with an ordered list of tagged source observations,
each valid at that input.  This bundles exactly the data the concrete adapter consumes. -/
structure CertifiedSpiroAuthoritySource (policy : P93SpiroAuthorityPolicy) where
  certified : CertifiedAuthoritativeChemicalInput
  observations : List (SourceSpiroAuthorityObservation policy)
  valid : ∀ observation ∈ observations,
    SourceSpiroAuthorityObservation.ValidFor certified.input observation

namespace CertifiedSpiroAuthoritySource

variable {policy : P93SpiroAuthorityPolicy}

/-- The explicit raw source with the binding derived from the certified input. -/
def toRaw (source : CertifiedSpiroAuthoritySource policy) :
    RawSpiroAuthoritySource policy (Fin source.certified.input.molecule.atomCount) :=
  RawSpiroAuthoritySource.ofCertified policy source.certified source.observations source.valid

/-- The satellite produced from the bundled certified source. -/
def adapt (source : CertifiedSpiroAuthoritySource policy) :
    SpiroAuthoritySatellite policy (Fin source.certified.input.molecule.atomCount) :=
  adaptSpiroSource policy source.toRaw

@[simp] theorem adapt_graph (source : CertifiedSpiroAuthoritySource policy) :
    source.adapt.graph = source.certified.decode.graph := rfl

@[simp] theorem adapt_spatial? (source : CertifiedSpiroAuthoritySource policy) :
    source.adapt.spatial? = source.certified.decode.spatial? := rfl

@[simp] theorem adapt_diagram? (source : CertifiedSpiroAuthoritySource policy) :
    source.adapt.diagram? = source.certified.decode.diagram? := rfl

/-- **Exact recovery from the bundled certified source.** -/
theorem decode_adapt_exact (source : CertifiedSpiroAuthoritySource policy) :
    decodeSpiroSource policy
        (identityEnumeration source.certified.input.molecule.atomCount) source.adapt =
      { source := source.certified.input, observations := source.observations } := by
  simpa [adapt, toRaw] using
    decodeSpiroSource_adaptSpiroCertified (policy := policy)
      source.certified source.observations source.valid

end CertifiedSpiroAuthoritySource

end TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeSpiroSystem_relabelSpiroSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.relabelSpiroSystem_decodeSpiroSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeSpiroSystem_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.relabelSpiroSystem_graphValid
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeSpiroSystem_mechanicallyValidFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeObservation_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.relabelObservation_decodeObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.relabelObservation_systemGraphValid
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeObservation_systemMechanicallyValidFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeObservationList_relabelObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.relabelObservationList_decodeObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeSpiroSource_adaptSpiroSource
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeObservation_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodedObservationList_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.SourceSpiroAuthorityObservation.row_decodeObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.NativeSpiroAuthorityObservation.row_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeObservationSet_relabelObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.relabelObservationSet_decodeObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.validFor_mem_relabelObservationSet_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeObservationList_rows
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.relabelObservationList_rows
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.decodeSpiroSource_adaptSpiroCertified
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoSpiroAuthorityIngress.CertifiedSpiroAuthoritySource.decode_adapt_exact
