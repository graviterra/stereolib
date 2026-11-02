import TetraStereo.OneCenter.OrganicStereoSourceBoundResidueAssembly
import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
import TetraStereo.KernelOnly
import Mathlib.Data.List.Nodup
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Image

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport

noncomputable section

/-!
# Repeat-residue construction: incorporated fragment templates to a real molecule

This module closes the construction gap between a finite repeat-residue recipe and an actual
complete finite molecule.  A recipe supplies *incorporated* fragment templates (each with a real
finite interaction hypergraph on its local atoms, a scoped locant-to-atom map and a finite locant
cover), an explicit ordered list of copies (including explicitly supplied start/end groups) and an
ordered list of resolved connections.  The construction then

* forms the global atom type as the dependent sum of copy index and local atom;
* inherits atom data verbatim and concatenates injected intra-copy interactions with the supplied
  connection edges, preserving order and multiplicity (no deduplication);
* constructs an actual `ResidueIncidenceLedger` whose every link cites the interaction offset plus
  the connection index, deriving both endpoint resolution and source-interaction membership;
* attaches the resulting source-bound residue channel to a real `WholeState` and
  `OrganicMolecularEvidence` carrying an arbitrary shared real conformation;
* recovers the concrete construction from the assembled and canonical representations.

A specialization for `n` repeat units with explicit start/end groups is provided for arbitrary
finite `n`; consecutive-copy endpoint distinctness is derived from the copy index, not assumed.
No atom, reaction, stereochemical or metadata fact is inferred from a Boolean image flag: all
fragments and connection ports are explicit inputs.
-/

/-! ## Concatenation of ordered blocks

`List.flatten` is not used because the core library does not expose a positional lookup lemma for
it.  `appendBlocks` is the recursive concatenation whose lookup law is proved below. -/

namespace RepeatResidueBlocks

variable {α : Type*}

/-- Recursive concatenation of an ordered list of blocks. -/
def appendBlocks : List (List α) → List α
  | [] => []
  | block :: rest => block ++ appendBlocks rest

@[simp] theorem appendBlocks_nil : appendBlocks ([] : List (List α)) = [] := rfl

@[simp] theorem appendBlocks_cons (block : List α) (rest : List (List α)) :
    appendBlocks (block :: rest) = block ++ appendBlocks rest := rfl

/-- The length of the concatenation is the sum of the block lengths. -/
theorem appendBlocks_length (blocks : List (List α)) :
    (appendBlocks blocks).length = (List.map List.length blocks).sum := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      rw [appendBlocks_cons, List.length_append, ih]
      rfl

/-- Membership in the concatenation is membership in one of the blocks. -/
theorem mem_appendBlocks {blocks : List (List α)} {value : α} :
    value ∈ appendBlocks blocks ↔ ∃ block ∈ blocks, value ∈ block := by
  induction blocks with
  | nil => simp
  | cons block rest ih =>
      rw [appendBlocks_cons, List.mem_append, ih]
      constructor
      · rintro (h | ⟨other, hother, hvalue⟩)
        · exact ⟨block, by simp, h⟩
        · exact ⟨other, by simp [hother], hvalue⟩
      · rintro ⟨other, hother, hvalue⟩
        rcases List.mem_cons.mp hother with rfl | hother
        · exact Or.inl hvalue
        · exact Or.inr ⟨other, hother, hvalue⟩

/-- Injectivity-aware preservation of `Nodup` under `List.map`. -/
theorem nodup_map_of_injective {β : Type*} {f : α → β} (hf : Function.Injective f)
    {values : List α} (hnodup : values.Nodup) : (values.map f).Nodup :=
  List.Nodup.map hf hnodup

/-- A prefix-take sum plus an offset into the next entry stays below the total sum. -/
theorem take_sum_add_lt (sizes : List ℕ) (i j : ℕ) (hi : i < sizes.length)
    (hj : j < sizes[i]'hi) :
    (List.take i sizes).sum + j < sizes.sum := by
  induction sizes generalizing i with
  | nil => simp at hi
  | cons size rest ih =>
      cases i with
      | zero =>
          simp only [List.take_zero, List.sum_nil, Nat.zero_add, List.sum_cons]
          exact Nat.lt_of_lt_of_le (by simpa using hj) (Nat.le_add_right size rest.sum)
      | succ i =>
          have hi' : i < rest.length := by simpa using hi
          have hj' : j < rest[i]'hi' := by simpa using hj
          have ih' := ih i hi' hj'
          simp only [List.take_succ_cons, List.sum_cons]
          rw [Nat.add_assoc]
          exact Nat.add_lt_add_left ih' size

/-- Proof-free positional lookup in the concatenation: the entry at the prefix offset plus `j` is
the `j`-th entry of block `i`.  Order and multiplicity are preserved literally.  The proof-free
`Option` form avoids dependent `getElem` rewrite motives. -/
theorem appendBlocks_getElem? (blocks : List (List α)) (i j : ℕ)
    (hi : i < blocks.length) (hj : j < (blocks[i]'hi).length) :
    (appendBlocks blocks)[(List.take i (List.map List.length blocks)).sum + j]? =
      (blocks[i]'hi)[j]? := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons block rest ih =>
      cases i with
      | zero =>
          have hj' : j < block.length := by simpa using hj
          simp only [List.take_zero, List.sum_nil, Nat.zero_add]
          rw [appendBlocks_cons, List.getElem?_append_left hj']
          rfl
      | succ i =>
          have hi' : i < rest.length := by simpa using hi
          have hj' : j < (rest[i]'hi').length := by simpa using hj
          have hsum : (List.take (Nat.succ i) (List.map List.length (block :: rest))).sum =
              block.length + (List.take i (List.map List.length rest)).sum := by
            simp
          rw [hsum, Nat.add_assoc]
          rw [appendBlocks_cons]
          rw [List.getElem?_append_right
            (Nat.le_add_right block.length
              ((List.take i (List.map List.length rest)).sum + j))]
          rw [Nat.add_sub_cancel_left]
          have hrest : ((block :: rest)[Nat.succ i]'hi)[j]? = (rest[i]'hi')[j]? := by
            simp
          rw [hrest]
          exact ih i hi' hj'

/-- Positional lookup in the concatenation, in `getElem` form.  This is the bridge from the
proof-free `Option` statement above. -/
theorem appendBlocks_getElem (blocks : List (List α)) (i j : ℕ)
    (hi : i < blocks.length) (hj : j < (blocks[i]'hi).length)
    (hbound : (List.take i (List.map List.length blocks)).sum + j < (appendBlocks blocks).length) :
    (appendBlocks blocks)[(List.take i (List.map List.length blocks)).sum + j]'hbound =
      (blocks[i]'hi)[j]'hj := by
  have h := appendBlocks_getElem? blocks i j hi hj
  rw [List.getElem?_eq_getElem hbound, List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

end RepeatResidueBlocks

/-! ## Incorporated fragment templates and recipes -/

/-- An incorporated fragment template: a genuine finite atom count, a finite interaction
hypergraph on the local atoms, a residue fragment with a scoped locant-to-atom map, a finite
duplicate-free locant cover of every locant the fragment actually resolves, and source-supplied
metadata retained verbatim.

Nothing is inferred from the molecule image: the atom count, graph, incidence and metadata are all
explicit source fields. -/
structure IncorporatedFragmentTemplate (Locant : Type) (Metadata : Type) where
  /-- Number of incorporated atoms of this fragment. -/
  atomCount : ℕ
  /-- The actual finite atom-labelled interaction hypergraph on the local atoms. -/
  graph : FiniteAtomInteractionHypergraph (Fin atomCount)
  /-- The residue support and scoped locant incidence of this incorporated fragment. -/
  fragment : ResidueFragment Locant atomCount
  /-- Finite duplicate-free cover of the locants used by this fragment. -/
  locantCover : List Locant
  locantCover_nodup : locantCover.Nodup
  locantCover_covers : ∀ (locant : Locant) (atom : Fin atomCount),
    fragment.incidence locant = some atom → locant ∈ locantCover
  /-- Opaque source metadata retained exactly as supplied. -/
  metadata : Metadata

/-- A finite ordered repeat-residue recipe.  `enumeration` is the explicit ordered copy list:
the copy at position `i` is `enumeration.symm i`.  There is no implicit library selection and no
deduplication. -/
structure RepeatResidueRecipe (Copy : Type) (Locant : Type) (Metadata : Type)
    [DecidableEq Copy] [Fintype Copy] where
  /-- Number of selected copies (including explicitly supplied end groups). -/
  copyCount : ℕ
  /-- The ordered finite copy list. -/
  enumeration : Copy ≃ Fin copyCount
  /-- The incorporated fragment template selected for each copy. -/
  template : Copy → IncorporatedFragmentTemplate Locant Metadata

/-- The global atom type of a recipe: dependent sum of copy identity and local atom.  It is an
`abbrev` so that typeclass synthesis sees the underlying sigma type and can use the standard
`Sigma` decidable-equality and finiteness instances. -/
abbrev RepeatGlobalAtom {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) : Type :=
  Σ copy : Copy, Fin ((recipe.template copy).atomCount)

/-- The total number of global atoms is exactly the sum of the incorporated fragment sizes. -/
theorem repeatGlobalAtom_card {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) :
    Fintype.card (RepeatGlobalAtom recipe) =
      ∑ copy : Copy, (recipe.template copy).atomCount := by
  have hcard : Fintype.card (RepeatGlobalAtom recipe) =
      ∑ copy : Copy, Fintype.card (Fin ((recipe.template copy).atomCount)) :=
    Fintype.card_sigma
  rw [hcard]
  simp

/-- A single copy inclusion is injective, proved directly from the sigma second projection. -/
theorem copyAtom_injective {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) (copy : Copy) :
    Function.Injective
      (fun atom : Fin ((recipe.template copy).atomCount) =>
        (⟨copy, atom⟩ : RepeatGlobalAtom recipe)) := by
  intro first second equal
  exact eq_of_heq (Sigma.mk.inj_iff.mp equal).2

/-- Distinct copies occupy disjoint ranges of global atoms. -/
theorem copyAtom_range_disjoint {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    {first second : Copy} (different : first ≠ second) :
    Disjoint
      (Set.range fun atom : Fin ((recipe.template first).atomCount) =>
        (⟨first, atom⟩ : RepeatGlobalAtom recipe))
      (Set.range fun atom : Fin ((recipe.template second).atomCount) =>
        (⟨second, atom⟩ : RepeatGlobalAtom recipe)) := by
  rw [Set.disjoint_left]
  rintro value ⟨firstAtom, rfl⟩ ⟨secondAtom, equal⟩
  have global : (⟨second, secondAtom⟩ : RepeatGlobalAtom recipe) = ⟨first, firstAtom⟩ := equal
  exact different (congrArg Sigma.fst global).symm

/-! ## Injected intra-copy interactions and ordered blocks -/

/-- Inject one local hyperedge of one copy into the global atom type. -/
def copyHyperedge {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) (copy : Copy)
    (edge : List (Fin ((recipe.template copy).atomCount)) × SemanticInteractionKind) :
    List (RepeatGlobalAtom recipe) × SemanticInteractionKind :=
  (edge.1.map fun atom => (⟨copy, atom⟩ : RepeatGlobalAtom recipe), edge.2)

/-- The injected interaction block of the copy at enumeration position `i`. -/
def copyBlock {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (i : Fin recipe.copyCount) :
    List (List (RepeatGlobalAtom recipe) × SemanticInteractionKind) :=
  (recipe.template (recipe.enumeration.symm i)).graph.interactions.map
    (copyHyperedge recipe (recipe.enumeration.symm i))

/-- The ordered list of copy blocks. -/
def blocks {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) :
    List (List (List (RepeatGlobalAtom recipe) × SemanticInteractionKind)) :=
  List.ofFn fun i : Fin recipe.copyCount => copyBlock recipe i

/-- Concatenated injected intra-copy interactions, in copy order. -/
def intraInteractions {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) :
    List (List (RepeatGlobalAtom recipe) × SemanticInteractionKind) :=
  RepeatResidueBlocks.appendBlocks (blocks recipe)

/-- The interaction offset of a copy: the total number of injected interactions of all earlier
copies in the ordered copy list. -/
def copyOffset {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (i : Fin recipe.copyCount) : ℕ :=
  (List.take i.val (List.map List.length (blocks recipe))).sum

/-- The number of injected intra-copy interactions.  It is an `abbrev` so that it is reducible to
the length of the injected interaction list wherever an index argument is matched. -/
abbrev intraInteractionCount {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) : ℕ :=
  (intraInteractions recipe).length

/-- Defining equation of the injected interaction count. -/
theorem intraInteractionCount_eq {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) :
    intraInteractionCount recipe = (intraInteractions recipe).length := rfl

/-- Every copy block is a member of the ordered block list. -/
theorem copyBlock_mem_blocks {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (i : Fin recipe.copyCount) : copyBlock recipe i ∈ blocks recipe := by
  simp [blocks]

/-- Exact positional form of a block in the ordered block list. -/
theorem blocks_getElem {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (i : Fin recipe.copyCount) (hi : i.val < (blocks recipe).length) :
    (blocks recipe)[i.val]'hi = copyBlock recipe i := by
  simp [blocks]

/-- Exact internal lookup: the interaction at the copy offset plus `k` is precisely the `k`-th
injected interaction of that copy. -/
theorem intraInteractions_getElem {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (i : Fin recipe.copyCount) (k : Fin (copyBlock recipe i).length)
    (hbound : copyOffset recipe i + k.val < (intraInteractions recipe).length) :
    (intraInteractions recipe)[copyOffset recipe i + k.val]'hbound =
      (copyBlock recipe i)[k.val]'k.isLt := by
  have hi : i.val < (blocks recipe).length := by
    simp [blocks]
  have hget : (blocks recipe)[i.val]'hi = copyBlock recipe i := blocks_getElem recipe i hi
  have hj : k.val < ((blocks recipe)[i.val]'hi).length := by
    rw [hget]
    exact k.isLt
  have hmain := RepeatResidueBlocks.appendBlocks_getElem (blocks recipe) i.val k.val hi hj hbound
  simpa [intraInteractions, copyOffset, hget] using hmain

/-- The copy offset plus an in-block index lies strictly inside the injected interaction prefix. -/
theorem copyOffset_add_lt {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (i : Fin recipe.copyCount) (k : Fin (copyBlock recipe i).length) :
    copyOffset recipe i + k.val < intraInteractionCount recipe := by
  have hi : i.val < (List.map List.length (blocks recipe)).length := by
    simp [blocks]
  have hj : k.val < (List.map List.length (blocks recipe))[i.val]'hi := by
    simp only [List.getElem_map]
    rw [blocks_getElem]
    exact k.isLt
  have hmain := RepeatResidueBlocks.take_sum_add_lt (List.map List.length (blocks recipe))
    i.val k.val hi hj
  simpa [copyOffset, intraInteractionCount, intraInteractions,
    RepeatResidueBlocks.appendBlocks_length] using hmain

/-! ## Resolved connections -/

/-- A resolved port: a copy, a locant, the local atom it resolves to, and the resolution proof.
The local atom index is typed at the template selected by that copy, so a port can never silently
name another copy's atom. -/
structure ResolvedPort {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) where
  copy : Copy
  locant : Locant
  atom : Fin ((recipe.template copy).atomCount)
  resolves : (recipe.template copy).fragment.locate? locant = some atom

namespace ResolvedPort

variable {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} {recipe : RepeatResidueRecipe Copy Locant Metadata}

/-- The global atom named by a resolved port. -/
def global (port : ResolvedPort recipe) : RepeatGlobalAtom recipe :=
  ⟨port.copy, port.atom⟩

end ResolvedPort

/-- An ordered binary connection.  Both endpoints are resolved local ports, the interaction kind is
explicit, and the two resulting global atoms are explicitly distinct. -/
structure ResolvedConnection {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata) where
  source : ResolvedPort recipe
  target : ResolvedPort recipe
  kind : SemanticInteractionKind
  distinct : source.global ≠ target.global

namespace ResolvedConnection

variable {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} {recipe : RepeatResidueRecipe Copy Locant Metadata}

/-- The participant list and kind of a connection, as a real global hyperedge. -/
def edge (connection : ResolvedConnection recipe) :
    List (RepeatGlobalAtom recipe) × SemanticInteractionKind :=
  ([connection.source.global, connection.target.global], connection.kind)

end ResolvedConnection

/-- The ordered list of supplied connection edges.  No deduplication and no reordering. -/
def connectionInteractions {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} {recipe : RepeatResidueRecipe Copy Locant Metadata}
    (connections : List (ResolvedConnection recipe)) :
    List (List (RepeatGlobalAtom recipe) × SemanticInteractionKind) :=
  connections.map ResolvedConnection.edge

/-! ## The assembled finite hypergraph -/

/-- The constructed finite atom-labelled interaction hypergraph.  Atom data is inherited exactly
from the selected template; interactions are the concatenation of the injected intra-copy
interactions followed by the supplied connection edges, in order, with multiplicity preserved. -/
def assembledGraph {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe)) :
    FiniteAtomInteractionHypergraph (RepeatGlobalAtom recipe) where
  atomData atom := (recipe.template atom.1).graph.atomData atom.2
  interactions := intraInteractions recipe ++ connectionInteractions connections
  arity_ge_two := by
    intro edge member
    rcases List.mem_append.mp member with intra | connection
    · obtain ⟨block, hblock, hedge⟩ := RepeatResidueBlocks.mem_appendBlocks.mp intra
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hblock
      obtain ⟨sourceEdge, hsource, rfl⟩ := List.mem_map.mp hedge
      have harity := (recipe.template (recipe.enumeration.symm i)).graph.arity_ge_two
        sourceEdge hsource
      simpa [copyHyperedge] using harity
    · obtain ⟨resolved, _, rfl⟩ := List.mem_map.mp connection
      simp [ResolvedConnection.edge]
  participants_nodup := by
    intro edge member
    rcases List.mem_append.mp member with intra | connection
    · obtain ⟨block, hblock, hedge⟩ := RepeatResidueBlocks.mem_appendBlocks.mp intra
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hblock
      obtain ⟨sourceEdge, hsource, rfl⟩ := List.mem_map.mp hedge
      have hnodup := (recipe.template (recipe.enumeration.symm i)).graph.participants_nodup
        sourceEdge hsource
      have hinjective : Function.Injective
          (fun atom : Fin ((recipe.template (recipe.enumeration.symm i)).atomCount) =>
            (⟨recipe.enumeration.symm i, atom⟩ : RepeatGlobalAtom recipe)) :=
        copyAtom_injective recipe (recipe.enumeration.symm i)
      exact RepeatResidueBlocks.nodup_map_of_injective hinjective hnodup
    · obtain ⟨resolved, _, rfl⟩ := List.mem_map.mp connection
      show ([resolved.source.global, resolved.target.global] :
        List (RepeatGlobalAtom recipe)).Nodup
      simp [resolved.distinct]

@[simp] theorem assembledGraph_atomData {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe)) (atom : RepeatGlobalAtom recipe) :
    (assembledGraph recipe connections).atomData atom =
      (recipe.template atom.1).graph.atomData atom.2 := rfl

@[simp] theorem assembledGraph_interactions {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe)) :
    (assembledGraph recipe connections).interactions =
      intraInteractions recipe ++ connectionInteractions connections := rfl

/-- Interaction-list length: injected interactions plus supplied connections. -/
@[simp] theorem assembledGraph_interactions_length {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe)) :
    (assembledGraph recipe connections).interactions.length =
      intraInteractionCount recipe + connections.length := by
  show (intraInteractions recipe ++ connectionInteractions connections).length =
    (intraInteractions recipe).length + connections.length
  rw [List.length_append]
  show (intraInteractions recipe).length + (connections.map ResolvedConnection.edge).length =
    (intraInteractions recipe).length + connections.length
  rw [List.length_map]

/-- The certified encoding of the assembled graph has exactly that interaction count. -/
@[simp] theorem assembledGraph_certifiedInteractions_length
    {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe))) :
    ((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.interactions.length =
      intraInteractionCount recipe + connections.length := by
  rw [certifiedEncoding_interactions_length, assembledGraph_interactions_length]

/-- A connection cited at interaction offset plus `j` is in range. -/
theorem assembledGraph_connection_bound {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe)) (j : Fin connections.length) :
    intraInteractionCount recipe + j.val <
      (assembledGraph recipe connections).interactions.length := by
  rw [assembledGraph_interactions_length]
  exact Nat.add_lt_add_left j.isLt _

/-- An intra-copy interaction cited at its copy offset plus `k` is in range. -/
theorem assembledGraph_intra_bound {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (i : Fin recipe.copyCount) (k : Fin (copyBlock recipe i).length) :
    copyOffset recipe i + k.val <
      (assembledGraph recipe connections).interactions.length := by
  rw [assembledGraph_interactions_length]
  exact Nat.lt_of_lt_of_le (copyOffset_add_lt recipe i k) (Nat.le_add_right _ _)

/-- Exact intra-copy occurrence recovery at the offset position. -/
theorem assembledGraph_intra_get {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (i : Fin recipe.copyCount) (k : Fin (copyBlock recipe i).length) :
    (assembledGraph recipe connections).interactions.get
        ⟨copyOffset recipe i + k.val, assembledGraph_intra_bound recipe connections i k⟩ =
      (copyBlock recipe i).get k := by
  show (assembledGraph recipe connections).interactions[copyOffset recipe i + k.val]'
      (assembledGraph_intra_bound recipe connections i k) =
    (copyBlock recipe i)[k.val]'k.isLt
  show (intraInteractions recipe ++ connectionInteractions connections)[
      copyOffset recipe i + k.val]'(assembledGraph_intra_bound recipe connections i k) =
    (copyBlock recipe i)[k.val]'k.isLt
  rw [List.getElem_append_left (as := intraInteractions recipe)
    (bs := connectionInteractions connections) (copyOffset_add_lt recipe i k)]
  exact intraInteractions_getElem recipe i k _

/-- Proof-free positional form of the connection lookup.  The `Option` form has no dependent proof
argument, so the connection offset can be normalised without a dependent rewrite motive. -/
theorem assembledGraph_connection_get? {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe)) (j : Fin connections.length) :
    (assembledGraph recipe connections).interactions[intraInteractionCount recipe + j.val]? =
      some ((connections.get j).edge) := by
  show (intraInteractions recipe ++ connectionInteractions connections)[
      (intraInteractions recipe).length + j.val]? = some ((connections.get j).edge)
  rw [List.getElem?_append_right
    (Nat.le_add_right (intraInteractions recipe).length j.val)]
  rw [Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem (by
    show j.val < (connectionInteractions connections).length
    simp [connectionInteractions])]
  simp only [connectionInteractions, List.getElem_map]
  rfl

/-- Exact connection occurrence recovery at the offset position. -/
theorem assembledGraph_connection_get {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe)) (j : Fin connections.length) :
    (assembledGraph recipe connections).interactions.get
        ⟨intraInteractionCount recipe + j.val,
          assembledGraph_connection_bound recipe connections j⟩ =
      (connections.get j).edge := by
  have h := assembledGraph_connection_get? recipe connections j
  rw [List.getElem?_eq_getElem
    (assembledGraph_connection_bound recipe connections j)] at h
  show (assembledGraph recipe connections).interactions[intraInteractionCount recipe + j.val]'
      (assembledGraph_connection_bound recipe connections j) = (connections.get j).edge
  exact Option.some.inj h

/-! ## The constructed residue fragments and ledger -/

/-- The atom equivalence induced by the assembled graph at the common enumeration.  It is exactly
the existing `encodedAtomEquiv`, so the constructed ledger and the source-bound channel share one
atom language. -/
def ledgerAtomEquiv {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe))) :
    RepeatGlobalAtom recipe ≃
      Fin ((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.atomCount :=
  OrganicStereoIndependentElectronicEncoding.encodedAtomEquiv
    (assembledGraph recipe connections) atomEquiv

/-- The finite support of one copy in the global encoded atom language. -/
def copySupport {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (copy : Copy) :
    Finset (Fin ((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.atomCount) :=
  (recipe.template copy).fragment.support.image
    (fun atom => ledgerAtomEquiv recipe connections atomEquiv ⟨copy, atom⟩)

/-- The residue fragment of one copy: supports and locant incidences move along the shared encoded
atom equivalence; nothing else changes. -/
def copyFragment {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (copy : Copy) :
    ResidueFragment Locant
      ((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.atomCount where
  support := copySupport recipe connections atomEquiv copy
  incidence locant := ((recipe.template copy).fragment.incidence locant).map
    (fun atom => ledgerAtomEquiv recipe connections atomEquiv ⟨copy, atom⟩)
  incidence_mem_support := by
    intro locant atom found
    obtain ⟨localAtom, hlocal, rfl⟩ := Option.map_eq_some_iff.mp found
    exact Finset.mem_image.mpr ⟨localAtom,
      (recipe.template copy).fragment.incidence_mem_support locant localAtom hlocal, rfl⟩

@[simp] theorem copyFragment_support {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (copy : Copy) :
    (copyFragment recipe connections atomEquiv copy).support =
      copySupport recipe connections atomEquiv copy := rfl

@[simp] theorem copyFragment_incidence {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (copy : Copy) (locant : Locant) :
    (copyFragment recipe connections atomEquiv copy).incidence locant =
      ((recipe.template copy).fragment.incidence locant).map
        (fun atom => ledgerAtomEquiv recipe connections atomEquiv ⟨copy, atom⟩) := rfl

/-- Supports of distinct copies are disjoint in the global atom language. -/
theorem copySupport_disjoint {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    {first second : Copy} (different : first ≠ second) :
    Disjoint (copySupport recipe connections atomEquiv first)
      (copySupport recipe connections atomEquiv second) := by
  rw [Finset.disjoint_left]
  intro value firstMember secondMember
  obtain ⟨firstAtom, _, rfl⟩ := Finset.mem_image.mp firstMember
  obtain ⟨secondAtom, _, hsecond⟩ := Finset.mem_image.mp secondMember
  have global : (⟨second, secondAtom⟩ : RepeatGlobalAtom recipe) = ⟨first, firstAtom⟩ :=
    (ledgerAtomEquiv recipe connections atomEquiv).injective hsecond
  exact different (congrArg Sigma.fst global).symm

/-- The same scope-local locant resolved in two different copies denotes different global atoms:
copy identity is preserved, so repeated local locants never collapse. -/
theorem copyFragment_locant_copy_eq {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    {first second : Copy} {locant : Locant}
    {firstAtom : Fin ((recipe.template first).atomCount)}
    {secondAtom : Fin ((recipe.template second).atomCount)}
    (_hfirst : (recipe.template first).fragment.incidence locant = some firstAtom)
    (_hsecond : (recipe.template second).fragment.incidence locant = some secondAtom)
    (equal : ledgerAtomEquiv recipe connections atomEquiv ⟨first, firstAtom⟩ =
      ledgerAtomEquiv recipe connections atomEquiv ⟨second, secondAtom⟩) :
    first = second :=
  congrArg Sigma.fst ((ledgerAtomEquiv recipe connections atomEquiv).injective equal)

/-- One directed residue link, citing the interaction offset plus the connection position. -/
def ledgerLink {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    DirectedResidueLink Locant (Fin recipe.copyCount)
      ((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.interactions.length where
  source := recipe.enumeration (connections.get j).source.copy
  sourceLocant := (connections.get j).source.locant
  target := recipe.enumeration (connections.get j).target.copy
  targetLocant := (connections.get j).target.locant
  interaction := ⟨intraInteractionCount recipe + j.val, by
    rw [assembledGraph_certifiedInteractions_length]
    exact Nat.add_lt_add_left j.isLt _⟩

@[simp] theorem ledgerLink_interaction_val {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (ledgerLink recipe connections atomEquiv j).interaction.val =
      intraInteractionCount recipe + j.val := rfl

/-- Exact resolution of the source port in the constructed copy fragment. -/
theorem constructedLedger_resolve_source {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (copyFragment recipe connections atomEquiv (connections.get j).source.copy).incidence
        (connections.get j).source.locant =
      some (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).source.copy, (connections.get j).source.atom⟩) := by
  rw [copyFragment_incidence]
  have lookup : (recipe.template (connections.get j).source.copy).fragment.incidence
      (connections.get j).source.locant = some (connections.get j).source.atom :=
    (connections.get j).source.resolves
  rw [lookup]
  rfl

/-- Exact resolution of the target port in the constructed copy fragment. -/
theorem constructedLedger_resolve_target {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (copyFragment recipe connections atomEquiv (connections.get j).target.copy).incidence
        (connections.get j).target.locant =
      some (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).target.copy, (connections.get j).target.atom⟩) := by
  rw [copyFragment_incidence]
  have lookup : (recipe.template (connections.get j).target.copy).fragment.incidence
      (connections.get j).target.locant = some (connections.get j).target.atom :=
    (connections.get j).target.resolves
  rw [lookup]
  rfl

/-- The source endpoint named by connection `j` really occurs as a participant of the interaction
at the cited offset position. -/
theorem constructedLedger_source_participant {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).source.copy, (connections.get j).source.atom⟩).val ∈
      (((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.interactions.get
        (ledgerLink recipe connections atomEquiv j).interaction).participants := by
  rw [certifiedEncoding_interactions_get]
  have hidx : residueSourceInteractionIndex (assembledGraph recipe connections) atomEquiv
      (ledgerLink recipe connections atomEquiv j).interaction =
      ⟨intraInteractionCount recipe + j.val,
        assembledGraph_connection_bound recipe connections j⟩ := by
    apply Fin.ext
    rfl
  rw [hidx, assembledGraph_connection_get]
  simp only [ResolvedConnection.edge, FiniteAtomInteractionHypergraph.encodeInteraction,
    List.mem_map, List.mem_cons, List.mem_nil_iff, or_false]
  exact ⟨(connections.get j).source.global, Or.inl rfl, rfl⟩

/-- The target endpoint named by connection `j` really occurs as a participant of the interaction
at the cited offset position. -/
theorem constructedLedger_target_participant {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).target.copy, (connections.get j).target.atom⟩).val ∈
      (((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.interactions.get
        (ledgerLink recipe connections atomEquiv j).interaction).participants := by
  rw [certifiedEncoding_interactions_get]
  have hidx : residueSourceInteractionIndex (assembledGraph recipe connections) atomEquiv
      (ledgerLink recipe connections atomEquiv j).interaction =
      ⟨intraInteractionCount recipe + j.val,
        assembledGraph_connection_bound recipe connections j⟩ := by
    apply Fin.ext
    rfl
  rw [hidx, assembledGraph_connection_get]
  simp only [ResolvedConnection.edge, FiniteAtomInteractionHypergraph.encodeInteraction,
    List.mem_map, List.mem_cons, List.mem_nil_iff, or_false]
  exact ⟨(connections.get j).target.global, Or.inr rfl, rfl⟩

/-- Endpoint resolution in the exact residual-index form used by the ledger's `residue` field. -/
theorem constructedLedger_source_incidence {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (copyFragment recipe connections atomEquiv
        (recipe.enumeration.symm (ledgerLink recipe connections atomEquiv j).source)).incidence
        (ledgerLink recipe connections atomEquiv j).sourceLocant =
      some (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).source.copy, (connections.get j).source.atom⟩) := by
  have hsource : (ledgerLink recipe connections atomEquiv j).source =
      recipe.enumeration (connections.get j).source.copy := rfl
  have hlocant : (ledgerLink recipe connections atomEquiv j).sourceLocant =
      (connections.get j).source.locant := rfl
  rw [hsource, hlocant, Equiv.symm_apply_apply]
  exact constructedLedger_resolve_source recipe connections atomEquiv j

/-- Endpoint resolution in the exact residual-index form used by the ledger's `residue` field. -/
theorem constructedLedger_target_incidence {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (copyFragment recipe connections atomEquiv
        (recipe.enumeration.symm (ledgerLink recipe connections atomEquiv j).target)).incidence
        (ledgerLink recipe connections atomEquiv j).targetLocant =
      some (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).target.copy, (connections.get j).target.atom⟩) := by
  have htarget : (ledgerLink recipe connections atomEquiv j).target =
      recipe.enumeration (connections.get j).target.copy := rfl
  have hlocant : (ledgerLink recipe connections atomEquiv j).targetLocant =
      (connections.get j).target.locant := rfl
  rw [htarget, hlocant, Equiv.symm_apply_apply]
  exact constructedLedger_resolve_target recipe connections atomEquiv j

/-- The constructed source-bound residue ledger.  It is built from the recipe and the connection
list alone; no original source ledger is accepted as a hypothesis.  Each link cites interaction
offset plus connection position, and both endpoint resolution and actual source interaction
membership are proved. -/
def constructedLedger {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe))) :
    ResidueIncidenceLedger Locant
      ((assembledGraph recipe connections).certifiedEncoding atomEquiv) where
  residueCount := recipe.copyCount
  residue index := copyFragment recipe connections atomEquiv (recipe.enumeration.symm index)
  links := List.ofFn fun j : Fin connections.length =>
    ledgerLink recipe connections atomEquiv j
  link_source_mem := by
    intro link member
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp member
    exact ⟨ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).source.copy, (connections.get j).source.atom⟩,
      constructedLedger_source_incidence recipe connections atomEquiv j,
      constructedLedger_source_participant recipe connections atomEquiv j⟩
  link_target_mem := by
    intro link member
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp member
    exact ⟨ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).target.copy, (connections.get j).target.atom⟩,
      constructedLedger_target_incidence recipe connections atomEquiv j,
      constructedLedger_target_participant recipe connections atomEquiv j⟩

@[simp] theorem constructedLedger_residueCount {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe))) :
    (constructedLedger recipe connections atomEquiv).residueCount = recipe.copyCount := rfl

@[simp] theorem constructedLedger_residue {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (index : Fin recipe.copyCount) :
    (constructedLedger recipe connections atomEquiv).residue index =
      copyFragment recipe connections atomEquiv (recipe.enumeration.symm index) := rfl

/-- Exact ordered link-list recovery: the constructed ledger has exactly one link per supplied
connection, in order, with duplicates preserved. -/
@[simp] theorem constructedLedger_links {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe))) :
    (constructedLedger recipe connections atomEquiv).links =
      List.ofFn (fun j : Fin connections.length =>
        ledgerLink recipe connections atomEquiv j) := rfl

/-- The constructed ledger resolves the source port of every link to the intended global atom. -/
theorem constructedLedger_resolves_source {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (constructedLedger recipe connections atomEquiv).resolve?
        (ledgerLink recipe connections atomEquiv j).source
        (ledgerLink recipe connections atomEquiv j).sourceLocant =
      some (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).source.copy, (connections.get j).source.atom⟩) := by
  unfold ResidueIncidenceLedger.resolve?
  rw [constructedLedger_residue]
  have hsource : (ledgerLink recipe connections atomEquiv j).source =
      recipe.enumeration (connections.get j).source.copy := rfl
  rw [hsource, Equiv.symm_apply_apply]
  show (copyFragment recipe connections atomEquiv (connections.get j).source.copy).incidence
      (connections.get j).source.locant =
    some (ledgerAtomEquiv recipe connections atomEquiv
      ⟨(connections.get j).source.copy, (connections.get j).source.atom⟩)
  exact constructedLedger_resolve_source recipe connections atomEquiv j

/-- The constructed ledger resolves the target port of every link to the intended global atom. -/
theorem constructedLedger_resolves_target {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (j : Fin connections.length) :
    (constructedLedger recipe connections atomEquiv).resolve?
        (ledgerLink recipe connections atomEquiv j).target
        (ledgerLink recipe connections atomEquiv j).targetLocant =
      some (ledgerAtomEquiv recipe connections atomEquiv
        ⟨(connections.get j).target.copy, (connections.get j).target.atom⟩) := by
  unfold ResidueIncidenceLedger.resolve?
  rw [constructedLedger_residue]
  have htarget : (ledgerLink recipe connections atomEquiv j).target =
      recipe.enumeration (connections.get j).target.copy := rfl
  rw [htarget, Equiv.symm_apply_apply]
  show (copyFragment recipe connections atomEquiv (connections.get j).target.copy).incidence
      (connections.get j).target.locant =
    some (ledgerAtomEquiv recipe connections atomEquiv
      ⟨(connections.get j).target.copy, (connections.get j).target.atom⟩)
  exact constructedLedger_resolve_target recipe connections atomEquiv j

/-- The constructed ledger's interaction budget is exactly the assembled graph's interaction
count. -/
@[simp] theorem constructedLedger_interactionCount {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe))) :
    ((assembledGraph recipe connections).certifiedEncoding atomEquiv).input.molecule.interactions.length =
      intraInteractionCount recipe + connections.length :=
  assembledGraph_certifiedInteractions_length recipe connections atomEquiv

/-- The constructed locant cover: each copy contributes exactly its template cover. -/
def constructedCover {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe))) :
    LocantCover (constructedLedger recipe connections atomEquiv) where
  cover index := (recipe.template (recipe.enumeration.symm index)).locantCover
  nodup index := (recipe.template (recipe.enumeration.symm index)).locantCover_nodup
  covers := by
    intro index locant atom found
    simp only [constructedLedger_residue, copyFragment_incidence] at found
    obtain ⟨localAtom, hlocal, _⟩ := Option.map_eq_some_iff.mp found
    exact (recipe.template (recipe.enumeration.symm index)).locantCover_covers
      locant localAtom hlocal

/-! ## Whole state, evidence and source-bound channel -/

/-- The real molecular whole state: the assembled graph, an arbitrary supplied shared real
conformation, and genuinely absent unrelated optional channels (`Fin 0` paths and bands,
`none` electronic/rational/diagram data, empty annotation lists).  The residue ledger field is left
absent here and attached by the evidence record through the source-bound channel. -/
def molecularState {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    WholeState (RepeatGlobalAtom recipe) (Fin 0) (Fin 0) where
  graph := assembledGraph recipe connections
  electronic? := none
  electronic_unpaired := by intro channel present; cases present
  conformation := conformation
  rationalPositions? := none
  rationalPositions_valid := by intro positions present; cases present
  roles := []
  role_valid := by intro annotation member; simp at member
  paths := fun edge => Fin.elim0 edge
  path_valid := fun edge => Fin.elim0 edge
  path_source_endpoint := fun edge => Fin.elim0 edge
  path_target_endpoint := fun edge => Fin.elim0 edge
  bandFamily := fun band => Fin.elim0 band
  band_agreement := fun band => Fin.elim0 band
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by intro row member; simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := none
  frames := []

@[simp] theorem molecularState_graph {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (molecularState recipe connections conformation).graph =
      assembledGraph recipe connections := rfl

@[simp] theorem molecularState_conformation {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (molecularState recipe connections conformation).conformation = conformation := rfl

/-- The actual molecular evidence: assembled graph, shared real conformation, and the constructed
source-bound residue channel.  No affine geometry is invented; every unrelated optional channel is
genuinely absent for this witness. -/
def molecularEvidence {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    OrganicMolecularEvidence (RepeatGlobalAtom recipe) where
  graph := assembledGraph recipe connections
  conformation := conformation
  rationalPositions? := none
  rationalPositions_valid := by intro positions present; cases present
  electronic? := none
  electronic_unpaired := by intro evidence present; cases present
  paths? := none
  paths_graph_eq := by intro family present; cases present
  paths_conformation_eq := by intro family present; cases present
  bands? := none
  bands_graph_eq := by intro bands present; cases present
  bands_conformation_eq := by intro bands present; cases present
  roles := []
  role_valid := by intro annotation member; simp at member
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by intro row member; simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := some (sourceBoundChannel codec atomEquiv
    (molecularState recipe connections conformation)
    (constructedLedger recipe connections atomEquiv)
    (constructedCover recipe connections atomEquiv))
  frames := []

@[simp] theorem molecularEvidence_graph {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (molecularEvidence recipe connections atomEquiv codec conformation).graph =
      assembledGraph recipe connections := rfl

@[simp] theorem molecularEvidence_conformation {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (molecularEvidence recipe connections atomEquiv codec conformation).conformation =
      conformation := rfl

@[simp] theorem molecularEvidence_bands? {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (molecularEvidence recipe connections atomEquiv codec conformation).bands? = none := rfl

@[simp] theorem molecularEvidence_paths? {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (molecularEvidence recipe connections atomEquiv codec conformation).paths? = none := rfl

/-- The source-bound channel attached by the constructed evidence is exactly the channel built
from the constructed ledger and cover. -/
@[simp] theorem molecularEvidence_residueLedger? {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (molecularEvidence recipe connections atomEquiv codec conformation).residueLedger? =
      some (sourceBoundChannel codec atomEquiv
        (molecularState recipe connections conformation)
        (constructedLedger recipe connections atomEquiv)
        (constructedCover recipe connections atomEquiv)) := rfl

/-! ## Assembled core projections -/

/-- The assembled state graph is exactly the constructed finite hypergraph. -/
theorem assemble_core_graph {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (assemble (molecularEvidence recipe connections atomEquiv codec conformation)).stateGraph =
      assembledGraph recipe connections := by
  rw [assemble_graph_of_no_bands _
    (molecularEvidence_bands? recipe connections atomEquiv codec conformation)]
  rfl

/-- The assembled state conformation is exactly the supplied shared real conformation. -/
theorem assemble_core_conformation {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (assemble (molecularEvidence recipe connections atomEquiv codec conformation)).stateConformation =
      conformation := by
  rw [assemble_conformation_of_no_bands _
    (molecularEvidence_bands? recipe connections atomEquiv codec conformation)]
  rfl

/-- The assembled residue channel is exactly the constructed source-bound channel. -/
theorem assemble_core_residueLedger? {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (assemble (molecularEvidence recipe connections atomEquiv codec conformation)).stateResidueLedger? =
      some (sourceBoundChannel codec atomEquiv
        (molecularState recipe connections conformation)
        (constructedLedger recipe connections atomEquiv)
        (constructedCover recipe connections atomEquiv)) := by
  rw [(assemble_annotation_projections
    (molecularEvidence recipe connections atomEquiv codec conformation)).2.2.2.2.2.2.2.2.1]
  rfl

/-- The channel's ordered link list is the positional encoding of the constructed ledger links:
order, multiplicity and duplicate/parallel links are preserved. -/
theorem assemble_core_links {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (sourceBoundChannel codec atomEquiv
        (molecularState recipe connections conformation)
        (constructedLedger recipe connections atomEquiv)
        (constructedCover recipe connections atomEquiv)).annotation.links =
      (constructedLedger recipe connections atomEquiv).links.map (encodeLink codec) :=
  sourceBoundChannel_links codec atomEquiv _ _ _

/-- The assembled representation decodes back to the constructed evidence. -/
theorem assemble_decode {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    decode (assemble (molecularEvidence recipe connections atomEquiv codec conformation)) =
      molecularEvidence recipe connections atomEquiv codec conformation :=
  decode_assemble _

/-! ## Canonical transport recovery -/

/-- The canonically assembled representation's graph is the constructed hypergraph. -/
theorem canonicalAssemble_graph {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (canonicalDecode (canonicalAssemble atomEquiv
      (molecularEvidence recipe connections atomEquiv codec conformation))).stateGraph =
      assembledGraph recipe connections := by
  rw [canonicalDecode_canonicalAssemble]
  exact assemble_core_graph recipe connections atomEquiv codec conformation

/-- The canonically assembled representation's conformation is the supplied real conformation. -/
theorem canonicalAssemble_conformation {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (canonicalDecode (canonicalAssemble atomEquiv
      (molecularEvidence recipe connections atomEquiv codec conformation))).stateConformation =
      conformation := by
  rw [canonicalDecode_canonicalAssemble]
  exact assemble_core_conformation recipe connections atomEquiv codec conformation

/-- The canonically assembled representation's residue channel is the constructed source-bound
channel. -/
theorem canonicalAssemble_residueLedger? {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    (canonicalDecode (canonicalAssemble atomEquiv
      (molecularEvidence recipe connections atomEquiv codec conformation))).stateResidueLedger? =
      some (sourceBoundChannel codec atomEquiv
        (molecularState recipe connections conformation)
        (constructedLedger recipe connections atomEquiv)
        (constructedCover recipe connections atomEquiv)) := by
  rw [canonicalDecode_canonicalAssemble]
  exact assemble_core_residueLedger? recipe connections atomEquiv codec conformation

/-- **Main recovery theorem.**  Applying the actual upstream decode to the decoded canonical
assembly returns the concrete constructed evidence, hence the constructed graph, conformation and
source-bound residue data.  No original source is stored as an opaque payload. -/
theorem decode_canonicalAssemble_construction {Copy : Type} [DecidableEq Copy] [Fintype Copy]
    {Locant Metadata : Type} (recipe : RepeatResidueRecipe Copy Locant Metadata)
    (connections : List (ResolvedConnection recipe))
    (atomEquiv : RepeatGlobalAtom recipe ≃ Fin (Fintype.card (RepeatGlobalAtom recipe)))
    (codec : LocantCodec Locant)
    (conformation : MolecularConformation (RepeatGlobalAtom recipe)) :
    decode (canonicalDecode (canonicalAssemble atomEquiv
      (molecularEvidence recipe connections atomEquiv codec conformation))) =
      molecularEvidence recipe connections atomEquiv codec conformation :=
  decode_canonicalAssemble atomEquiv _

/-! ## A chain specialization for arbitrary finite `n` -/

/-- The ordered copy positions of an `n`-repeat chain with explicit start and end groups.  The
constructors avoid any coercion, so `template .first` is definitionally the start group and ports
need no casts. -/
inductive ChainCopy (n : ℕ) where
  | first
  | middle (index : Fin n)
  | last
deriving DecidableEq

namespace ChainCopy

/-- The middle constructor is injective: two repeat copies with the same local index are the same
copy. -/
theorem middle_injective {n : ℕ} :
    Function.Injective (ChainCopy.middle : Fin n → ChainCopy n) := by
  intro first second equal
  simpa using equal

/-- Position of a chain copy in the canonical `Fin (n + 2)` order: first, middles, last. -/
def toFin {n : ℕ} : ChainCopy n → Fin (n + 2)
  | .first => ⟨0, by omega⟩
  | .middle index => ⟨index.val + 1, by omega⟩
  | .last => ⟨n + 1, by omega⟩

/-- Inverse of `toFin`. -/
def ofFin {n : ℕ} (position : Fin (n + 2)) : ChainCopy n :=
  if hzero : position.val = 0 then .first
  else if hlast : position.val = n + 1 then .last
  else .middle ⟨position.val - 1, by omega⟩

theorem ofFin_toFin {n : ℕ} (copy : ChainCopy n) : ofFin (toFin copy) = copy := by
  cases copy with
  | first =>
      show ofFin (⟨0, by omega⟩ : Fin (n + 2)) = ChainCopy.first
      simp [ofFin]
  | middle index =>
      have hzero : index.val + 1 ≠ 0 := Nat.succ_ne_zero index.val
      have hlast : index.val + 1 ≠ n + 1 := by omega
      simp only [toFin, ofFin, dif_neg hzero, dif_neg hlast]
      congr 1
  | last =>
      have hzero : n + 1 ≠ 0 := Nat.succ_ne_zero n
      show ofFin (⟨n + 1, by omega⟩ : Fin (n + 2)) = ChainCopy.last
      simp [ofFin]

theorem toFin_ofFin {n : ℕ} (position : Fin (n + 2)) : toFin (ofFin position) = position := by
  unfold ofFin
  by_cases hzero : position.val = 0
  · rw [dif_pos hzero]
    show (⟨0, by omega⟩ : Fin (n + 2)) = position
    exact Fin.ext hzero.symm
  · by_cases hlast : position.val = n + 1
    · rw [dif_neg hzero, dif_pos hlast]
      show (⟨n + 1, by omega⟩ : Fin (n + 2)) = position
      exact Fin.ext hlast.symm
    · rw [dif_neg hzero, dif_neg hlast]
      show (⟨(position.val - 1) + 1, by omega⟩ : Fin (n + 2)) = position
      exact Fin.ext (by
        have hpos : 0 < position.val := Nat.pos_of_ne_zero hzero
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt hpos))

/-- The ordered copy equivalence of the chain specialization. -/
def equiv (n : ℕ) : ChainCopy n ≃ Fin (n + 2) where
  toFun := toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

instance instFintype (n : ℕ) : Fintype (ChainCopy n) :=
  Fintype.ofEquiv (Fin (n + 2)) (equiv n).symm

/-- The chain has exactly `n + 2` copies. -/
@[simp] theorem card (n : ℕ) : Fintype.card (ChainCopy n) = n + 2 := by
  rw [Fintype.card_congr (equiv n)]
  simp

end ChainCopy

/-- Resolved ports of the chain specialization.  Every port is a concrete local atom of the
start, repeat or end group; repeat unit ports are shared between all repeat copies because the
*template* is shared while the copy identity (and hence the global atom) remains distinct. -/
structure ChainPorts (Locant : Type) (Metadata : Type) where
  startGroup : IncorporatedFragmentTemplate Locant Metadata
  repeatUnit : IncorporatedFragmentTemplate Locant Metadata
  endGroup : IncorporatedFragmentTemplate Locant Metadata
  startLocant : Locant
  startAtom : Fin startGroup.atomCount
  start_resolves : startGroup.fragment.locate? startLocant = some startAtom
  repeatAcceptorLocant : Locant
  repeatAcceptorAtom : Fin repeatUnit.atomCount
  repeatAcceptor_resolves :
    repeatUnit.fragment.locate? repeatAcceptorLocant = some repeatAcceptorAtom
  repeatDonorLocant : Locant
  repeatDonorAtom : Fin repeatUnit.atomCount
  repeatDonor_resolves : repeatUnit.fragment.locate? repeatDonorLocant = some repeatDonorAtom
  endLocant : Locant
  endAtom : Fin endGroup.atomCount
  end_resolves : endGroup.fragment.locate? endLocant = some endAtom
  linkKind : SemanticInteractionKind

/-- The template selected by a chain copy.  Cases are definitional, so ports written at `.first`,
`.middle` or `.last` typecheck without any cast. -/
def chainTemplate {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ) :
    ChainCopy n → IncorporatedFragmentTemplate Locant Metadata
  | .first => ports.startGroup
  | .middle _ => ports.repeatUnit
  | .last => ports.endGroup

@[simp] theorem chainTemplate_first {Locant Metadata : Type}
    (ports : ChainPorts Locant Metadata) (n : ℕ) :
    chainTemplate ports n .first = ports.startGroup := rfl

@[simp] theorem chainTemplate_middle {Locant Metadata : Type}
    (ports : ChainPorts Locant Metadata) (n : ℕ) (index : Fin n) :
    chainTemplate ports n (.middle index) = ports.repeatUnit := rfl

@[simp] theorem chainTemplate_last {Locant Metadata : Type}
    (ports : ChainPorts Locant Metadata) (n : ℕ) :
    chainTemplate ports n .last = ports.endGroup := rfl

/-- The chain recipe: explicit start group, `n` repeat units and an explicit end group, in order. -/
def chainRecipe {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ) :
    RepeatResidueRecipe (ChainCopy n) Locant Metadata where
  copyCount := n + 2
  enumeration := ChainCopy.equiv n
  template := chainTemplate ports n

/-- The source copy of connection `j`, derived from the position only: `first` at position zero and
`middle (j-1)` afterwards. -/
def chainSourceCopy (n : ℕ) (j : Fin (n + 1)) : ChainCopy n :=
  if hzero : j.val = 0 then .first
  else .middle ⟨j.val - 1, by
    have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have hpos : 0 < j.val := Nat.pos_of_ne_zero hzero
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hpos Nat.one_pos) hj⟩

/-- The target copy of connection `j`, derived from the position only: `last` at the final position
and `middle j` otherwise. -/
def chainTargetCopy (n : ℕ) (j : Fin (n + 1)) : ChainCopy n :=
  if hlast : j.val = n then .last
  else .middle ⟨j.val, by
    have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    exact Nat.lt_of_le_of_ne hj hlast⟩

/-- The resolved source port of connection `j`.  The port locant is the repeat donor for repeat
sources and the start locant for the first connection. -/
def chainSourcePort {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (j : Fin (n + 1)) : ResolvedPort (chainRecipe ports n) :=
  if hzero : j.val = 0 then
    { copy := .first
      locant := ports.startLocant
      atom := ports.startAtom
      resolves := ports.start_resolves }
  else
    { copy := .middle ⟨j.val - 1, by
        have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
        have hpos : 0 < j.val := Nat.pos_of_ne_zero hzero
        exact Nat.lt_of_lt_of_le (Nat.sub_lt hpos Nat.one_pos) hj⟩
      locant := ports.repeatDonorLocant
      atom := ports.repeatDonorAtom
      resolves := ports.repeatDonor_resolves }

/-- The resolved target port of connection `j`: repeat acceptor except at the final connection,
which terminates at the explicit end group. -/
def chainTargetPort {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (j : Fin (n + 1)) : ResolvedPort (chainRecipe ports n) :=
  if hlast : j.val = n then
    { copy := .last
      locant := ports.endLocant
      atom := ports.endAtom
      resolves := ports.end_resolves }
  else
    { copy := .middle ⟨j.val, by
        have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
        exact Nat.lt_of_le_of_ne hj hlast⟩
      locant := ports.repeatAcceptorLocant
      atom := ports.repeatAcceptorAtom
      resolves := ports.repeatAcceptor_resolves }

theorem chainSourcePort_copy {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (j : Fin (n + 1)) :
    (chainSourcePort ports n j).copy = chainSourceCopy n j := by
  by_cases hzero : j.val = 0
  · simp [chainSourcePort, chainSourceCopy, hzero]
  · simp only [chainSourcePort, chainSourceCopy, dif_neg hzero]

theorem chainTargetPort_copy {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (j : Fin (n + 1)) :
    (chainTargetPort ports n j).copy = chainTargetCopy n j := by
  by_cases hlast : j.val = n
  · simp [chainTargetPort, chainTargetCopy, hlast]
  · simp only [chainTargetPort, chainTargetCopy, dif_neg hlast]

/-- Consecutive chain copies are different; this is derived from the position, not assumed. -/
theorem chainSourceCopy_ne_targetCopy (n : ℕ) (j : Fin (n + 1)) :
    chainSourceCopy n j ≠ chainTargetCopy n j := by
  unfold chainSourceCopy chainTargetCopy
  by_cases hzero : j.val = 0
  · by_cases hlast : j.val = n
    · rw [dif_pos hzero, dif_pos hlast]
      simp
    · rw [dif_pos hzero, dif_neg hlast]
      simp
  · by_cases hlast : j.val = n
    · rw [dif_neg hzero, dif_pos hlast]
      simp
    · rw [dif_neg hzero, dif_neg hlast]
      intro equal
      have values : j.val - 1 = j.val :=
        congrArg Fin.val (ChainCopy.middle_injective equal)
      have hlt : j.val - 1 < j.val :=
        Nat.sub_lt (Nat.pos_of_ne_zero hzero) Nat.one_pos
      exact (Nat.ne_of_lt hlt) values

/-- Connection `j` of the chain, with endpoint distinctness derived from the copy position. -/
def chainConnection {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (j : Fin (n + 1)) : ResolvedConnection (chainRecipe ports n) where
  source := chainSourcePort ports n j
  target := chainTargetPort ports n j
  kind := ports.linkKind
  distinct := by
    intro equal
    have copyEqual : (chainSourcePort ports n j).copy = (chainTargetPort ports n j).copy :=
      congrArg Sigma.fst equal
    rw [chainSourcePort_copy, chainTargetPort_copy] at copyEqual
    exact chainSourceCopy_ne_targetCopy n j copyEqual

/-- The ordered chain connections: exactly `n + 1` connections, one between each consecutive pair
of copies. -/
def chainConnections {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ) :
    List (ResolvedConnection (chainRecipe ports n)) :=
  List.ofFn fun j : Fin (n + 1) => chainConnection ports n j

@[simp] theorem chainConnections_length {Locant Metadata : Type}
    (ports : ChainPorts Locant Metadata) (n : ℕ) :
    (chainConnections ports n).length = n + 1 := by
  simp [chainConnections]

/-- The first chain connection starts at the explicit start group. -/
theorem chain_first_source {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ) :
    (chainConnection ports n ⟨0, Nat.succ_pos n⟩).source.copy = ChainCopy.first ∧
    (chainConnection ports n ⟨0, Nat.succ_pos n⟩).source.locant = ports.startLocant := by
  constructor
  · simp [chainConnection, chainSourcePort]
  · simp [chainConnection, chainSourcePort]

/-- Every non-initial chain connection starts at a repeat unit donor port. -/
theorem chain_repeat_source {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (j : Fin (n + 1)) (hpos : 0 < j.val) :
    (chainConnection ports n j).source.locant = ports.repeatDonorLocant := by
  have hzero : j.val ≠ 0 := Nat.ne_of_gt hpos
  simp [chainConnection, chainSourcePort, hzero]

/-- Every non-final chain connection targets a repeat unit acceptor port. -/
theorem chain_repeat_target {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (j : Fin (n + 1)) (hlast : j.val < n) :
    (chainConnection ports n j).target.locant = ports.repeatAcceptorLocant := by
  have hne : j.val ≠ n := Nat.ne_of_lt hlast
  simp [chainConnection, chainTargetPort, hne]

/-- The final chain connection terminates at the explicit end group. -/
theorem chain_last_target {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ) :
    (chainConnection ports n ⟨n, Nat.lt_succ_self n⟩).target.copy = ChainCopy.last ∧
    (chainConnection ports n ⟨n, Nat.lt_succ_self n⟩).target.locant = ports.endLocant := by
  constructor
  · simp [chainConnection, chainTargetPort]
  · simp [chainConnection, chainTargetPort]

/-- The chain construction is total for every finite `n`: the assembled graph has exactly
`n + 1` supplied connection interactions beyond the injected fragment interactions, and its atom
cardinality is the sum of the selected fragment sizes. -/
theorem chain_construction_summary {Locant Metadata : Type} (ports : ChainPorts Locant Metadata)
    (n : ℕ) :
    (assembledGraph (chainRecipe ports n) (chainConnections ports n)).interactions.length =
        intraInteractionCount (chainRecipe ports n) + (n + 1) ∧
      Fintype.card (RepeatGlobalAtom (chainRecipe ports n)) =
        ∑ copy : ChainCopy n, (chainTemplate ports n copy).atomCount := by
  constructor
  · rw [assembledGraph_interactions_length, chainConnections_length]
  · exact repeatGlobalAtom_card (chainRecipe ports n)

/-- The ledger constructed from the chain has exactly `n + 1` links and `n + 2` residues, for every
finite `n`. -/
theorem chain_ledger_summary {Locant Metadata : Type} (ports : ChainPorts Locant Metadata) (n : ℕ)
    (atomEquiv : RepeatGlobalAtom (chainRecipe ports n) ≃
      Fin (Fintype.card (RepeatGlobalAtom (chainRecipe ports n)))) :
    (constructedLedger (chainRecipe ports n) (chainConnections ports n) atomEquiv).links.length =
        n + 1 ∧
      (constructedLedger (chainRecipe ports n) (chainConnections ports n) atomEquiv).residueCount =
        n + 2 := by
  constructor
  · rw [constructedLedger_links, List.length_ofFn, chainConnections_length]
  · rw [constructedLedger_residueCount]
    rfl

/-! ## Kernel-only certificates -/

assert_kernel_only repeatGlobalAtom_card
assert_kernel_only copyAtom_range_disjoint
assert_kernel_only copySupport_disjoint
assert_kernel_only assembledGraph_connection_get
assert_kernel_only intraInteractions_getElem
assert_kernel_only constructedLedger_resolves_source
assert_kernel_only constructedLedger_resolves_target
assert_kernel_only constructedLedger_source_participant
assert_kernel_only assembledGraph_intra_get
assert_kernel_only assemble_core_graph
assert_kernel_only assemble_core_conformation
assert_kernel_only assemble_core_residueLedger?
assert_kernel_only canonicalAssemble_graph
assert_kernel_only decode_canonicalAssemble_construction
assert_kernel_only chainSourceCopy_ne_targetCopy
assert_kernel_only chain_construction_summary
assert_kernel_only chain_ledger_summary

end

end TetraStereo.OneCenter
