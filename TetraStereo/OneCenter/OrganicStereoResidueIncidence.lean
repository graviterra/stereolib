import TetraStereo.OneCenter.OrganicStereoFiniteEncoding
import TetraStereo.OneCenter.GlycolipidStereochemistrySemantics
import TetraStereo.OneCenter.NucleicAcidStereochemistrySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Source-bound finite residue/fragment incidence ledger

This module adds a representation component, not a chemistry oracle.  It records, against an
already certified `CertifiedAuthoritativeChemicalInput`:

* finite residue (or fragment) atom supports, indexed by `Fin residueCount`;
* a partial *residue-scoped* map from locant tokens to source atom indices;
* directed residue links, each carrying a `Fin` index into the actual source interaction list,
  together with endpoint-in-participants certificates (a link records a locant-to-locant
  correspondence into an existing source interaction and does **not** assert a distinct physical
  bond); and
* an optional finite *naming* parent hierarchy that is deliberately independent of the directed
  linkage graph.  Its only content is a rank-acyclic parent map for scoped nomenclature; it makes
  no atom-support-containment claim.

The molecular graph itself is owned by `TetraStereo.OneCenter.OrganicStereoFiniteEncoding`; this
module never introduces a second graph.  Atoms are exactly `Fin input.molecule.atomCount` and
interactions are exactly `Fin input.molecule.interactions.length`, so every support, locant
incidence and link endpoint denotes a source object.

Nothing here requires residue supports to be disjoint, the directed linkage graph to be a tree,
linear, or acyclic, or a locant token to be globally unique.  Locant uniqueness is only meaningful
*within* one residue: the same token may denote different atoms in different residues.  This is
what makes cyclic peptides, branched glycans and overlapping nomenclature support representable.

The two supplied metadata adapters (`GlycolipidCitationAdapter` and
`PhosphodiesterAdapter`) bind existing source-level metadata records to this ledger.  They retain
the supplied anomer / linkage metadata verbatim and prove exact endpoint correspondence; they do
not infer a stereochemical assignment, CIP descriptor or chemical class.

Source-wide atom renaming is intentionally **not** provided: permuting atom indices while leaving
the source `spatial?`/`diagram?` channels unchanged would rebind coordinates, parities and diagram
bond indices to the wrong atoms.  Faithful source-wide index transport belongs to the independent
diagram-encoding component.  Only the sound fragment-local `ResidueFragment.rename` is provided.
-/

/-! ## Bridge between the repository list lookup and `List.getElem?` -/

private theorem listGet?_eq_getElem? {α : Type*} (values : List α) (index : ℕ) :
    listGet? values index = values[index]? := by
  induction values generalizing index with
  | nil => simp [listGet?]
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index => simpa [listGet?] using inductionHypothesis index

/-! ## Residue fragments and scoped locant incidence -/

/-- A finite residue (or fragment) support together with a residue-scoped partial locant map.
`incidence locant = some atom` means that locant, *interpreted in this residue*, denotes the
source atom `atom`.  The function is total on the locant token type but partial into the source
atom type; `none` means that the residue does not use the token.

The map is scoped by the residue: two different residues may assign the same locant token to
different atoms.  The only incidence constraint is local support containment. -/
structure ResidueFragment (Locant : Type*) (atomCount : ℕ) where
  /-- Finite set of source atom indices belonging to this residue/fragment. -/
  support : Finset (Fin atomCount)
  /-- Residue-scoped partial locant-to-atom incidence. -/
  incidence : Locant → Option (Fin atomCount)
  /-- Every locant that resolves denotes an atom of the same residue's support. -/
  incidence_mem_support : ∀ (locant : Locant) (atom : Fin atomCount),
    incidence locant = some atom → atom ∈ support

namespace ResidueFragment

variable {Locant : Type*} {atomCount : ℕ}

/-- Exact scoped lookup of a locant in one residue. -/
def locate? (fragment : ResidueFragment Locant atomCount) (locant : Locant) :
    Option (Fin atomCount) :=
  fragment.incidence locant

@[simp] theorem locate?_eq_incidence (fragment : ResidueFragment Locant atomCount)
    (locant : Locant) : fragment.locate? locant = fragment.incidence locant := rfl

/-- Exact-lookup elimination: a resolved locant denotes an atom inside the residue support. -/
theorem locate?_mem_support (fragment : ResidueFragment Locant atomCount) {locant : Locant}
    {atom : Fin atomCount} (found : fragment.locate? locant = some atom) :
    atom ∈ fragment.support :=
  fragment.incidence_mem_support locant atom found

/-- Support-bound: every atom index in a residue support lies inside the source atom range. -/
theorem support_atom_lt (fragment : ResidueFragment Locant atomCount) {atom : Fin atomCount}
    (_member : atom ∈ fragment.support) : atom.val < atomCount :=
  atom.isLt

/-- Support size is bounded by the source atom count. -/
theorem support_card_le (fragment : ResidueFragment Locant atomCount) :
    fragment.support.card ≤ atomCount := by
  have bound := Finset.card_le_univ fragment.support
  simpa using bound

/-- Atom renaming of a residue fragment along a permutation of the source atom indices.  Supports
and locant incidences move together, so scoped lookup is natural. -/
def rename (fragment : ResidueFragment Locant atomCount) (σ : Equiv.Perm (Fin atomCount)) :
    ResidueFragment Locant atomCount where
  support := fragment.support.map σ.toEmbedding
  incidence locant := (fragment.incidence locant).map σ
  incidence_mem_support := by
    intro locant atom found
    cases observed : fragment.incidence locant with
    | none => simp [observed] at found
    | some old =>
        simp only [observed, Option.map_some, Option.some.injEq] at found
        subst atom
        exact Finset.mem_map.mpr
          ⟨old, fragment.incidence_mem_support locant old observed, rfl⟩

@[simp] theorem rename_support (fragment : ResidueFragment Locant atomCount)
    (σ : Equiv.Perm (Fin atomCount)) :
    (fragment.rename σ).support = fragment.support.map σ.toEmbedding := rfl

/-- Renaming commutes with exact scoped lookup. -/
theorem rename_locate? (fragment : ResidueFragment Locant atomCount)
    (σ : Equiv.Perm (Fin atomCount)) (locant : Locant) :
    (fragment.rename σ).locate? locant = (fragment.locate? locant).map σ := rfl

/-- Pointwise form of `rename_locate?`. -/
theorem rename_locate?_eq_some (fragment : ResidueFragment Locant atomCount)
    (σ : Equiv.Perm (Fin atomCount)) {locant : Locant} {atom : Fin atomCount}
    (found : fragment.locate? locant = some atom) :
    (fragment.rename σ).locate? locant = some (σ atom) := by
  rw [rename_locate?, found]
  rfl

end ResidueFragment

/-! ## Directed links and parent hierarchy -/

/-- A directed residue link in an independently indexed residue type.  The interaction field is
always a `Fin` index into the actual source interaction list, never a free-form identifier.

A link says that a locant in the source residue and a locant in the target residue both resolve to
participants of the same actual source interaction.  It does not by itself claim that the two
resolved atoms are distinct, and it does not claim a bond order or connectivity.  Consumers that
need a real atom-to-atom link use `ResidueIncidenceLedger.DistinctEndpointLink`. -/
structure DirectedResidueLink (Locant : Type*) (Residue : Type*) (interactionCount : ℕ) where
  source : Residue
  sourceLocant : Locant
  target : Residue
  targetLocant : Locant
  interaction : Fin interactionCount

/-- A finite **naming** parent hierarchy on residues.  Parent edges strictly decrease a
natural-number rank, which makes the hierarchy acyclic.  It is *not* the linkage graph: links are
an independent list and may be cyclic, branched or linear.

The structure deliberately says nothing about atom-support containment.  It is a scoped-naming
device (for example, which residue is the parent in a systematic oligosaccharide name), not a
chemical connectivity claim. -/
structure ResidueParentHierarchy (residueCount : ℕ) where
  parent : Fin residueCount → Option (Fin residueCount)
  rank : Fin residueCount → ℕ
  /-- Every parent edge strictly decreases rank. -/
  parent_rank_lt : ∀ (child parentResidue : Fin residueCount),
    parent child = some parentResidue → rank parentResidue < rank child

namespace ResidueParentHierarchy

variable {residueCount : ℕ}

/-- Ranking invariant of the finite parent hierarchy. -/
theorem parent_rank_lt' (hierarchy : ResidueParentHierarchy residueCount)
    {child parentResidue : Fin residueCount}
    (edge : hierarchy.parent child = some parentResidue) :
    hierarchy.rank parentResidue < hierarchy.rank child :=
  hierarchy.parent_rank_lt child parentResidue edge

/-- The parent hierarchy has no self-loops. -/
theorem parent_ne_self (hierarchy : ResidueParentHierarchy residueCount)
    (residue : Fin residueCount) : hierarchy.parent residue ≠ some residue := by
  intro loop
  exact Nat.lt_irrefl _ (hierarchy.parent_rank_lt residue residue loop)

end ResidueParentHierarchy

/-- Parent hierarchy in an independently indexed residue type, mapped to `Fin` by the explicit
enumeration of the general constructor. -/
structure RawResidueParentHierarchy (Residue : Type*) where
  parent : Residue → Option Residue
  rank : Residue → ℕ
  parent_rank_lt : ∀ (child parentResidue : Residue),
    parent child = some parentResidue → rank parentResidue < rank child

/-! ## Source-bound ledger -/

/-- A residue/fragment incidence ledger bound to a certified authoritative source input.

* `residue` gives `residueCount` independently indexed finite supports with scoped locants.
* `links` is an arbitrary finite list of directed links; every `interaction` index is a `Fin`
  index into the source interaction list.
* `link_source_mem` / `link_target_mem` certify that each resolved endpoint really occurs as a
  participant of the interaction at the bound source index.
* `hierarchy?` optionally adds a finite, acyclic parent hierarchy unrelated to `links`.

No disjointness, acyclicity, tree-ness or global locant uniqueness is assumed. -/
structure ResidueIncidenceLedger (Locant : Type*)
    (input : CertifiedAuthoritativeChemicalInput) where
  residueCount : ℕ
  residue : Fin residueCount → ResidueFragment Locant input.input.molecule.atomCount
  links : List
    (DirectedResidueLink Locant (Fin residueCount) input.input.molecule.interactions.length)
  /-- Each link's source endpoint resolves to a participant of the bound source interaction. -/
  link_source_mem : ∀ link ∈ links,
    ∃ atom : Fin input.input.molecule.atomCount,
      (residue link.source).incidence link.sourceLocant = some atom ∧
        atom.val ∈
          (input.input.molecule.interactions.get link.interaction).participants
  /-- Each link's target endpoint resolves to a participant of the bound source interaction. -/
  link_target_mem : ∀ link ∈ links,
    ∃ atom : Fin input.input.molecule.atomCount,
      (residue link.target).incidence link.targetLocant = some atom ∧
        atom.val ∈
          (input.input.molecule.interactions.get link.interaction).participants
  /-- Optional finite parent hierarchy, independent of the directed linkage list. -/
  hierarchy? : Option (ResidueParentHierarchy residueCount) := none

namespace ResidueIncidenceLedger

variable {Locant : Type*} {input : CertifiedAuthoritativeChemicalInput}

/-- Exact scoped lookup in the ledger: resolve a locant inside one residue. -/
def resolve? (ledger : ResidueIncidenceLedger Locant input)
    (residueIndex : Fin ledger.residueCount) (locant : Locant) :
    Option (Fin input.input.molecule.atomCount) :=
  (ledger.residue residueIndex).locate? locant

@[simp] theorem resolve?_eq (ledger : ResidueIncidenceLedger Locant input)
    (residueIndex : Fin ledger.residueCount) (locant : Locant) :
    ledger.resolve? residueIndex locant =
      (ledger.residue residueIndex).incidence locant := rfl

/-- The source interaction named by a link index, as an actual list element. -/
def interaction (_ledger : ResidueIncidenceLedger Locant input)
    (index : Fin input.input.molecule.interactions.length) : SemanticInteraction :=
  input.input.molecule.interactions.get index

/-- Successful scoped lookup stays inside the residue support. -/
theorem resolve?_mem_support (ledger : ResidueIncidenceLedger Locant input)
    {residueIndex : Fin ledger.residueCount} {locant : Locant}
    {atom : Fin input.input.molecule.atomCount}
    (found : ledger.resolve? residueIndex locant = some atom) :
    atom ∈ (ledger.residue residueIndex).support :=
  (ledger.residue residueIndex).locate?_mem_support found

/-- A resolved locant denotes an in-range source atom index. -/
theorem resolve?_atom_lt (ledger : ResidueIncidenceLedger Locant input)
    {residueIndex : Fin ledger.residueCount} {locant : Locant}
    {atom : Fin input.input.molecule.atomCount}
    (_found : ledger.resolve? residueIndex locant = some atom) :
    atom.val < input.input.molecule.atomCount :=
  atom.isLt

/-- Support size is bounded by the source atom count. -/
theorem support_card_le (ledger : ResidueIncidenceLedger Locant input)
    (residueIndex : Fin ledger.residueCount) :
    (ledger.residue residueIndex).support.card ≤ input.input.molecule.atomCount :=
  (ledger.residue residueIndex).support_card_le

/-- Every ledger atom index is a real source atom position: its entry exists in the source atom
list.  This is the representation-level atom-identity guarantee. -/
theorem sourceAtom_exists (_ledger : ResidueIncidenceLedger Locant input)
    (atom : Fin input.input.molecule.atomCount) :
    ∃ sourceAtom : SemanticAtom,
      listGet? input.input.molecule.atoms atom.val = some sourceAtom := by
  have bound : atom.val < input.input.molecule.atoms.length := atom.isLt
  exact listGet?_exists_of_lt _ _ bound

/-- Exact form of `sourceAtom_exists`: the resolved source atom is the list element at that
index, so no atom data is reinterpreted or invented. -/
theorem sourceAtomAt (_ledger : ResidueIncidenceLedger Locant input)
    (atom : Fin input.input.molecule.atomCount) :
    listGet? input.input.molecule.atoms atom.val =
      some (input.input.molecule.atoms.get ⟨atom.val, atom.isLt⟩) :=
  listGet?_eq_some_get _ _

/-- The interaction at a link index is exactly the source list element at that index. -/
theorem interactionAt (ledger : ResidueIncidenceLedger Locant input)
    (index : Fin input.input.molecule.interactions.length) :
    listGet? input.input.molecule.interactions index.val = some (ledger.interaction index) :=
  listGet?_eq_some_get _ index

/-- Source-endpoint correctness: a link's source locant resolves to an atom that lies in the
source residue support and occurs as a participant of the actual source interaction. -/
theorem link_source_correct (ledger : ResidueIncidenceLedger Locant input)
    {link : DirectedResidueLink Locant (Fin ledger.residueCount)
      input.input.molecule.interactions.length}
    (member : link ∈ ledger.links) :
    ∃ atom : Fin input.input.molecule.atomCount,
      (ledger.residue link.source).incidence link.sourceLocant = some atom ∧
        atom ∈ (ledger.residue link.source).support ∧
        atom.val ∈ (ledger.interaction link.interaction).participants := by
  obtain ⟨atom, found, participant⟩ := ledger.link_source_mem link member
  exact ⟨atom, found, (ledger.residue link.source).locate?_mem_support found, participant⟩

/-- Target-endpoint correctness, mirroring `link_source_correct`. -/
theorem link_target_correct (ledger : ResidueIncidenceLedger Locant input)
    {link : DirectedResidueLink Locant (Fin ledger.residueCount)
      input.input.molecule.interactions.length}
    (member : link ∈ ledger.links) :
    ∃ atom : Fin input.input.molecule.atomCount,
      (ledger.residue link.target).incidence link.targetLocant = some atom ∧
        atom ∈ (ledger.residue link.target).support ∧
        atom.val ∈ (ledger.interaction link.interaction).participants := by
  obtain ⟨atom, found, participant⟩ := ledger.link_target_mem link member
  exact ⟨atom, found, (ledger.residue link.target).locate?_mem_support found, participant⟩

/-- Link interaction identity: the referenced interaction is an actual source interaction at
exactly the recorded source index. -/
theorem link_interaction_is_source (ledger : ResidueIncidenceLedger Locant input)
    {link : DirectedResidueLink Locant (Fin ledger.residueCount)
      input.input.molecule.interactions.length}
    (_member : link ∈ ledger.links) :
    listGet? input.input.molecule.interactions link.interaction.val =
      some (ledger.interaction link.interaction) :=
  ledger.interactionAt link.interaction

/-- A ledger link whose two resolved endpoint atoms are certified **distinct** and both occur as
participants of the bound source interaction.  This is the subtype for a real atom-to-atom link;
the plain `links` list intentionally stays permissive (two locants may resolve to the same atom,
which is useful for degenerate or overlapping nomenclature support).

No bond order, CIP descriptor or chemical-class membership is claimed. -/
structure DistinctEndpointLink (ledger : ResidueIncidenceLedger Locant input) where
  /-- The underlying ledger link. -/
  link : DirectedResidueLink Locant (Fin ledger.residueCount)
    input.input.molecule.interactions.length
  /-- The underlying link really occurs in the ledger. -/
  mem : link ∈ ledger.links
  /-- Resolved source atom at the link's source locant. -/
  sourceAtom : Fin input.input.molecule.atomCount
  /-- Resolved source atom at the link's target locant. -/
  targetAtom : Fin input.input.molecule.atomCount
  source_eq : (ledger.residue link.source).incidence link.sourceLocant = some sourceAtom
  target_eq : (ledger.residue link.target).incidence link.targetLocant = some targetAtom
  source_participant : sourceAtom.val ∈ (ledger.interaction link.interaction).participants
  target_participant : targetAtom.val ∈ (ledger.interaction link.interaction).participants
  /-- The two source atoms are distinct. -/
  distinct_atoms : sourceAtom ≠ targetAtom

namespace DistinctEndpointLink

variable {ledger : ResidueIncidenceLedger Locant input}

/-- Both distinct endpoints lie in the corresponding residue supports. -/
theorem endpoints_mem_support (binding : DistinctEndpointLink ledger) :
    binding.sourceAtom ∈ (ledger.residue binding.link.source).support ∧
      binding.targetAtom ∈ (ledger.residue binding.link.target).support :=
  ⟨(ledger.residue binding.link.source).locate?_mem_support binding.source_eq,
    (ledger.residue binding.link.target).locate?_mem_support binding.target_eq⟩

/-- The referenced source interaction is the actual interaction at the recorded source index. -/
theorem interaction_is_source (binding : DistinctEndpointLink ledger) :
    listGet? input.input.molecule.interactions binding.link.interaction.val =
      some (ledger.interaction binding.link.interaction) :=
  ledger.interactionAt binding.link.interaction

end DistinctEndpointLink

end ResidueIncidenceLedger

/-! ## General constructor from independently indexed data

The source data are indexed by an arbitrary finite residue type `Residue`.  A single explicit
bijection `Residue ≃ Fin (Fintype.card Residue)` fixes the `Fin` indexing used by the ledger.  The
constructor is exact: residue data, scoped lookup, links and the parent hierarchy are transported
along that bijection without reinterpretation. -/

/-- Independently indexed residue incidence data over a certified source input.  `Residue` is any
finite type; the explicit enumeration is supplied to `toLedger`. -/
structure RawResidueIncidence (Locant : Type*) (Residue : Type*) [Fintype Residue]
    (input : CertifiedAuthoritativeChemicalInput) where
  fragment : Residue → ResidueFragment Locant input.input.molecule.atomCount
  links : List (DirectedResidueLink Locant Residue input.input.molecule.interactions.length)
  link_source_mem : ∀ link ∈ links,
    ∃ atom : Fin input.input.molecule.atomCount,
      (fragment link.source).incidence link.sourceLocant = some atom ∧
        atom.val ∈
          (input.input.molecule.interactions.get link.interaction).participants
  link_target_mem : ∀ link ∈ links,
    ∃ atom : Fin input.input.molecule.atomCount,
      (fragment link.target).incidence link.targetLocant = some atom ∧
        atom.val ∈
          (input.input.molecule.interactions.get link.interaction).participants
  hierarchy? : Option (RawResidueParentHierarchy Residue) := none

namespace RawResidueIncidence

variable {Locant Residue : Type*} [Fintype Residue]
    {input : CertifiedAuthoritativeChemicalInput}

/-- Transport one raw directed link to the `Fin`-indexed representation.  The interaction index
and both locant tokens are copied verbatim. -/
def mapLink (_source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (link : DirectedResidueLink Locant Residue input.input.molecule.interactions.length) :
    DirectedResidueLink Locant (Fin (Fintype.card Residue))
      input.input.molecule.interactions.length where
  source := enumeration link.source
  sourceLocant := link.sourceLocant
  target := enumeration link.target
  targetLocant := link.targetLocant
  interaction := link.interaction

@[simp] theorem mapLink_source (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (link : DirectedResidueLink Locant Residue input.input.molecule.interactions.length) :
    (source.mapLink enumeration link).source = enumeration link.source := rfl

@[simp] theorem mapLink_sourceLocant (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (link : DirectedResidueLink Locant Residue input.input.molecule.interactions.length) :
    (source.mapLink enumeration link).sourceLocant = link.sourceLocant := rfl

@[simp] theorem mapLink_target (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (link : DirectedResidueLink Locant Residue input.input.molecule.interactions.length) :
    (source.mapLink enumeration link).target = enumeration link.target := rfl

@[simp] theorem mapLink_targetLocant (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (link : DirectedResidueLink Locant Residue input.input.molecule.interactions.length) :
    (source.mapLink enumeration link).targetLocant = link.targetLocant := rfl

/-- Interaction indices are preserved exactly by the constructor. -/
@[simp] theorem mapLink_interaction (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (link : DirectedResidueLink Locant Residue input.input.molecule.interactions.length) :
    (source.mapLink enumeration link).interaction = link.interaction := rfl

/-- Transport a raw parent hierarchy to the `Fin`-indexed representation.  The rank-strictness
certificate is preserved, so the transported hierarchy is still acyclic. -/
def mapHierarchy (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (hierarchy : RawResidueParentHierarchy Residue) :
    ResidueParentHierarchy (Fintype.card Residue) where
  parent index := (hierarchy.parent (enumeration.symm index)).map enumeration
  rank index := hierarchy.rank (enumeration.symm index)
  parent_rank_lt := by
    intro child parentResidue found
    cases observed : hierarchy.parent (enumeration.symm child) with
    | none => simp [observed] at found
    | some candidate =>
        simp only [observed, Option.map_some, Option.some.injEq] at found
        subst parentResidue
        have strict := hierarchy.parent_rank_lt (enumeration.symm child) candidate observed
        simpa using strict

/-- Build the source-bound ledger from independently indexed data and the explicit bijection to
`Fin`.  Every field is transported exactly; nothing is inferred. -/
def toLedger (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) :
    ResidueIncidenceLedger Locant input where
  residueCount := Fintype.card Residue
  residue index := source.fragment (enumeration.symm index)
  links := source.links.map (source.mapLink enumeration)
  link_source_mem := by
    intro link member
    obtain ⟨rawLink, rawMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨atom, found, participant⟩ := source.link_source_mem rawLink rawMember
    refine ⟨atom, ?_, participant⟩
    simpa [mapLink] using found
  link_target_mem := by
    intro link member
    obtain ⟨rawLink, rawMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨atom, found, participant⟩ := source.link_target_mem rawLink rawMember
    refine ⟨atom, ?_, participant⟩
    simpa [mapLink] using found
  hierarchy? := source.hierarchy?.map (mapHierarchy enumeration)

/-- Exact residue lookup after construction: the index named by a source residue carries exactly
that residue's fragment data. -/
theorem toLedger_residue (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) (residue : Residue) :
    (source.toLedger enumeration).residue (enumeration residue) = source.fragment residue := by
  simp [toLedger]

/-- Exact scoped locant lookup after construction. -/
theorem toLedger_resolve (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) (residue : Residue)
    (locant : Locant) :
    (source.toLedger enumeration).resolve? (enumeration residue) locant =
      (source.fragment residue).locate? locant := by
  simp [ResidueIncidenceLedger.resolve?, toLedger]

/-- Exact link lookup after construction: the ledger link at position `index` is precisely the
mapped raw link at that position, so interaction identity and locant tokens are preserved. -/
theorem toLedger_linkAt (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) (index : ℕ)
    (bound : index < source.links.length) :
    listGet? (source.toLedger enumeration).links index =
      some (source.mapLink enumeration (source.links.get ⟨index, bound⟩)) := by
  unfold toLedger
  rw [listGet?_eq_getElem?]
  have mappedBound : index < (source.links.map (source.mapLink enumeration)).length := by
    simpa using bound
  rw [List.getElem?_eq_getElem mappedBound, List.getElem_map]
  rfl

/-- The constructed ledger has exactly as many links as the source. -/
@[simp] theorem toLedger_links_length (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) :
    (source.toLedger enumeration).links.length = source.links.length := by
  simp [toLedger]

/-- The constructed ledger's residue indexing is exactly the source cardinality. -/
@[simp] theorem toLedger_residueCount (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) :
    (source.toLedger enumeration).residueCount = Fintype.card Residue := rfl

/-! ### Decoding residues back to the independent index type -/

/-- Decode a `Fin` residue index back to the independent residue type. -/
def decodeResidue? (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (index : ℕ) : Option Residue :=
  if bound : index < Fintype.card Residue then
    some (enumeration.symm ⟨index, bound⟩)
  else none

/-- Decoding the index of a source residue recovers that residue exactly. -/
@[simp] theorem decodeResidue?_encode (enumeration : Residue ≃ Fin (Fintype.card Residue))
    (residue : Residue) :
    decodeResidue? enumeration (enumeration residue).val = some residue := by
  unfold decodeResidue?
  rw [dif_pos (enumeration residue).isLt]
  simp

/-- Scoped lookup round trip: resolving through the decoded `Fin` index is the same as resolving
directly in the independent residue. -/
theorem toLedger_decode_resolve (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) (index : ℕ)
    (bound : index < Fintype.card Residue) (locant : Locant) :
    (source.toLedger enumeration).resolve? ⟨index, bound⟩ locant =
      (source.fragment (enumeration.symm ⟨index, bound⟩)).locate? locant := by
  rfl

/-- End-to-end round trip at any independently indexed residue. -/
theorem toLedger_resolve_roundtrip (source : RawResidueIncidence Locant Residue input)
    (enumeration : Residue ≃ Fin (Fintype.card Residue)) (residue : Residue)
    (locant : Locant) :
    (source.toLedger enumeration).resolve?
        ⟨(enumeration residue).val, (enumeration residue).isLt⟩ locant =
      (source.fragment residue).locate? locant := by
  simpa using source.toLedger_resolve enumeration residue locant

end RawResidueIncidence

/-! ## Exact metadata adapters

Existing source-level metadata records are *not* molecular bindings by themselves.  The adapters
below attach such a record to explicit residues, locants and an actual source interaction index,
and prove that the attached locants resolve to participants of that interaction.  They retain the
supplied metadata verbatim; no adapter infers an anomeric configuration, a CIP descriptor or a
chemical class. -/

namespace GlycolipidCitationAdapter

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- A `Glycolipid1997.GlycosidicCitation` bound to a natural-number-locant ledger.  The citation's
`anomer`, `donorLocant` and `acceptorLocant` are copied from the source metadata; the binding
records where the two locants resolve and that the resolved atoms participate in the supplied
source interaction.

There is no field asserting that the anomer is the chemically correct configuration. -/
structure Binding (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) where
  /-- The supplied source metadata, retained verbatim. -/
  citation : Glycolipid1997.GlycosidicCitation
  sourceResidue : Fin ledger.residueCount
  targetResidue : Fin ledger.residueCount
  /-- Index of the actual source interaction that carries both resolved endpoints. -/
  interaction : Fin input.input.molecule.interactions.length
  sourceAtom : Fin input.input.molecule.atomCount
  targetAtom : Fin input.input.molecule.atomCount
  /-- The donor locant resolves to `sourceAtom` in the source residue. -/
  source_eq : (ledger.residue sourceResidue).incidence citation.donorLocant = some sourceAtom
  /-- The acceptor locant resolves to `targetAtom` in the target residue. -/
  target_eq : (ledger.residue targetResidue).incidence citation.acceptorLocant = some targetAtom
  source_participant :
    sourceAtom.val ∈ (input.input.molecule.interactions.get interaction).participants
  target_participant :
    targetAtom.val ∈ (input.input.molecule.interactions.get interaction).participants

namespace Binding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- The supplied anomer metadata, retained without inference. -/
def anomer (binding : Binding input ledger) : Glycolipid1997.Anomer :=
  binding.citation.anomer

/-- The supplied donor locant, retained verbatim. -/
def donorLocant (binding : Binding input ledger) : Nat :=
  binding.citation.donorLocant

/-- The supplied acceptor locant, retained verbatim. -/
def acceptorLocant (binding : Binding input ledger) : Nat :=
  binding.citation.acceptorLocant

@[simp] theorem anomer_eq (binding : Binding input ledger) :
    binding.anomer = binding.citation.anomer := rfl

@[simp] theorem donorLocant_eq (binding : Binding input ledger) :
    binding.donorLocant = binding.citation.donorLocant := rfl

@[simp] theorem acceptorLocant_eq (binding : Binding input ledger) :
    binding.acceptorLocant = binding.citation.acceptorLocant := rfl

/-- Convert the bound citation into a directed ledger link.  The two locant tokens are exactly the
supplied donor and acceptor locants and the interaction index is the supplied source index. -/
def toLink (binding : Binding input ledger) :
    DirectedResidueLink Nat (Fin ledger.residueCount)
      input.input.molecule.interactions.length where
  source := binding.sourceResidue
  sourceLocant := binding.citation.donorLocant
  target := binding.targetResidue
  targetLocant := binding.citation.acceptorLocant
  interaction := binding.interaction

@[simp] theorem toLink_source (binding : Binding input ledger) :
    binding.toLink.source = binding.sourceResidue := rfl

@[simp] theorem toLink_target (binding : Binding input ledger) :
    binding.toLink.target = binding.targetResidue := rfl

@[simp] theorem toLink_sourceLocant (binding : Binding input ledger) :
    binding.toLink.sourceLocant = binding.citation.donorLocant := rfl

@[simp] theorem toLink_targetLocant (binding : Binding input ledger) :
    binding.toLink.targetLocant = binding.citation.acceptorLocant := rfl

@[simp] theorem toLink_interaction (binding : Binding input ledger) :
    binding.toLink.interaction = binding.interaction := rfl

/-- Exact source-endpoint lookup for the bound citation. -/
theorem toLink_source_resolves (binding : Binding input ledger) :
    (ledger.residue binding.toLink.source).incidence binding.toLink.sourceLocant =
      some binding.sourceAtom := by
  change (ledger.residue binding.sourceResidue).incidence
      binding.citation.donorLocant = some binding.sourceAtom
  exact binding.source_eq

/-- Exact target-endpoint lookup for the bound citation. -/
theorem toLink_target_resolves (binding : Binding input ledger) :
    (ledger.residue binding.toLink.target).incidence binding.toLink.targetLocant =
      some binding.targetAtom := by
  change (ledger.residue binding.targetResidue).incidence
      binding.citation.acceptorLocant = some binding.targetAtom
  exact binding.target_eq

/-- Both converted link endpoints are participants of the bound actual source interaction. -/
theorem toLink_endpoint_correct (binding : Binding input ledger) :
    (∃ atom : Fin input.input.molecule.atomCount,
        (ledger.residue binding.toLink.source).incidence binding.toLink.sourceLocant =
            some atom ∧
          atom.val ∈ (ledger.interaction binding.toLink.interaction).participants) ∧
      (∃ atom : Fin input.input.molecule.atomCount,
        (ledger.residue binding.toLink.target).incidence binding.toLink.targetLocant =
            some atom ∧
          atom.val ∈ (ledger.interaction binding.toLink.interaction).participants) :=
  ⟨⟨binding.sourceAtom, binding.toLink_source_resolves, binding.source_participant⟩,
    ⟨binding.targetAtom, binding.toLink_target_resolves, binding.target_participant⟩⟩

/-- Exact metadata retention: the converted link uses precisely the supplied donor and acceptor
locants, and the recorded anomer is precisely the supplied anomer.  This theorem makes no
stereochemical-correctness claim. -/
theorem metadata_retained (binding : Binding input ledger) :
    binding.toLink.sourceLocant = binding.donorLocant ∧
      binding.toLink.targetLocant = binding.acceptorLocant ∧
      binding.anomer = binding.citation.anomer :=
  ⟨rfl, rfl, rfl⟩

end Binding

/-- Exact adapter constructor: bind a supplied glycosidic citation to explicit residues and an
actual source interaction, given the two locant resolutions and the two participant certificates.
This is the only way this adapter turns metadata into a link; locants are never guessed. -/
def bind (citation : Glycolipid1997.GlycosidicCitation)
    (sourceResidue targetResidue : Fin ledger.residueCount)
    (interaction : Fin input.input.molecule.interactions.length)
    (sourceAtom targetAtom : Fin input.input.molecule.atomCount)
    (source_eq : (ledger.residue sourceResidue).incidence citation.donorLocant = some sourceAtom)
    (target_eq : (ledger.residue targetResidue).incidence citation.acceptorLocant = some targetAtom)
    (source_participant :
      sourceAtom.val ∈ (input.input.molecule.interactions.get interaction).participants)
    (target_participant :
      targetAtom.val ∈ (input.input.molecule.interactions.get interaction).participants) :
    Binding input ledger where
  citation := citation
  sourceResidue := sourceResidue
  targetResidue := targetResidue
  interaction := interaction
  sourceAtom := sourceAtom
  targetAtom := targetAtom
  source_eq := source_eq
  target_eq := target_eq
  source_participant := source_participant
  target_participant := target_participant

@[simp] theorem bind_citation (citation : Glycolipid1997.GlycosidicCitation)
    (sourceResidue targetResidue : Fin ledger.residueCount)
    (interaction : Fin input.input.molecule.interactions.length)
    (sourceAtom targetAtom : Fin input.input.molecule.atomCount)
    (source_eq : (ledger.residue sourceResidue).incidence citation.donorLocant = some sourceAtom)
    (target_eq : (ledger.residue targetResidue).incidence citation.acceptorLocant = some targetAtom)
    (source_participant :
      sourceAtom.val ∈ (input.input.molecule.interactions.get interaction).participants)
    (target_participant :
      targetAtom.val ∈ (input.input.molecule.interactions.get interaction).participants) :
    (bind citation sourceResidue targetResidue interaction sourceAtom targetAtom
      source_eq target_eq source_participant target_participant).citation = citation := rfl

end GlycolipidCitationAdapter

namespace PhosphodiesterAdapter

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger NucleicAcid1970.SugarLocant input}

/-- A `NucleicAcid1970.DirectedPhosphodiester` bound to a sugar-locant ledger.  The direction
(`leftAttachment` to `rightAttachment`) is retained exactly; no direction is inferred. -/
structure Binding (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger NucleicAcid1970.SugarLocant input) where
  /-- The supplied source linkage metadata, retained verbatim. -/
  linkage : NucleicAcid1970.DirectedPhosphodiester
  sourceResidue : Fin ledger.residueCount
  targetResidue : Fin ledger.residueCount
  /-- Index of the actual source interaction that carries both resolved endpoints. -/
  interaction : Fin input.input.molecule.interactions.length
  sourceAtom : Fin input.input.molecule.atomCount
  targetAtom : Fin input.input.molecule.atomCount
  /-- The left attachment resolves to `sourceAtom` in the source residue. -/
  source_eq :
    (ledger.residue sourceResidue).incidence linkage.leftAttachment = some sourceAtom
  /-- The right attachment resolves to `targetAtom` in the target residue. -/
  target_eq :
    (ledger.residue targetResidue).incidence linkage.rightAttachment = some targetAtom
  source_participant :
    sourceAtom.val ∈ (input.input.molecule.interactions.get interaction).participants
  target_participant :
    targetAtom.val ∈ (input.input.molecule.interactions.get interaction).participants

namespace Binding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger NucleicAcid1970.SugarLocant input}

/-- The supplied left attachment locant, retained verbatim. -/
def leftAttachment (binding : Binding input ledger) : NucleicAcid1970.SugarLocant :=
  binding.linkage.leftAttachment

/-- The supplied right attachment locant, retained verbatim. -/
def rightAttachment (binding : Binding input ledger) : NucleicAcid1970.SugarLocant :=
  binding.linkage.rightAttachment

@[simp] theorem leftAttachment_eq (binding : Binding input ledger) :
    binding.leftAttachment = binding.linkage.leftAttachment := rfl

@[simp] theorem rightAttachment_eq (binding : Binding input ledger) :
    binding.rightAttachment = binding.linkage.rightAttachment := rfl

/-- Convert the bound phosphodiester metadata into a directed ledger link.  The link runs from the
supplied left attachment to the supplied right attachment; nothing is reoriented. -/
def toLink (binding : Binding input ledger) :
    DirectedResidueLink NucleicAcid1970.SugarLocant (Fin ledger.residueCount)
      input.input.molecule.interactions.length where
  source := binding.sourceResidue
  sourceLocant := binding.linkage.leftAttachment
  target := binding.targetResidue
  targetLocant := binding.linkage.rightAttachment
  interaction := binding.interaction

@[simp] theorem toLink_source (binding : Binding input ledger) :
    binding.toLink.source = binding.sourceResidue := rfl

@[simp] theorem toLink_target (binding : Binding input ledger) :
    binding.toLink.target = binding.targetResidue := rfl

@[simp] theorem toLink_sourceLocant (binding : Binding input ledger) :
    binding.toLink.sourceLocant = binding.linkage.leftAttachment := rfl

@[simp] theorem toLink_targetLocant (binding : Binding input ledger) :
    binding.toLink.targetLocant = binding.linkage.rightAttachment := rfl

@[simp] theorem toLink_interaction (binding : Binding input ledger) :
    binding.toLink.interaction = binding.interaction := rfl

/-- Exact source-endpoint lookup for the bound phosphodiester. -/
theorem toLink_source_resolves (binding : Binding input ledger) :
    (ledger.residue binding.toLink.source).incidence binding.toLink.sourceLocant =
      some binding.sourceAtom := by
  change (ledger.residue binding.sourceResidue).incidence
      binding.linkage.leftAttachment = some binding.sourceAtom
  exact binding.source_eq

/-- Exact target-endpoint lookup for the bound phosphodiester. -/
theorem toLink_target_resolves (binding : Binding input ledger) :
    (ledger.residue binding.toLink.target).incidence binding.toLink.targetLocant =
      some binding.targetAtom := by
  change (ledger.residue binding.targetResidue).incidence
      binding.linkage.rightAttachment = some binding.targetAtom
  exact binding.target_eq

/-- Both converted link endpoints are participants of the bound actual source interaction. -/
theorem toLink_endpoint_correct (binding : Binding input ledger) :
    (∃ atom : Fin input.input.molecule.atomCount,
        (ledger.residue binding.toLink.source).incidence binding.toLink.sourceLocant =
            some atom ∧
          atom.val ∈ (ledger.interaction binding.toLink.interaction).participants) ∧
      (∃ atom : Fin input.input.molecule.atomCount,
        (ledger.residue binding.toLink.target).incidence binding.toLink.targetLocant =
            some atom ∧
          atom.val ∈ (ledger.interaction binding.toLink.interaction).participants) :=
  ⟨⟨binding.sourceAtom, binding.toLink_source_resolves, binding.source_participant⟩,
    ⟨binding.targetAtom, binding.toLink_target_resolves, binding.target_participant⟩⟩

/-- Exact metadata retention: the converted link is precisely left attachment to right
attachment, and the interaction index is the supplied source index. -/
theorem metadata_retained (binding : Binding input ledger) :
    binding.toLink.sourceLocant = binding.linkage.leftAttachment ∧
      binding.toLink.targetLocant = binding.linkage.rightAttachment ∧
      binding.toLink.interaction = binding.interaction :=
  ⟨rfl, rfl, rfl⟩

end Binding

/-- Exact adapter constructor for phosphodiester metadata. -/
def bind (linkage : NucleicAcid1970.DirectedPhosphodiester)
    (sourceResidue targetResidue : Fin ledger.residueCount)
    (interaction : Fin input.input.molecule.interactions.length)
    (sourceAtom targetAtom : Fin input.input.molecule.atomCount)
    (source_eq :
      (ledger.residue sourceResidue).incidence linkage.leftAttachment = some sourceAtom)
    (target_eq :
      (ledger.residue targetResidue).incidence linkage.rightAttachment = some targetAtom)
    (source_participant :
      sourceAtom.val ∈ (input.input.molecule.interactions.get interaction).participants)
    (target_participant :
      targetAtom.val ∈ (input.input.molecule.interactions.get interaction).participants) :
    Binding input ledger where
  linkage := linkage
  sourceResidue := sourceResidue
  targetResidue := targetResidue
  interaction := interaction
  sourceAtom := sourceAtom
  targetAtom := targetAtom
  source_eq := source_eq
  target_eq := target_eq
  source_participant := source_participant
  target_participant := target_participant

@[simp] theorem bind_linkage (linkage : NucleicAcid1970.DirectedPhosphodiester)
    (sourceResidue targetResidue : Fin ledger.residueCount)
    (interaction : Fin input.input.molecule.interactions.length)
    (sourceAtom targetAtom : Fin input.input.molecule.atomCount)
    (source_eq :
      (ledger.residue sourceResidue).incidence linkage.leftAttachment = some sourceAtom)
    (target_eq :
      (ledger.residue targetResidue).incidence linkage.rightAttachment = some targetAtom)
    (source_participant :
      sourceAtom.val ∈ (input.input.molecule.interactions.get interaction).participants)
    (target_participant :
      targetAtom.val ∈ (input.input.molecule.interactions.get interaction).participants) :
    (bind linkage sourceResidue targetResidue interaction sourceAtom targetAtom
      source_eq target_eq source_participant target_participant).linkage = linkage := rfl

end PhosphodiesterAdapter

/-! ## Representability witnesses

These witnesses are deliberately small, but they exercise the *generic* ledger rather than a
bespoke special case: overlapping supports, the same locant token resolving differently in two
residues, a two-cycle in the directed link list, and a separate naming parent hierarchy. -/

namespace ResidueIncidenceWitness

/-- A concrete carbon atom for the two-atom witness. -/
def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

/-- Two carbon atoms joined by one single interaction. -/
def twoAtomMolecule : SemanticMolecule where
  atoms := [{ element := carbon }, { element := carbon }]
  interactions :=
    [{ participants := [0, 1], kind := SemanticInteractionKind.covalent 1 }]

theorem twoAtomMolecule_structurallyWellFormed : twoAtomMolecule.StructurallyWellFormed := by
  unfold SemanticMolecule.StructurallyWellFormed
  decide

/-- Certified two-atom source input. -/
def twoAtomInput : CertifiedAuthoritativeChemicalInput where
  input :=
    { molecule := twoAtomMolecule
      spatial? := none
      diagram? := none }
  structurallyWellFormed := ⟨twoAtomMolecule_structurallyWellFormed, trivial, trivial⟩

/-- First source atom index. -/
def atomZero : Fin twoAtomInput.input.molecule.atomCount := ⟨0, by decide⟩

/-- Second source atom index. -/
def atomOne : Fin twoAtomInput.input.molecule.atomCount := ⟨1, by decide⟩

/-- A residue whose support is the whole two-atom molecule.  `swap` reverses which atom each
Boolean locant denotes, exhibiting residue-scoped rather than global locant uniqueness. -/
def witnessFragment (swap : Bool) : ResidueFragment Bool twoAtomInput.input.molecule.atomCount where
  support := Finset.univ
  incidence locant := if xor locant swap then some atomZero else some atomOne
  incidence_mem_support := by
    intro locant atom _found
    simp

/-- The single raw link used twice (in opposite directions) by the witness. -/
def linkZero : DirectedResidueLink Bool Bool
    twoAtomInput.input.molecule.interactions.length :=
  { source := false
    sourceLocant := true
    target := true
    targetLocant := true
    interaction := ⟨0, by decide⟩ }

/-- The reversed raw link. -/
def linkOne : DirectedResidueLink Bool Bool
    twoAtomInput.input.molecule.interactions.length :=
  { source := true
    sourceLocant := true
    target := false
    targetLocant := true
    interaction := ⟨0, by decide⟩ }

/-- The raw directed link list: a two-cycle. -/
def witnessLinks : List (DirectedResidueLink Bool Bool
    twoAtomInput.input.molecule.interactions.length) :=
  [linkZero, linkOne]

/-- The separate naming parent hierarchy: residue `true` has parent `false`. -/
def witnessRawHierarchy : RawResidueParentHierarchy Bool where
  parent residue := if residue then some false else none
  rank residue := if residue then 1 else 0
  parent_rank_lt := by
    intro child parentResidue edge
    cases child <;> cases parentResidue <;> simp_all

/-- Independent raw witness data. -/
def witnessRaw : RawResidueIncidence Bool Bool twoAtomInput where
  fragment := witnessFragment
  links := witnessLinks
  link_source_mem := by
    intro link member
    simp only [witnessLinks, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨atomZero, by decide, by decide⟩
    · exact ⟨atomOne, by decide, by decide⟩
  link_target_mem := by
    intro link member
    simp only [witnessLinks, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨atomOne, by decide, by decide⟩
    · exact ⟨atomZero, by decide, by decide⟩
  hierarchy? := some witnessRawHierarchy

/-- Explicit computable bijection `Bool ≃ Fin 2`. -/
def boolFinTwo : Bool ≃ Fin 2 where
  toFun residue := if residue then ⟨1, by decide⟩ else ⟨0, by decide⟩
  invFun index := decide (index.val = 1)
  left_inv residue := by cases residue <;> rfl
  right_inv index := by fin_cases index <;> rfl

/-- The cardinality of `Bool`. -/
theorem card_bool : Fintype.card Bool = 2 := by decide

/-- Explicit computable bijection `Bool ≃ Fin (Fintype.card Bool)`, obtained from `boolFinTwo`
by casting the finite index type along the (proof-irrelevant) cardinality equality. -/
def boolEnumeration : Bool ≃ Fin (Fintype.card Bool) :=
  boolFinTwo.trans (finCongr card_bool.symm)

@[simp] theorem boolEnumeration_false :
    boolEnumeration false = (⟨0, by decide⟩ : Fin (Fintype.card Bool)) := rfl

@[simp] theorem boolEnumeration_true :
    boolEnumeration true = (⟨1, by decide⟩ : Fin (Fintype.card Bool)) := rfl

/-- The witness ledger, built through the generic constructor. -/
def witnessLedger : ResidueIncidenceLedger Bool twoAtomInput :=
  witnessRaw.toLedger boolEnumeration

/-- The transported naming parent hierarchy. -/
def witnessHierarchy : ResidueParentHierarchy witnessLedger.residueCount :=
  RawResidueIncidence.mapHierarchy boolEnumeration witnessRawHierarchy

theorem witness_links_length : witnessLedger.links.length = 2 := by
  change (witnessRaw.toLedger boolEnumeration).links.length = 2
  rw [RawResidueIncidence.toLedger_links_length]
  rfl

/-- The directed link list has a two-cycle. -/
theorem witness_link_cycle :
    ∃ first ∈ witnessLedger.links, ∃ second ∈ witnessLedger.links,
      first.source = second.target ∧ first.target = second.source := by
  have mapped : witnessLedger.links =
      witnessRaw.links.map (witnessRaw.mapLink boolEnumeration) := rfl
  refine ⟨witnessRaw.mapLink boolEnumeration linkZero, ?_,
    witnessRaw.mapLink boolEnumeration linkOne, ?_, rfl, rfl⟩
  · rw [mapped]
    exact List.mem_map.mpr ⟨linkZero, by simp [witnessRaw, witnessLinks], rfl⟩
  · rw [mapped]
    exact List.mem_map.mpr ⟨linkOne, by simp [witnessRaw, witnessLinks], rfl⟩

/-- Two distinct residues share the whole atom support. -/
theorem witness_supports_overlap :
    ∃ first second : Fin witnessLedger.residueCount, first ≠ second ∧
      ((witnessLedger.residue first).support ∩
        (witnessLedger.residue second).support).Nonempty := by
  refine ⟨boolEnumeration false, boolEnumeration true, ?_, ?_⟩
  · intro equal
    have values := congrArg Fin.val equal
    rw [boolEnumeration_false, boolEnumeration_true] at values
    simp at values
  · exact ⟨atomZero, by simp [witnessLedger, witnessRaw, RawResidueIncidence.toLedger,
      witnessFragment]⟩

/-- The same locant token denotes different atoms in different residues, so locants are scoped by
residue and never assumed globally unique. -/
theorem witness_same_locant_scoped :
    witnessLedger.resolve? (boolEnumeration false) true = some atomZero ∧
      witnessLedger.resolve? (boolEnumeration true) true = some atomOne := by
  constructor <;> decide

/-- The naming parent hierarchy is present. -/
theorem witness_hierarchy_present :
    witnessLedger.hierarchy? = some witnessHierarchy := rfl

/-- Its parent edge runs from the `true` residue to the `false` residue, independently of the
two-cycle in the directed link list. -/
theorem witness_hierarchy_parent :
    witnessHierarchy.parent (boolEnumeration true) = some (boolEnumeration false) := by
  simp [witnessHierarchy, RawResidueIncidence.mapHierarchy, witnessRawHierarchy]

end ResidueIncidenceWitness

end TetraStereo.OneCenter
