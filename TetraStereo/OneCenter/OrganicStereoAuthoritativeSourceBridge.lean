import TetraStereo.OneCenter.OrganicStereoDiagramEncoding

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact ingress from certified authoritative input to independent finite sources

This module closes the *source-ingress* direction of the representation bridge.  Starting from an
arbitrary `CertifiedAuthoritativeChemicalInput` — that is, a format-neutral `SemanticMolecule`
together with the kernel-checked structural certificate and either optional evidence channel — it
constructs an independent-label finite source carrying

* a genuine `FiniteAtomInteractionHypergraph (Fin atomCount)` whose atoms and interaction
  occurrences are recovered constructively from the stored atom list and the stored ordered
  interaction list, using the bounds supplied by the certificate (no preimage is assumed),
* `Option (Fin atomCount → CartesianPoint3)` for the rational spatial channel, with absence
  preserved as `none` (no origin is invented), and
* `Option (OrganicDiagramSource (Fin atomCount))` for the drawing channel, with absence preserved
  as `none`.

The reconstruction is then proved to be an exact left inverse of the existing encoders:
`OrganicFiniteSource.encode (decode certified) = certified.input`, including atom order,
interaction order, participant order, every interaction kind (including `.other` authority codes),
every broad element/electronic atom field, the exact rational coordinates, the entire drawing
configuration, and both cases of channel absence.

The carrier deliberately contains only the graph, the optional coordinate function and the
optional drawing source.  The original `AuthoritativeChemicalInput` is never hidden in a field.

Nothing here decides chemical admissibility, localized closed-shell applicability, descriptor
values, or a graphical interpretation of parity tokens.  It is a representation theorem only.
-/

/-! ## Atom data of the reconstructed graph -/

namespace SemanticInteraction

/-- Every participant of a well-formed interaction is an in-range atom index.  This is the bound
used by the reconstruction; it is extracted from the stored certificate rather than assumed. -/
theorem WellFormed_participant_lt {interaction : SemanticInteraction} {atomCount : ℕ}
    (wellFormed : interaction.WellFormed atomCount) {atom : ℕ}
    (member : atom ∈ interaction.participants) : atom < atomCount := by
  have hall : interaction.participants.all
      (fun atom => decide (atom < atomCount)) = true := wellFormed.2.2
  exact of_decide_eq_true (List.all_eq_true.mp hall atom member)

end SemanticInteraction

/-! ## The independent source carrier -/

/-- An independent-label finite molecular source.  Atom labels are an arbitrary finite type `V`
together with a decidable equality; the graph stores complete semantic atom data under those
labels, and the two optional evidence channels store positions over the same labels.  Absence of
an evidence channel is `none`. -/
structure OrganicFiniteSource (V : Type*) [DecidableEq V] [Fintype V] where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none

namespace OrganicFiniteSource

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Encode an optional total coordinate function as the existing all-or-nothing spatial channel.
`none` stays `none`; a present function is materialised in enumeration order. -/
def encodeSpatial? (e : V ≃ Fin (Fintype.card V)) :
    Option (V → CartesianPoint3) → Option SpatialConfiguration
  | none => none
  | some positions =>
      some { positions := List.ofFn fun index : Fin (Fintype.card V) =>
        positions (e.symm index) }

omit [DecidableEq V] in
@[simp] theorem encodeSpatial?_none (e : V ≃ Fin (Fintype.card V)) :
    encodeSpatial? e none = none := rfl

omit [DecidableEq V] in
@[simp] theorem encodeSpatial?_some (e : V ≃ Fin (Fintype.card V))
    (positions : V → CartesianPoint3) :
    encodeSpatial? e (some positions) =
      some { positions := List.ofFn fun index : Fin (Fintype.card V) =>
        positions (e.symm index) } := rfl

/-- Encode the independent source into the existing authoritative input.  The molecule is the
graph encoding under the supplied enumeration, the spatial channel is materialised from the
optional coordinate function, and the diagram channel is the encoded optional drawing source. -/
def encode (source : OrganicFiniteSource V) (e : V ≃ Fin (Fintype.card V)) :
    AuthoritativeChemicalInput :=
  { molecule := source.graph.encode e
    spatial? := encodeSpatial? e source.spatial?
    diagram? := source.diagram?.map (OrganicDiagramSource.encodeDiagram e) }

@[simp] theorem encode_molecule (source : OrganicFiniteSource V)
    (e : V ≃ Fin (Fintype.card V)) :
    (source.encode e).molecule = source.graph.encode e := rfl

@[simp] theorem encode_spatial? (source : OrganicFiniteSource V)
    (e : V ≃ Fin (Fintype.card V)) :
    (source.encode e).spatial? = encodeSpatial? e source.spatial? := rfl

@[simp] theorem encode_diagram? (source : OrganicFiniteSource V)
    (e : V ≃ Fin (Fintype.card V)) :
    (source.encode e).diagram? =
      source.diagram?.map (OrganicDiagramSource.encodeDiagram e) := rfl

end OrganicFiniteSource

/-! ## The identity enumeration on `Fin n`

The reconstruction uses `Fin atomCount` as its carrier.  `FiniteAtomInteractionHypergraph.encode`
expects an equivalence to `Fin (Fintype.card V)`, so we use the canonical comparison equivalence
`Fin n ≃ Fin (Fintype.card (Fin n))`, which preserves the underlying natural value definitionally.
-/

/-- The identity comparison equivalence between `Fin n` and `Fin (Fintype.card (Fin n))`.  Its
forward and inverse maps both preserve the underlying `Nat` value definitionally. -/
def identityEnumeration (n : ℕ) : Fin n ≃ Fin (Fintype.card (Fin n)) where
  toFun index := ⟨index.val,
    Nat.lt_of_lt_of_eq index.isLt (Fintype.card_fin n).symm⟩
  invFun index := ⟨index.val,
    Nat.lt_of_lt_of_eq index.isLt (Fintype.card_fin n)⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

@[simp] theorem identityEnumeration_apply_val (n : ℕ) (index : Fin n) :
    (identityEnumeration n index).val = index.val := rfl

@[simp] theorem identityEnumeration_symm_apply_val (n : ℕ)
    (index : Fin (Fintype.card (Fin n))) :
    ((identityEnumeration n).symm index).val = index.val := rfl

/-! ## List and partial-map helpers -/

/-- Recover a list from a function over an index type of the same length.  This is the
length-cast form of `List.ofFn_get` used for atom lists, coordinate lists and bond lists whose
declared length is an equality hypothesis rather than a definitional unfolding. -/
private theorem ofFn_eq_list_of_get {α : Type*} {m : ℕ} {l : List α} (hlen : m = l.length)
    (f : Fin m → α)
    (h : ∀ index : Fin m, f index = l.get (Fin.cast hlen index)) :
    List.ofFn f = l := by
  rw [List.ofFn_congr hlen]
  have hfun : (fun index : Fin l.length => f (Fin.cast hlen.symm index)) =
      (fun index : Fin l.length => l.get index) := by
    funext index
    have hcast : Fin.cast hlen (Fin.cast hlen.symm index) = index := Fin.ext rfl
    rw [← hcast]
    exact h (Fin.cast hlen.symm index)
  rw [hfun]
  exact List.ofFn_get l

/-- Mapping a partial map by a pointwise inverse recovers the source list.  This is stated for an
arbitrary predicate and an arbitrary target type so that it applies to the membership-indexed
partial maps used below. -/
private theorem map_pmap_map_eq_self {α β : Type*} {p : α → Prop} (l : List α)
    (f : ∀ a, p a → β) (g : β → α) (H : ∀ a ∈ l, p a)
    (h : ∀ (a : α) (ha : p a), g (f a ha) = a) :
    (l.pmap f H).map g = l := by
  rw [List.pmap_eq_map_attach, List.map_map]
  have hmap : List.map (g ∘ fun x => f x.1 (H x.1 x.2)) l.attach =
      l.attach.map Subtype.val := by
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    simpa using h x.1 (H x.1 x.2)
  rw [hmap, List.attach_map_subtype_val]

/-- `List.get` only depends on the underlying natural value of its index. -/
private theorem list_get_congr_val {α : Type*} {l : List α} {first second : Fin l.length}
    (h : first.val = second.val) : l.get first = l.get second := by
  rw [Fin.ext h]

/-! ## Reconstructing the graph from the stored atom and interaction lists -/

/-- One participant list mapped into independent atom labels, using the bounds from the stored
well-formedness certificate. -/
def reconstructParticipants (atomCount : ℕ) (interaction : SemanticInteraction)
    (wellFormed : interaction.WellFormed atomCount) : List (Fin atomCount) :=
  interaction.participants.pmap
    (fun atom member => ⟨atom,
      SemanticInteraction.WellFormed_participant_lt wellFormed member⟩)
    (fun _ member => member)

/-- One stored interaction occurrence, with participants rebuilt as genuine `Fin atomCount`
labels and the kind copied verbatim.  No participant index is defaulted and no invalid label is
constructed: every label carries the bound extracted from the certificate at that occurrence. -/
def reconstructEdge (atomCount : ℕ) (interaction : SemanticInteraction)
    (wellFormed : interaction.WellFormed atomCount) :
    List (Fin atomCount) × SemanticInteractionKind :=
  (reconstructParticipants atomCount interaction wellFormed, interaction.kind)

@[simp] theorem reconstructEdge_participants (atomCount : ℕ)
    (interaction : SemanticInteraction) (wellFormed : interaction.WellFormed atomCount) :
    (reconstructEdge atomCount interaction wellFormed).1 =
      reconstructParticipants atomCount interaction wellFormed := rfl

@[simp] theorem reconstructEdge_kind (atomCount : ℕ)
    (interaction : SemanticInteraction) (wellFormed : interaction.WellFormed atomCount) :
    (reconstructEdge atomCount interaction wellFormed).2 = interaction.kind := rfl

theorem reconstructParticipants_arity (atomCount : ℕ) (interaction : SemanticInteraction)
    (wellFormed : interaction.WellFormed atomCount) :
    2 ≤ (reconstructParticipants atomCount interaction wellFormed).length := by
  unfold reconstructParticipants
  rw [List.length_pmap]
  exact wellFormed.1

theorem reconstructParticipants_nodup (atomCount : ℕ) (interaction : SemanticInteraction)
    (wellFormed : interaction.WellFormed atomCount) :
    (reconstructParticipants atomCount interaction wellFormed).Nodup := by
  unfold reconstructParticipants
  exact List.Pairwise.pmap (l := interaction.participants)
    (R := fun left right => left ≠ right)
    (p := fun atom => atom ∈ interaction.participants)
    (f := fun atom member =>
      ⟨atom, SemanticInteraction.WellFormed_participant_lt wellFormed member⟩)
    (S := fun left right => left ≠ right)
    wellFormed.2.1 (fun _ member => member)
    (fun a _ b _ equal equalFin => equal (congrArg Fin.val equalFin))

theorem reconstructEdge_arity (atomCount : ℕ) (interaction : SemanticInteraction)
    (wellFormed : interaction.WellFormed atomCount) :
    2 ≤ (reconstructEdge atomCount interaction wellFormed).1.length := by
  simpa using reconstructParticipants_arity atomCount interaction wellFormed

theorem reconstructEdge_nodup (atomCount : ℕ) (interaction : SemanticInteraction)
    (wellFormed : interaction.WellFormed atomCount) :
    (reconstructEdge atomCount interaction wellFormed).1.Nodup := by
  simpa using reconstructParticipants_nodup atomCount interaction wellFormed

/-- Reconstruct the ordered interaction list.  Each occurrence carries its own certificate,
extracted from the whole-molecule structural certificate by membership. -/
def reconstructInteractions (atomCount : ℕ) (interactions : List SemanticInteraction)
    (wellFormed : ∀ interaction, interaction ∈ interactions →
      interaction.WellFormed atomCount) :
    List (List (Fin atomCount) × SemanticInteractionKind) :=
  interactions.pmap
    (fun interaction member =>
      reconstructEdge atomCount interaction (wellFormed interaction member))
    (fun _ member => member)

theorem reconstructInteractions_arity (atomCount : ℕ) (interactions : List SemanticInteraction)
    (wellFormed : ∀ interaction, interaction ∈ interactions →
      interaction.WellFormed atomCount) :
    ∀ edge ∈ reconstructInteractions atomCount interactions wellFormed,
      2 ≤ edge.1.length := by
  intro edge member
  unfold reconstructInteractions at member
  rw [List.mem_pmap] at member
  obtain ⟨interaction, hmem, rfl⟩ := member
  exact reconstructEdge_arity atomCount interaction (wellFormed interaction hmem)

theorem reconstructInteractions_nodup (atomCount : ℕ) (interactions : List SemanticInteraction)
    (wellFormed : ∀ interaction, interaction ∈ interactions →
      interaction.WellFormed atomCount) :
    ∀ edge ∈ reconstructInteractions atomCount interactions wellFormed,
      edge.1.Nodup := by
  intro edge member
  unfold reconstructInteractions at member
  rw [List.mem_pmap] at member
  obtain ⟨interaction, hmem, rfl⟩ := member
  exact reconstructEdge_nodup atomCount interaction (wellFormed interaction hmem)

/-- Extract per-occurrence well-formedness from the whole-molecule structural certificate. -/
def interactionWellFormed (molecule : SemanticMolecule)
    (wellFormed : molecule.StructurallyWellFormed) :
    ∀ interaction, interaction ∈ molecule.interactions →
      interaction.WellFormed molecule.atomCount :=
  fun interaction member => by
    have hall : molecule.interactions.all
        (fun interaction => interaction.wellFormed? molecule.atomCount) = true := wellFormed
    exact (SemanticInteraction.wellFormed?_eq_true_iff interaction
      molecule.atomCount).mp (List.all_eq_true.mp hall interaction member)

/-- Reconstruct a genuine finite atom-interaction hypergraph over `Fin molecule.atomCount` from
the stored atom list and the stored ordered interaction list.  The atom list is read position by
position; the interaction list keeps its order, and each participant is rebuilt as the genuine
`Fin` label carrying the bound stored in the certificate. -/
def reconstructGraph (molecule : SemanticMolecule)
    (wellFormed : molecule.StructurallyWellFormed) :
    FiniteAtomInteractionHypergraph (Fin molecule.atomCount) :=
  let semanticWellFormed := interactionWellFormed molecule wellFormed
  { atomData := fun index => molecule.atoms.get index
    interactions := reconstructInteractions molecule.atomCount molecule.interactions
      semanticWellFormed
    arity_ge_two := fun edge member =>
      reconstructInteractions_arity molecule.atomCount molecule.interactions
        semanticWellFormed edge member
    participants_nodup := fun edge member =>
      reconstructInteractions_nodup molecule.atomCount molecule.interactions
        semanticWellFormed edge member }

@[simp] theorem reconstructGraph_atomData (molecule : SemanticMolecule)
    (wellFormed : molecule.StructurallyWellFormed) (index : Fin molecule.atomCount) :
    (reconstructGraph molecule wellFormed).atomData index = molecule.atoms.get index := rfl

@[simp] theorem reconstructGraph_interactions (molecule : SemanticMolecule)
    (wellFormed : molecule.StructurallyWellFormed) :
    (reconstructGraph molecule wellFormed).interactions =
      reconstructInteractions molecule.atomCount molecule.interactions
        (interactionWellFormed molecule wellFormed) := rfl

/-! ## Encoding the reconstructed graph is the identity on the molecule -/

/-- Participant order, multiplicity and the complete participant list are recovered exactly. -/
theorem map_encode_reconstructParticipants (n : ℕ)
    (e : Fin n ≃ Fin (Fintype.card (Fin n)))
    (hval : ∀ index : Fin n, (e index).val = index.val)
    (interaction : SemanticInteraction) (wellFormed : interaction.WellFormed n) :
    (reconstructParticipants n interaction wellFormed).map
        (fun atom => (e atom).val) = interaction.participants := by
  rw [show (fun atom : Fin n => (e atom).val) = Fin.val from funext hval]
  unfold reconstructParticipants
  exact map_pmap_map_eq_self interaction.participants
    (fun atom member =>
      ⟨atom, SemanticInteraction.WellFormed_participant_lt wellFormed member⟩)
    Fin.val (fun _ member => member) (fun _ _ => rfl)

/-- Encoding a reconstructed interaction occurrence recovers the source occurrence exactly:
participant order and kind are both identities. -/
theorem encodeInteraction_reconstructEdge (n : ℕ)
    (e : Fin n ≃ Fin (Fintype.card (Fin n)))
    (hval : ∀ index : Fin n, (e index).val = index.val)
    (interaction : SemanticInteraction) (wellFormed : interaction.WellFormed n) :
    FiniteAtomInteractionHypergraph.encodeInteraction e
        (reconstructEdge n interaction wellFormed) = interaction := by
  cases interaction with
  | mk participants kind =>
      have hpart : (reconstructParticipants n
            { participants := participants, kind := kind } wellFormed).map
            (fun atom => (e atom).val) = participants :=
        map_encode_reconstructParticipants n e hval
          { participants := participants, kind := kind } wellFormed
      simp only [reconstructEdge, FiniteAtomInteractionHypergraph.encodeInteraction]
      rw [hpart]

/-- The ordered interaction list of the reconstructed graph encodes back to the stored ordered
interaction list exactly. -/
theorem map_encode_reconstructInteractions (n : ℕ)
    (e : Fin n ≃ Fin (Fintype.card (Fin n)))
    (hval : ∀ index : Fin n, (e index).val = index.val)
    (interactions : List SemanticInteraction)
    (wellFormed : ∀ interaction, interaction ∈ interactions → interaction.WellFormed n) :
    (reconstructInteractions n interactions wellFormed).map
        (FiniteAtomInteractionHypergraph.encodeInteraction e) = interactions := by
  unfold reconstructInteractions
  exact map_pmap_map_eq_self interactions
    (fun interaction member => reconstructEdge n interaction (wellFormed interaction member))
    (FiniteAtomInteractionHypergraph.encodeInteraction e)
    (fun _ member => member)
    (fun interaction member =>
      encodeInteraction_reconstructEdge n e hval interaction (wellFormed interaction member))

/-- Helper extension theorem for `SemanticMolecule`. -/
theorem semanticMolecule_ext {first second : SemanticMolecule}
    (atomsEqual : first.atoms = second.atoms)
    (interactionsEqual : first.interactions = second.interactions) : first = second := by
  cases first
  cases second
  simp_all

/-- **Exact molecule reconstruction.**  Encoding the reconstructed graph under the identity
enumeration yields exactly the stored `SemanticMolecule`: atom order and every atom field,
interaction occurrence order, participant order, and every interaction kind. -/
theorem reconstructGraph_encode (molecule : SemanticMolecule)
    (wellFormed : molecule.StructurallyWellFormed) :
    (reconstructGraph molecule wellFormed).encode
        (identityEnumeration molecule.atomCount) = molecule := by
  apply semanticMolecule_ext
  · show List.ofFn (fun index : Fin (Fintype.card (Fin molecule.atomCount)) =>
        molecule.atoms.get ((identityEnumeration molecule.atomCount).symm index)) =
      molecule.atoms
    apply ofFn_eq_list_of_get (m := Fintype.card (Fin molecule.atomCount))
      (l := molecule.atoms) (hlen := Fintype.card_fin molecule.atomCount)
    intro index
    exact list_get_congr_val (l := molecule.atoms) (h := rfl)
  · show (reconstructInteractions molecule.atomCount molecule.interactions
        (interactionWellFormed molecule wellFormed)).map
        (FiniteAtomInteractionHypergraph.encodeInteraction
          (identityEnumeration molecule.atomCount)) = molecule.interactions
    exact map_encode_reconstructInteractions molecule.atomCount
      (identityEnumeration molecule.atomCount) (fun _ => rfl)
      molecule.interactions (interactionWellFormed molecule wellFormed)

/-! ## Decoding the optional spatial channel -/

/-- Unpack the length condition for a present spatial configuration from the certificate. -/
theorem spatialFits_of_wf (input : AuthoritativeChemicalInput)
    (wellFormed : input.SpatialIndicesWellFormed) (spatial : SpatialConfiguration)
    (observed : input.spatial? = some spatial) :
    spatial.positions.length = input.molecule.atomCount := by
  unfold AuthoritativeChemicalInput.SpatialIndicesWellFormed at wellFormed
  rw [observed] at wellFormed
  exact wellFormed

/-- Decode a stored coordinate list into an independent total coordinate function.  Every index
is in range because the certificate states the list length. -/
def decodeSpatial (spatial : SpatialConfiguration) (atomCount : ℕ)
    (fits : spatial.positions.length = atomCount) :
    Fin atomCount → CartesianPoint3 :=
  fun index => spatial.positions.get ⟨index.val, by rw [fits]; exact index.isLt⟩

/-- Decode the optional spatial channel.  Absence is preserved as `none`; a present
configuration becomes a total function on the atom labels. -/
def decodeSpatial? (input : AuthoritativeChemicalInput)
    (wellFormed : input.SpatialIndicesWellFormed) :
    Option (Fin input.molecule.atomCount → CartesianPoint3) :=
  match observed : input.spatial? with
  | none => none
  | some spatial =>
      some (decodeSpatial spatial input.molecule.atomCount
        (spatialFits_of_wf input wellFormed spatial observed))

/-- Reduction lemma for the present case of the optional spatial channel. -/
theorem decodeSpatial?_some (input : AuthoritativeChemicalInput)
    (wellFormed : input.SpatialIndicesWellFormed) (spatial : SpatialConfiguration)
    (observed : input.spatial? = some spatial) :
    decodeSpatial? input wellFormed =
      some (decodeSpatial spatial input.molecule.atomCount
        (spatialFits_of_wf input wellFormed spatial observed)) := by
  rcases input with ⟨molecule, spatial?, diagram?⟩
  unfold AuthoritativeChemicalInput.SpatialIndicesWellFormed at wellFormed
  cases spatial? with
  | none => simp at observed
  | some actual =>
      simp only [Option.some.injEq] at observed
      subst actual
      rfl

/-- Helper extension theorem for `SpatialConfiguration`. -/
theorem spatialConfiguration_ext {first second : SpatialConfiguration}
    (positionsEqual : first.positions = second.positions) : first = second := by
  cases first
  cases second
  simp_all

/-- Encode-decode round trip for a present spatial configuration: the recovered function stores
exactly the original coordinate list in enumeration order. -/
theorem encodeSpatial_decodeSpatial (n : ℕ) (spatial : SpatialConfiguration)
    (fits : spatial.positions.length = n) :
    OrganicFiniteSource.encodeSpatial? (identityEnumeration n)
        (some (decodeSpatial spatial n fits)) = some spatial := by
  simp only [OrganicFiniteSource.encodeSpatial?]
  congr 1
  apply spatialConfiguration_ext
  apply ofFn_eq_list_of_get (l := spatial.positions)
    (hlen := (Fintype.card_fin n).trans fits.symm)
  intro index
  exact list_get_congr_val (h := rfl)

/-- Decoding the nullary spatial channel yields `none`. -/
@[simp] theorem decodeSpatial?_none (input : AuthoritativeChemicalInput)
    (wellFormed : input.SpatialIndicesWellFormed)
    (absent : input.spatial? = none) :
    decodeSpatial? input wellFormed = none := by
  rcases input with ⟨molecule, spatial?, diagram?⟩
  unfold AuthoritativeChemicalInput.SpatialIndicesWellFormed at wellFormed
  cases spatial? with
  | none => rfl
  | some spatial => simp at absent

/-- **Exact spatial round trip**, including absence. -/
theorem encodeSpatial?_decodeSpatial? (input : AuthoritativeChemicalInput)
    (wellFormed : input.SpatialIndicesWellFormed) :
    OrganicFiniteSource.encodeSpatial? (identityEnumeration input.molecule.atomCount)
        (decodeSpatial? input wellFormed) = input.spatial? := by
  cases observed : input.spatial? with
  | none =>
      rw [decodeSpatial?_none input wellFormed observed]
      rfl
  | some spatial =>
      rw [decodeSpatial?_some input wellFormed spatial observed]
      exact encodeSpatial_decodeSpatial input.molecule.atomCount spatial
        (spatialFits_of_wf input wellFormed spatial observed)

/-! ## Decoding the optional diagram channel -/

/-- Extract the positions-length condition from the diagram certificate. -/
theorem diagramPositionsFits_of_wf (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) (diagram : DiagramConfiguration)
    (observed : input.diagram? = some diagram) :
    ∀ positions, diagram.atomPositions? = some positions →
      positions.length = input.molecule.atomCount := by
  intro positions present
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  rw [observed] at wellFormed
  have hpos := wellFormed.1
  rw [present] at hpos
  exact hpos

/-- Extract the bond-endpoint condition from the diagram certificate. -/
theorem diagramBondOk_of_wf (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) (diagram : DiagramConfiguration)
    (observed : input.diagram? = some diagram) :
    diagram.bonds.all (fun bond =>
      decide (bond.source < input.molecule.atomCount) &&
        decide (bond.target < input.molecule.atomCount) &&
          decide (bond.source ≠ bond.target)) = true := by
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  rw [observed] at wellFormed
  exact wellFormed.2.1

/-- Extract the atom-configuration condition from the diagram certificate. -/
theorem diagramAtomOk_of_wf (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) (diagram : DiagramConfiguration)
    (observed : input.diagram? = some diagram) :
    diagram.atomConfigurations.all
      (fun configuration => decide (configuration.atom < input.molecule.atomCount)) = true := by
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  rw [observed] at wellFormed
  exact wellFormed.2.2

/-- A bond endpoint bound follows from the stored `all` condition. -/
theorem diagramBond_source_lt {atomCount : ℕ} {bonds : List DiagramBond}
    (ok : bonds.all (fun bond =>
      decide (bond.source < atomCount) && decide (bond.target < atomCount) &&
        decide (bond.source ≠ bond.target)) = true)
    {bond : DiagramBond} (member : bond ∈ bonds) : bond.source < atomCount := by
  have h := List.all_eq_true.mp ok bond member
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact h.1.1

/-- A bond endpoint bound follows from the stored `all` condition. -/
theorem diagramBond_target_lt {atomCount : ℕ} {bonds : List DiagramBond}
    (ok : bonds.all (fun bond =>
      decide (bond.source < atomCount) && decide (bond.target < atomCount) &&
        decide (bond.source ≠ bond.target)) = true)
    {bond : DiagramBond} (member : bond ∈ bonds) : bond.target < atomCount := by
  have h := List.all_eq_true.mp ok bond member
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact h.1.2

/-- An atom-configuration bound follows from the stored `all` condition. -/
theorem diagramAtom_lt {atomCount : ℕ}
    {configurations : List DiagramAtomConfiguration}
    (ok : configurations.all
      (fun configuration => decide (configuration.atom < atomCount)) = true)
    {configuration : DiagramAtomConfiguration}
    (member : configuration ∈ configurations) :
    configuration.atom < atomCount := by
  have h := List.all_eq_true.mp ok configuration member
  exact of_decide_eq_true h

/-- Decode a stored two-dimensional position list into a total function on atom labels. -/
def decodeDiagramPositions (positions : List CartesianPoint2) (atomCount : ℕ)
    (fits : positions.length = atomCount) : Fin atomCount → CartesianPoint2 :=
  fun index => positions.get ⟨index.val, by rw [fits]; exact index.isLt⟩

/-- Decode one drawing bond occurrence into independent atom labels, preserving endpoint order,
style and scope (including group numbers). -/
def decodeDiagramBond (atomCount : ℕ) (bond : DiagramBond)
    (sourceBound : bond.source < atomCount) (targetBound : bond.target < atomCount) :
    SourceDiagramBond (Fin atomCount) :=
  { source := ⟨bond.source, sourceBound⟩
    target := ⟨bond.target, targetBound⟩
    style := bond.style
    scope := bond.scope }

/-- Decode one atom-parity annotation into independent atom labels, preserving the parity token
and scope syntactically. -/
def decodeDiagramAtom (atomCount : ℕ) (configuration : DiagramAtomConfiguration)
    (bound : configuration.atom < atomCount) : SourceDiagramAtom (Fin atomCount) :=
  { atom := ⟨configuration.atom, bound⟩
    parity := configuration.parity
    scope := configuration.scope }

/-- Decode the optional drawing position list.  `none` is preserved; a present list becomes a
total function on the atom labels, using the stored length bound. -/
def decodeDiagramPositions? (diagram : DiagramConfiguration) (atomCount : ℕ)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = atomCount) : Option (Fin atomCount → CartesianPoint2) :=
  match observed : diagram.atomPositions? with
  | none => none
  | some positions =>
      some (decodeDiagramPositions positions atomCount (positionsFit positions observed))

/-- Reduction lemma for an absent drawing position list. -/
theorem decodeDiagramPositions?_none (diagram : DiagramConfiguration) (atomCount : ℕ)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = atomCount)
    (absent : diagram.atomPositions? = none) :
    decodeDiagramPositions? diagram atomCount positionsFit = none := by
  rcases diagram with ⟨atomPositions?, bonds, atomConfigurations⟩
  cases atomPositions? with
  | none => rfl
  | some positions => simp at absent

/-- Reduction lemma for a present drawing position list. -/
theorem decodeDiagramPositions?_some (diagram : DiagramConfiguration) (atomCount : ℕ)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = atomCount)
    (positions : List CartesianPoint2)
    (observed : diagram.atomPositions? = some positions) :
    decodeDiagramPositions? diagram atomCount positionsFit =
      some (decodeDiagramPositions positions atomCount
        (positionsFit positions observed)) := by
  rcases diagram with ⟨atomPositions?, bonds, atomConfigurations⟩
  cases atomPositions? with
  | none => simp at observed
  | some actual =>
      simp only [Option.some.injEq] at observed
      subst actual
      rfl

/-- Decode a complete drawing configuration into independent drawing evidence.  Positions are
optional and absence is preserved; bond and parity occurrences keep their order and multiplicity. -/
def decodeDiagram (diagram : DiagramConfiguration) (atomCount : ℕ)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = atomCount)
    (bondsOk : diagram.bonds.all (fun bond =>
      decide (bond.source < atomCount) && decide (bond.target < atomCount) &&
        decide (bond.source ≠ bond.target)) = true)
    (atomConfigurationsOk : diagram.atomConfigurations.all
      (fun configuration => decide (configuration.atom < atomCount)) = true) :
    OrganicDiagramSource (Fin atomCount) :=
  { positions? := decodeDiagramPositions? diagram atomCount positionsFit
    bonds := diagram.bonds.pmap
      (fun bond member => decodeDiagramBond atomCount bond
        (diagramBond_source_lt bondsOk member)
        (diagramBond_target_lt bondsOk member))
      (fun _ member => member)
    atomConfigurations := diagram.atomConfigurations.pmap
      (fun configuration member => decodeDiagramAtom atomCount configuration
        (diagramAtom_lt atomConfigurationsOk member))
      (fun _ member => member) }

/-- Decode the optional diagram channel.  Absence stays `none`. -/
def decodeDiagram? (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) :
    Option (OrganicDiagramSource (Fin input.molecule.atomCount)) :=
  match observed : input.diagram? with
  | none => none
  | some diagram =>
      some (decodeDiagram diagram input.molecule.atomCount
        (diagramPositionsFits_of_wf input wellFormed diagram observed)
        (diagramBondOk_of_wf input wellFormed diagram observed)
        (diagramAtomOk_of_wf input wellFormed diagram observed))

/-- Reduction lemma for the present case of the optional diagram channel. -/
theorem decodeDiagram?_some (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) (diagram : DiagramConfiguration)
    (observed : input.diagram? = some diagram) :
    decodeDiagram? input wellFormed =
      some (decodeDiagram diagram input.molecule.atomCount
        (diagramPositionsFits_of_wf input wellFormed diagram observed)
        (diagramBondOk_of_wf input wellFormed diagram observed)
        (diagramAtomOk_of_wf input wellFormed diagram observed)) := by
  rcases input with ⟨molecule, spatial?, diagram?⟩
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  cases diagram? with
  | none => simp at observed
  | some actual =>
      simp only [Option.some.injEq] at observed
      subst actual
      rfl

/-- The positions field of the decoded drawing source. -/
@[simp] theorem decodeDiagram_positions? (diagram : DiagramConfiguration) (atomCount : ℕ)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = atomCount)
    (bondsOk : diagram.bonds.all (fun bond =>
      decide (bond.source < atomCount) && decide (bond.target < atomCount) &&
        decide (bond.source ≠ bond.target)) = true)
    (atomConfigurationsOk : diagram.atomConfigurations.all
      (fun configuration => decide (configuration.atom < atomCount)) = true) :
    (decodeDiagram diagram atomCount positionsFit bondsOk atomConfigurationsOk).positions? =
      decodeDiagramPositions? diagram atomCount positionsFit := rfl

/-- The bonds field of the decoded drawing source. -/
@[simp] theorem decodeDiagram_bonds (diagram : DiagramConfiguration) (atomCount : ℕ)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = atomCount)
    (bondsOk : diagram.bonds.all (fun bond =>
      decide (bond.source < atomCount) && decide (bond.target < atomCount) &&
        decide (bond.source ≠ bond.target)) = true)
    (atomConfigurationsOk : diagram.atomConfigurations.all
      (fun configuration => decide (configuration.atom < atomCount)) = true) :
    (decodeDiagram diagram atomCount positionsFit bondsOk atomConfigurationsOk).bonds =
      diagram.bonds.pmap
        (fun bond member => decodeDiagramBond atomCount bond
          (diagramBond_source_lt bondsOk member)
          (diagramBond_target_lt bondsOk member))
        (fun _ member => member) := rfl

/-- The atom-parity field of the decoded drawing source. -/
@[simp] theorem decodeDiagram_atomConfigurations (diagram : DiagramConfiguration)
    (atomCount : ℕ)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = atomCount)
    (bondsOk : diagram.bonds.all (fun bond =>
      decide (bond.source < atomCount) && decide (bond.target < atomCount) &&
        decide (bond.source ≠ bond.target)) = true)
    (atomConfigurationsOk : diagram.atomConfigurations.all
      (fun configuration => decide (configuration.atom < atomCount)) = true) :
    (decodeDiagram diagram atomCount positionsFit bondsOk
        atomConfigurationsOk).atomConfigurations =
      diagram.atomConfigurations.pmap
        (fun configuration member => decodeDiagramAtom atomCount configuration
          (diagramAtom_lt atomConfigurationsOk member))
        (fun _ member => member) := rfl

/-- Helper extension theorem for `DiagramConfiguration`. -/
theorem diagramConfiguration_ext {first second : DiagramConfiguration}
    (positionsEqual : first.atomPositions? = second.atomPositions?)
    (bondsEqual : first.bonds = second.bonds)
    (configurationsEqual : first.atomConfigurations = second.atomConfigurations) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Encoding one reconstructed bond occurrence recovers the stored bond exactly. -/
theorem encodeBond_decodeDiagramBond (n : ℕ)
    (e : Fin n ≃ Fin (Fintype.card (Fin n)))
    (hval : ∀ index : Fin n, (e index).val = index.val)
    (bond : DiagramBond) (sourceBound : bond.source < n) (targetBound : bond.target < n) :
    OrganicDiagramSource.encodeBond e
        (decodeDiagramBond n bond sourceBound targetBound) = bond := by
  cases bond with
  | mk source target style scope =>
      have hs : (e ⟨source, sourceBound⟩).val = source := hval ⟨source, sourceBound⟩
      have ht : (e ⟨target, targetBound⟩).val = target := hval ⟨target, targetBound⟩
      simp [OrganicDiagramSource.encodeBond, decodeDiagramBond, hs, ht]

/-- Encoding one reconstructed atom-parity occurrence recovers the stored annotation exactly. -/
theorem encodeAtomConfiguration_decodeDiagramAtom (n : ℕ)
    (e : Fin n ≃ Fin (Fintype.card (Fin n)))
    (hval : ∀ index : Fin n, (e index).val = index.val)
    (configuration : DiagramAtomConfiguration) (bound : configuration.atom < n) :
    OrganicDiagramSource.encodeAtomConfiguration e
        (decodeDiagramAtom n configuration bound) = configuration := by
  cases configuration with
  | mk atom parity scope =>
      have ha : (e ⟨atom, bound⟩).val = atom := hval ⟨atom, bound⟩
      simp [OrganicDiagramSource.encodeAtomConfiguration, decodeDiagramAtom, ha]

/-- The ordered bond list round-trips exactly. -/
theorem map_encodeBond_decodeDiagramBonds (n : ℕ)
    (e : Fin n ≃ Fin (Fintype.card (Fin n)))
    (hval : ∀ index : Fin n, (e index).val = index.val)
    (bonds : List DiagramBond)
    (sourceLt : ∀ bond ∈ bonds, bond.source < n)
    (targetLt : ∀ bond ∈ bonds, bond.target < n) :
    (bonds.pmap
        (fun bond member =>
          decodeDiagramBond n bond (sourceLt bond member) (targetLt bond member))
        (fun _ member => member)).map (OrganicDiagramSource.encodeBond e) = bonds :=
  map_pmap_map_eq_self bonds
    (fun bond member =>
      decodeDiagramBond n bond (sourceLt bond member) (targetLt bond member))
    (OrganicDiagramSource.encodeBond e) (fun _ member => member)
    (fun bond member =>
      encodeBond_decodeDiagramBond n e hval bond (sourceLt bond member)
        (targetLt bond member))

/-- The ordered atom-parity list round-trips exactly. -/
theorem map_encodeAtomConfiguration_decodeDiagramAtoms (n : ℕ)
    (e : Fin n ≃ Fin (Fintype.card (Fin n)))
    (hval : ∀ index : Fin n, (e index).val = index.val)
    (configurations : List DiagramAtomConfiguration)
    (bounds : ∀ configuration ∈ configurations, configuration.atom < n) :
    (configurations.pmap
        (fun configuration member =>
          decodeDiagramAtom n configuration (bounds configuration member))
        (fun _ member => member)).map
        (OrganicDiagramSource.encodeAtomConfiguration e) = configurations :=
  map_pmap_map_eq_self configurations
    (fun configuration member =>
      decodeDiagramAtom n configuration (bounds configuration member))
    (OrganicDiagramSource.encodeAtomConfiguration e) (fun _ member => member)
    (fun configuration member =>
      encodeAtomConfiguration_decodeDiagramAtom n e hval configuration
        (bounds configuration member))

/-- The optional position list round-trips exactly when present. -/
theorem encodePositions?_decodeDiagramPositions (n : ℕ) (positions : List CartesianPoint2)
    (fits : positions.length = n) :
    OrganicDiagramSource.encodePositions? (identityEnumeration n)
        (some (decodeDiagramPositions positions n fits)) = some positions := by
  simp only [OrganicDiagramSource.encodePositions?]
  congr 1
  apply ofFn_eq_list_of_get (l := positions)
    (hlen := (Fintype.card_fin n).trans fits.symm)
  intro index
  exact list_get_congr_val (h := rfl)

/-- **Exact diagram reconstruction.**  Encoding the decoded drawing source recovers the entire
stored `DiagramConfiguration`: optional positions, ordered bonds with endpoints/style/scope, and
ordered atom-parity annotations with parity tokens and scopes. -/
theorem encodeDiagram_decodeDiagram (n : ℕ) (diagram : DiagramConfiguration)
    (positionsFit : ∀ positions, diagram.atomPositions? = some positions →
      positions.length = n)
    (bondsOk : diagram.bonds.all (fun bond =>
      decide (bond.source < n) && decide (bond.target < n) &&
        decide (bond.source ≠ bond.target)) = true)
    (atomConfigurationsOk : diagram.atomConfigurations.all
      (fun configuration => decide (configuration.atom < n)) = true) :
    OrganicDiagramSource.encodeDiagram (identityEnumeration n)
        (decodeDiagram diagram n positionsFit bondsOk atomConfigurationsOk) = diagram := by
  apply diagramConfiguration_ext
  · rw [OrganicDiagramSource.encodeDiagram_atomPositions?, decodeDiagram_positions?]
    cases observed : diagram.atomPositions? with
    | none =>
        rw [decodeDiagramPositions?_none diagram n positionsFit observed]
        rfl
    | some positions =>
        rw [decodeDiagramPositions?_some diagram n positionsFit positions observed]
        simp only [OrganicDiagramSource.encodePositions?_some]
        exact encodePositions?_decodeDiagramPositions n positions
          (positionsFit positions observed)
  · rw [OrganicDiagramSource.encodeDiagram_bonds, decodeDiagram_bonds]
    exact map_encodeBond_decodeDiagramBonds n (identityEnumeration n) (fun _ => rfl)
      diagram.bonds
      (fun bond member => diagramBond_source_lt bondsOk member)
      (fun bond member => diagramBond_target_lt bondsOk member)
  · rw [OrganicDiagramSource.encodeDiagram_atomConfigurations, decodeDiagram_atomConfigurations]
    exact map_encodeAtomConfiguration_decodeDiagramAtoms n (identityEnumeration n)
      (fun _ => rfl) diagram.atomConfigurations
      (fun configuration member => diagramAtom_lt atomConfigurationsOk member)

/-- Decoding the nullary diagram channel yields `none`. -/
@[simp] theorem decodeDiagram?_none (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed)
    (absent : input.diagram? = none) :
    decodeDiagram? input wellFormed = none := by
  rcases input with ⟨molecule, spatial?, diagram?⟩
  unfold AuthoritativeChemicalInput.DiagramIndicesWellFormed at wellFormed
  cases diagram? with
  | none => rfl
  | some diagram => simp at absent

/-- **Exact diagram round trip**, including absence. -/
theorem encodeDiagram?_decodeDiagram? (input : AuthoritativeChemicalInput)
    (wellFormed : input.DiagramIndicesWellFormed) :
    (decodeDiagram? input wellFormed).map
        (OrganicDiagramSource.encodeDiagram (identityEnumeration input.molecule.atomCount)) =
      input.diagram? := by
  cases observed : input.diagram? with
  | none =>
      rw [decodeDiagram?_none input wellFormed observed]
      rfl
  | some diagram =>
      rw [decodeDiagram?_some input wellFormed diagram observed]
      simp only [Option.map_some]
      exact congrArg some (encodeDiagram_decodeDiagram input.molecule.atomCount diagram
        (diagramPositionsFits_of_wf input wellFormed diagram observed)
        (diagramBondOk_of_wf input wellFormed diagram observed)
        (diagramAtomOk_of_wf input wellFormed diagram observed))

/-! ## The ingress map on certified inputs -/

/-- Helper extension theorem for `AuthoritativeChemicalInput`. -/
theorem authoritativeInput_ext {first second : AuthoritativeChemicalInput}
    (moleculeEqual : first.molecule = second.molecule)
    (spatialEqual : first.spatial? = second.spatial?)
    (diagramEqual : first.diagram? = second.diagram?) : first = second := by
  cases first
  cases second
  simp_all

namespace CertifiedAuthoritativeChemicalInput

/-- **Exact ingress.**  Every certified authoritative input yields an independent-label finite
source: the reconstructed graph over `Fin atomCount`, the optional total rational coordinate
function, and the optional independent drawing source.  No original input is stored or hidden. -/
def decode (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicFiniteSource (Fin certified.input.molecule.atomCount) :=
  { graph := reconstructGraph certified.input.molecule
      certified.structurallyWellFormed.1
    spatial? := decodeSpatial? certified.input certified.structurallyWellFormed.2.1
    diagram? := decodeDiagram? certified.input certified.structurallyWellFormed.2.2 }

@[simp] theorem decode_graph (certified : CertifiedAuthoritativeChemicalInput) :
    (decode certified).graph =
      reconstructGraph certified.input.molecule certified.structurallyWellFormed.1 := rfl

@[simp] theorem decode_spatial? (certified : CertifiedAuthoritativeChemicalInput) :
    (decode certified).spatial? =
      decodeSpatial? certified.input certified.structurallyWellFormed.2.1 := rfl

@[simp] theorem decode_diagram? (certified : CertifiedAuthoritativeChemicalInput) :
    (decode certified).diagram? =
      decodeDiagram? certified.input certified.structurallyWellFormed.2.2 := rfl

/-- Spatial absence is preserved by the ingress. -/
theorem decode_spatial?_eq_none (certified : CertifiedAuthoritativeChemicalInput)
    (absent : certified.input.spatial? = none) :
    (decode certified).spatial? = none := by
  simp [decode_spatial?, decodeSpatial?_none certified.input
    certified.structurallyWellFormed.2.1 absent]

/-- Diagram absence is preserved by the ingress. -/
theorem decode_diagram?_eq_none (certified : CertifiedAuthoritativeChemicalInput)
    (absent : certified.input.diagram? = none) :
    (decode certified).diagram? = none := by
  simp [decode_diagram?, decodeDiagram?_none certified.input
    certified.structurallyWellFormed.2.2 absent]

/-- **Exact round trip.**  Encoding the ingress source reproduces the entire original
`AuthoritativeChemicalInput`: the semantic molecule exactly, and both optional evidence channels
exactly, including their absence. -/
theorem encode_decode (certified : CertifiedAuthoritativeChemicalInput) :
    (decode certified).encode
        (identityEnumeration certified.input.molecule.atomCount) = certified.input := by
  apply authoritativeInput_ext
  · exact reconstructGraph_encode certified.input.molecule
      certified.structurallyWellFormed.1
  · exact encodeSpatial?_decodeSpatial? certified.input
      certified.structurallyWellFormed.2.1
  · exact encodeDiagram?_decodeDiagram? certified.input
      certified.structurallyWellFormed.2.2

/-- The molecule projection of the round trip: the reconstructed graph encodes to exactly the
stored `SemanticMolecule`, with all ordered occurrences and all broad atom fields. -/
theorem encode_decode_molecule (certified : CertifiedAuthoritativeChemicalInput) :
    (decode certified).graph.encode
        (identityEnumeration certified.input.molecule.atomCount) =
      certified.input.molecule :=
  reconstructGraph_encode certified.input.molecule certified.structurallyWellFormed.1

/-- The spatial projection of the round trip, with absence included. -/
theorem encode_decode_spatial? (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicFiniteSource.encodeSpatial?
        (identityEnumeration certified.input.molecule.atomCount)
        (decode certified).spatial? = certified.input.spatial? :=
  encodeSpatial?_decodeSpatial? certified.input certified.structurallyWellFormed.2.1

/-- The diagram projection of the round trip, with absence included. -/
theorem encode_decode_diagram? (certified : CertifiedAuthoritativeChemicalInput) :
    ((decode certified).diagram?).map
        (OrganicDiagramSource.encodeDiagram
          (identityEnumeration certified.input.molecule.atomCount)) =
      certified.input.diagram? :=
  encodeDiagram?_decodeDiagram? certified.input certified.structurallyWellFormed.2.2

end CertifiedAuthoritativeChemicalInput

end TetraStereo.OneCenter
