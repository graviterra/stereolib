import TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Image
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoMaterializedSiteSourceRecovery

open OrganicStereoElectronicSites
open OrganicStereoIndependentElectronicEncoding
open OrganicStereoInventoryImplicitHMaterialization

/-!
# Whole-source recovery from a materialized implicit-protium graph

The approved module `OrganicStereoInventoryImplicitHMaterialization` supplies the literal graph
expansion `expand` and the canonical projection `restore`, proves `restore (expand graph count) =
graph`, proves that the introduced slot family read from the expanded interaction list is the whole
supplied slot enumeration, and proves the concrete `CHBrClF` detector result.  Those results are
projections of one direction only: they recover the graph from the expanded graph, but the
*implicit-protium count* and the complete independent electronic site source are not carried by the
expanded graph alone.

This module closes that gap with an actual whole-input bundle.  The independently supplied input is

* `graph : FiniteAtomInteractionHypergraph V`;
* `siteSource : IndependentElectronicSiteSource graph`, i.e. a per-owner `SuppliedSiteCounts` and
  the single source tie `unpairedElectronPositions = (graph.atomData owner).unpairedElectrons`.

The materialized output is a single dependent record carrying

* `implicitCount : V → ℕ`, the explicit dimensional witness for the protium slots;
* `residual : V → ResidualSiteFields`, the five old-owner **non-protium** count fields, with
  `implicitProtia` absent from the residual type;
* `expanded : FiniteAtomInteractionHypergraph (ExpandedLabel implicitCount)`, the graph on
  `V ⊕ Σ owner, Fin (implicitCount owner)`;
* proof-only coherence fields: every introduced label carries the protium atom record, the
  interaction list is exactly the lifted old list followed by the selected hydrogen bonds, and the
  residual unpaired count agrees with the restored graph's atom data.

No original graph, no original `IndependentElectronicSiteSource`, and no original whole-input term
is stored.  The output type is `MaterializedOutput V`; there is no field of type
`FiniteAtomInteractionHypergraph V` and no field of type
`IndependentElectronicSiteSource graph`.

The decoder is literal:

* the graph is `restore implicitCount expanded`, the actual projection from the approved module;
* each owner's `implicitProtia` is the explicit count witness `implicitCount owner`; it is also
  proved to equal the number of introduced slots at that owner read back from the expanded
  interaction list (`introducedOwnerSlots_length`);
* the other five fields come from `residual`;
* the `unpaired_tied` proof of the reconstructed source is the output's proof-only coherence.

Two inverse laws are proved for the whole dependent records:

* `decode (materialize input) = input` for every independently supplied input;
* `materialize (decode output) = output` for every output of `MaterializedOutput`, with no
  extra hypothesis: the correlated set of outputs is the whole output type, and the decoder's
  reconstruction conditions are exactly the coherence fields carried by that type.

Scope boundaries, stated exactly:

* the richer repository inventories (`AuthoritativeChemicalInput`, `ElectronicSiteSource`,
  endpoint inventories, geometry, P-94 ledgers, and diagram/physical data) are **not** inputs here
  and are not derived.  This theorem is about `FiniteAtomInteractionHypergraph` together with
  `IndependentElectronicSiteSource` only;
* the residual fields are exactly `lonePairs`, `vacancies`, `unpairedElectronPositions`,
  `cipNotionalPhantoms`, and `cipVirtualDuplicates`.  They are preserved as counts and are never
  turned into hydrogen atoms: only `implicitProtia` creates expanded atoms;
* `introducedSlotOfEdge?` is a decoder for the selected hydrogen-bond shape.  It is not a general
  graph-validity checker.  The readback theorem below is therefore stated only for outputs whose
  interaction list satisfies the output's coherence field, where the introduced block is exactly
  the selected hydrogen bonds;
* the concrete examples are formal sources.  They make no physical-realizability claim, and the
  repeated `CHBrClF` fixture reuses the approved module's existing finite source.
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-! ## The independently supplied whole input -/

/-- The independently supplied source package: a finite atom interaction graph together with an
independent electronic site source over exactly that graph.  The site source is dependent on the
graph because its only tie refers to the graph's atom data. -/
structure WholeSource (V : Type*) [DecidableEq V] [Fintype V] where
  /-- The independently supplied finite atom interaction graph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- The independent electronic site inventory over that graph. -/
  siteSource : IndependentElectronicSiteSource graph

/-! ## Residual old-owner non-protium counts -/

/-- The old-owner counts that remain after removing the implicit-protium field.  The type itself has
no `implicitProtia` component, so lone pairs, vacancies, unpaired positions and CIP-reference
bookkeeping cannot be confused with materialized hydrogen atoms. -/
structure ResidualSiteFields where
  lonePairs : ℕ
  vacancies : ℕ
  unpairedElectronPositions : ℕ
  cipNotionalPhantoms : ℕ
  cipVirtualDuplicates : ℕ
  deriving DecidableEq, Repr

namespace ResidualSiteFields

/-- The residual projection of a supplied count record.  The protium field is deliberately not
retained. -/
def ofSupplied (counts : SuppliedSiteCounts) : ResidualSiteFields where
  lonePairs := counts.lonePairs
  vacancies := counts.vacancies
  unpairedElectronPositions := counts.unpairedElectronPositions
  cipNotionalPhantoms := counts.cipNotionalPhantoms
  cipVirtualDuplicates := counts.cipVirtualDuplicates

/-- Reattach an independently witnessed protium count to a residual record. -/
def toSupplied (residual : ResidualSiteFields) (implicitProtia : ℕ) : SuppliedSiteCounts where
  implicitProtia := implicitProtia
  lonePairs := residual.lonePairs
  vacancies := residual.vacancies
  unpairedElectronPositions := residual.unpairedElectronPositions
  cipNotionalPhantoms := residual.cipNotionalPhantoms
  cipVirtualDuplicates := residual.cipVirtualDuplicates

@[simp] theorem ofSupplied_lonePairs (counts : SuppliedSiteCounts) :
    (ofSupplied counts).lonePairs = counts.lonePairs :=
  rfl

@[simp] theorem ofSupplied_vacancies (counts : SuppliedSiteCounts) :
    (ofSupplied counts).vacancies = counts.vacancies :=
  rfl

@[simp] theorem ofSupplied_unpairedElectronPositions (counts : SuppliedSiteCounts) :
    (ofSupplied counts).unpairedElectronPositions = counts.unpairedElectronPositions :=
  rfl

@[simp] theorem ofSupplied_cipNotionalPhantoms (counts : SuppliedSiteCounts) :
    (ofSupplied counts).cipNotionalPhantoms = counts.cipNotionalPhantoms :=
  rfl

@[simp] theorem ofSupplied_cipVirtualDuplicates (counts : SuppliedSiteCounts) :
    (ofSupplied counts).cipVirtualDuplicates = counts.cipVirtualDuplicates :=
  rfl

@[simp] theorem toSupplied_implicitProtia (residual : ResidualSiteFields) (implicitProtia : ℕ) :
    (toSupplied residual implicitProtia).implicitProtia = implicitProtia :=
  rfl

@[simp] theorem toSupplied_lonePairs (residual : ResidualSiteFields) (implicitProtia : ℕ) :
    (toSupplied residual implicitProtia).lonePairs = residual.lonePairs :=
  rfl

@[simp] theorem toSupplied_vacancies (residual : ResidualSiteFields) (implicitProtia : ℕ) :
    (toSupplied residual implicitProtia).vacancies = residual.vacancies :=
  rfl

@[simp] theorem toSupplied_unpairedElectronPositions (residual : ResidualSiteFields)
    (implicitProtia : ℕ) :
    (toSupplied residual implicitProtia).unpairedElectronPositions =
      residual.unpairedElectronPositions :=
  rfl

@[simp] theorem toSupplied_cipNotionalPhantoms (residual : ResidualSiteFields)
    (implicitProtia : ℕ) :
    (toSupplied residual implicitProtia).cipNotionalPhantoms = residual.cipNotionalPhantoms :=
  rfl

@[simp] theorem toSupplied_cipVirtualDuplicates (residual : ResidualSiteFields)
    (implicitProtia : ℕ) :
    (toSupplied residual implicitProtia).cipVirtualDuplicates = residual.cipVirtualDuplicates :=
  rfl

/-- Projecting and then reattaching the protium count recovers the supplied record exactly. -/
@[simp] theorem toSupplied_ofSupplied (counts : SuppliedSiteCounts) :
    toSupplied (ofSupplied counts) counts.implicitProtia = counts := by
  cases counts
  rfl

/-- Reattaching any protium count and then projecting removes exactly that field. -/
@[simp] theorem ofSupplied_toSupplied (residual : ResidualSiteFields) (implicitProtia : ℕ) :
    ofSupplied (toSupplied residual implicitProtia) = residual := by
  cases residual
  rfl

/-- The approved module's blanked payload is exactly the residual record with a zero protium
count. -/
theorem nonProtiumPayload_eq_toSupplied_zero (counts : SuppliedSiteCounts) :
    nonProtiumPayload counts = toSupplied (ofSupplied counts) 0 := by
  cases counts
  rfl

end ResidualSiteFields

/-! ## The actual materialized output -/

/-- The materialized output.  It carries the expanded graph on `ExpandedLabel implicitCount`, the
explicit count witness, the residual non-protium counts, and proof-only coherence with the graph
that `restore` reads back.  It does not carry the original graph or the original site source. -/
structure MaterializedOutput (V : Type*) [DecidableEq V] [Fintype V] where
  /-- The explicit dimensional witness: the supplied implicit-protium count at each old owner. -/
  implicitCount : V → ℕ
  /-- The preserved old-owner non-protium counts. -/
  residual : V → ResidualSiteFields
  /-- The expanded graph over old atoms and tagged hydrogen slots. -/
  expanded : FiniteAtomInteractionHypergraph (ExpandedLabel implicitCount)
  /-- Every tagged hydrogen label carries exactly the materialized protium atom record. -/
  hydrogen_atomData : ∀ h : HydrogenSlot implicitCount,
    expanded.atomData (Sum.inr h) = materializedHydrogenAtom
  /-- The interaction list consists exactly of the lifted old interactions followed by the selected
  hydrogen bonds.  This is the exact correlated-set condition making the output recoverable. -/
  interaction_coherent : expanded.interactions =
    (expanded.interactions.filterMap (decodeOriginalInteraction implicitCount)).map
        (liftInteraction implicitCount) ++ hydrogenBonds implicitCount
  /-- The residual unpaired count agrees with the restored graph's semantic atom data. -/
  unpaired_coherent : ∀ owner : V,
    (residual owner).unpairedElectronPositions =
      ((restore implicitCount expanded).atomData owner).unpairedElectrons

/-! ## Materialization of an independently supplied whole source -/

/-- Materialize an independently supplied graph and site source.  The count is read only from the
source's explicit `implicitProtia` field; the residual fields are the other five supplied counts;
the expanded graph is the approved literal expansion. -/
noncomputable def materialize (input : WholeSource V) : MaterializedOutput V where
  implicitCount := siteImplicitCount input.siteSource
  residual owner := ResidualSiteFields.ofSupplied (input.siteSource.siteCounts.counts owner)
  expanded := expand input.graph (siteImplicitCount input.siteSource)
  hydrogen_atomData h :=
    expand_atomData_hydrogen input.graph (siteImplicitCount input.siteSource) h
  interaction_coherent := by
    change (input.graph.interactions.map
          (liftInteraction (siteImplicitCount input.siteSource)) ++
        hydrogenBonds (siteImplicitCount input.siteSource)) =
      ((input.graph.interactions.map
          (liftInteraction (siteImplicitCount input.siteSource)) ++
        hydrogenBonds (siteImplicitCount input.siteSource)).filterMap
          (decodeOriginalInteraction (siteImplicitCount input.siteSource))).map
        (liftInteraction (siteImplicitCount input.siteSource)) ++
      hydrogenBonds (siteImplicitCount input.siteSource)
    rw [List.filterMap_append,
      filterMap_liftInteractions_eq,
      filterMap_hydrogenBonds_eq_nil,
      List.append_nil]
  unpaired_coherent owner := by
    change (input.siteSource.siteCounts.counts owner).unpairedElectronPositions =
      ((restore (siteImplicitCount input.siteSource)
        (expand input.graph (siteImplicitCount input.siteSource))).atomData owner).unpairedElectrons
    rw [restore_expand]
    exact input.siteSource.unpaired_tied owner

/-! ## Decoding a materialized output -/

/-- Decode a materialized output back to a whole source.  The graph is the approved actual
projection `restore`; the protium count is the explicit witness; the other counts are the residual
fields; the tie is the output's coherence proof. -/
noncomputable def decode (output : MaterializedOutput V) : WholeSource V where
  graph := restore output.implicitCount output.expanded
  siteSource :=
    { siteCounts :=
        { counts := fun owner =>
            (output.residual owner).toSupplied (output.implicitCount owner) }
      unpaired_tied owner := output.unpaired_coherent owner }

/-! ## Projection laws -/

@[simp] theorem materialize_implicitCount (input : WholeSource V) :
    (materialize input).implicitCount = siteImplicitCount input.siteSource :=
  rfl

@[simp] theorem materialize_expanded (input : WholeSource V) :
    (materialize input).expanded =
      expand input.graph (siteImplicitCount input.siteSource) :=
  rfl

@[simp] theorem materialize_residual (input : WholeSource V) (owner : V) :
    (materialize input).residual owner =
      ResidualSiteFields.ofSupplied (input.siteSource.siteCounts.counts owner) :=
  rfl

@[simp] theorem decode_graph (output : MaterializedOutput V) :
    (decode output).graph = restore output.implicitCount output.expanded :=
  rfl

@[simp] theorem decode_counts (output : MaterializedOutput V) (owner : V) :
    (decode output).siteSource.siteCounts.counts owner =
      (output.residual owner).toSupplied (output.implicitCount owner) :=
  rfl

/-- The decoded `implicitProtia` is the explicit dimensional witness, exactly. -/
@[simp] theorem decode_implicitProtia (output : MaterializedOutput V) (owner : V) :
    ((decode output).siteSource.siteCounts.counts owner).implicitProtia =
      output.implicitCount owner :=
  rfl

/-- The site-implicit count of the decoded source is exactly the output's explicit count. -/
@[simp] theorem decode_siteImplicitCount (output : MaterializedOutput V) :
    siteImplicitCount (decode output).siteSource = output.implicitCount := by
  funext owner
  exact decode_implicitProtia output owner

/-- Every non-protium old-owner field is recovered from the residual output, not from the expanded
graph. -/
@[simp] theorem decode_lonePairs (output : MaterializedOutput V) (owner : V) :
    ((decode output).siteSource.siteCounts.counts owner).lonePairs =
      (output.residual owner).lonePairs :=
  rfl

@[simp] theorem decode_vacancies (output : MaterializedOutput V) (owner : V) :
    ((decode output).siteSource.siteCounts.counts owner).vacancies =
      (output.residual owner).vacancies :=
  rfl

@[simp] theorem decode_unpairedElectronPositions (output : MaterializedOutput V) (owner : V) :
    ((decode output).siteSource.siteCounts.counts owner).unpairedElectronPositions =
      (output.residual owner).unpairedElectronPositions :=
  rfl

@[simp] theorem decode_cipNotionalPhantoms (output : MaterializedOutput V) (owner : V) :
    ((decode output).siteSource.siteCounts.counts owner).cipNotionalPhantoms =
      (output.residual owner).cipNotionalPhantoms :=
  rfl

@[simp] theorem decode_cipVirtualDuplicates (output : MaterializedOutput V) (owner : V) :
    ((decode output).siteSource.siteCounts.counts owner).cipVirtualDuplicates =
      (output.residual owner).cipVirtualDuplicates :=
  rfl

/-! ## Readback of the explicit count from introduced slots

The count witness is not a validity checker for an arbitrary expanded graph: `introducedSlotOfEdge?`
recognizes only the selected hydrogen-bond shapes.  For an actual output the coherence field says
that the whole interaction list is the lifted old block followed by the selected hydrogen bonds, so
the readback is exact. -/

/-- For an actual output, the introduced slot family is exactly the canonical slot enumeration. -/
theorem introducedSlots_eq_hydrogenOccurrences (output : MaterializedOutput V) :
    introducedSlots output.implicitCount output.expanded =
      hydrogenOccurrences output.implicitCount := by
  change output.expanded.interactions.filterMap (introducedSlotOfEdge? output.implicitCount) =
    hydrogenOccurrences output.implicitCount
  rw [output.interaction_coherent, List.filterMap_append,
    introducedSlots_liftInteractions,
    introducedSlots_hydrogenBonds,
    List.nil_append]

/-- The total number of introduced slots is the total explicit count. -/
theorem introducedSlots_length (output : MaterializedOutput V) :
    (introducedSlots output.implicitCount output.expanded).length =
      (Finset.univ : Finset V).sum output.implicitCount := by
  rw [introducedSlots_eq_hydrogenOccurrences, hydrogenOccurrences_length, hydrogenSlot_card]

/-- The fiber of slots over one owner. -/
def hydrogenSlotOwnerFiberEquiv (count : V → ℕ) (owner : V) :
    {h : HydrogenSlot count // h.1 = owner} ≃ Fin (count owner) where
  toFun h := by
    obtain ⟨⟨hOwner, slot⟩, ownerEq⟩ := h
    exact ownerEq ▸ slot
  invFun slot := ⟨⟨owner, slot⟩, rfl⟩
  left_inv h := by
    obtain ⟨⟨hOwner, slot⟩, ownerEq⟩ := h
    cases ownerEq
    rfl
  right_inv slot := rfl

/-- The number of slots at one owner is exactly the explicit count at that owner. -/
theorem hydrogenSlotOwnerFiber_card (count : V → ℕ) (owner : V) :
    Fintype.card {h : HydrogenSlot count // h.1 = owner} = count owner := by
  rw [Fintype.card_congr (hydrogenSlotOwnerFiberEquiv count owner), Fintype.card_fin]

/-- Per-owner readback: the number of introduced slots owned by `owner` in an actual output is
exactly the explicit count witness at `owner`. -/
theorem introducedOwnerSlots_length (output : MaterializedOutput V) (owner : V) :
    ((introducedSlots output.implicitCount output.expanded).filter
        (fun h => h.1 = owner)).length =
      output.implicitCount owner := by
  rw [introducedSlots_eq_hydrogenOccurrences]
  unfold hydrogenOccurrences
  have nodup :
      (((Finset.univ : Finset (HydrogenSlot output.implicitCount)).toList).filter
        (fun h => h.1 = owner)).Nodup :=
    (Finset.nodup_toList _).filter _
  rw [← List.toFinset_card_of_nodup nodup]
  have finsetEq :
      ((((Finset.univ : Finset (HydrogenSlot output.implicitCount)).toList).filter
          (fun h => h.1 = owner)).toFinset) =
        (Finset.univ.filter fun h : HydrogenSlot output.implicitCount => h.1 = owner) := by
    ext h
    simp
  rw [finsetEq, ← Fintype.card_subtype]
  exact hydrogenSlotOwnerFiber_card output.implicitCount owner

/-! ## Whole dependent record inverse laws -/

/-- Extensionality of whole sources.  The site sources are compared heterogeneously because their
types are indexed by the graph. -/
theorem WholeSource.extEq {first second : WholeSource V}
    (graph : first.graph = second.graph)
    (siteSource : HEq first.siteSource second.siteSource) :
    first = second := by
  obtain ⟨firstGraph, firstSource⟩ := first
  obtain ⟨secondGraph, secondSource⟩ := second
  cases graph
  have sourceEq : firstSource = secondSource := eq_of_heq siteSource
  rw [sourceEq]

/-- A transport lemma for a site source along an equality of its graph index.  The site counts are
graph-independent data, and the only graph-dependent field is a proposition, so after aligning the
indices and the counts the records are equal by proof irrelevance. -/
theorem eqRec_siteSource_heq {graph graph' : FiniteAtomInteractionHypergraph V}
    (h : graph = graph')
    (siteSource : IndependentElectronicSiteSource graph) :
    HEq (h ▸ siteSource) siteSource := by
  cases h
  rfl

/-- Two independent electronic sources at equal graphs with equal site counts are heterogeneously
equal.  This is the form used for the whole-input recovery: the decoded source and the supplied
source live at propositionally equal graph indices, and their count data is identical. -/
theorem heq_of_siteCounts_eq {graph' graph : FiniteAtomInteractionHypergraph V}
    (h : graph' = graph)
    (source' : IndependentElectronicSiteSource graph')
    (source : IndependentElectronicSiteSource graph)
    (counts : source'.siteCounts = source.siteCounts) :
    HEq source' source := by
  obtain ⟨counts', tied'⟩ := source'
  obtain ⟨counts, tied⟩ := source
  dsimp only at counts
  cases counts
  cases h
  rfl

/-- Extensionality of independent site counts. -/
theorem IndependentSiteCounts.ext {first second : IndependentSiteCounts V}
    (counts : first.counts = second.counts) : first = second := by
  obtain ⟨firstCounts⟩ := first
  obtain ⟨secondCounts⟩ := second
  dsimp only at counts
  cases counts
  rfl

/-- The decoded site counts are exactly the supplied site counts. -/
theorem decode_materialize_siteCounts (graph : FiniteAtomInteractionHypergraph V)
    (siteSource : IndependentElectronicSiteSource graph) :
    (decode (materialize (⟨graph, siteSource⟩ : WholeSource V))).siteSource.siteCounts =
      siteSource.siteCounts := by
  apply IndependentSiteCounts.ext
  funext owner
  change (ResidualSiteFields.ofSupplied (siteSource.siteCounts.counts owner)).toSupplied
      (siteImplicitCount siteSource owner) = siteSource.siteCounts.counts owner
  rw [show siteImplicitCount siteSource owner =
      (siteSource.siteCounts.counts owner).implicitProtia from rfl]
  exact ResidualSiteFields.toSupplied_ofSupplied (siteSource.siteCounts.counts owner)

/-- Materialization followed by decoding recovers the whole independently supplied source,
including the graph, every count field, and the unpaired tie proof. -/
theorem decode_materialize (input : WholeSource V) :
    decode (materialize input) = input := by
  obtain ⟨graph, siteSource⟩ := input
  apply WholeSource.extEq
  · change restore (siteImplicitCount siteSource)
        (expand graph (siteImplicitCount siteSource)) = graph
    exact restore_expand graph (siteImplicitCount siteSource)
  · exact heq_of_siteCounts_eq
      (restore_expand graph (siteImplicitCount siteSource))
      (decode (materialize (⟨graph, siteSource⟩ : WholeSource V))).siteSource
      siteSource
      (decode_materialize_siteCounts graph siteSource)

/-- Extensionality of materialized outputs with the count and residual data fixed.  The expanded
graph is compared by equality; the protium atom-data and unpaired coherence fields are functions
into propositions, so after transporting along the graph equality they are equal pointwise by
proof irrelevance. -/
theorem MaterializedOutput.extEq {count : V → ℕ} {residual : V → ResidualSiteFields}
    {expanded₁ expanded₂ : FiniteAtomInteractionHypergraph (ExpandedLabel count)}
    (expanded : expanded₁ = expanded₂)
    (atomData₁ : ∀ h : HydrogenSlot count,
      expanded₁.atomData (Sum.inr h) = materializedHydrogenAtom)
    (atomData₂ : ∀ h : HydrogenSlot count,
      expanded₂.atomData (Sum.inr h) = materializedHydrogenAtom)
    (interactions₁ : expanded₁.interactions =
      (expanded₁.interactions.filterMap (decodeOriginalInteraction count)).map
        (liftInteraction count) ++ hydrogenBonds count)
    (interactions₂ : expanded₂.interactions =
      (expanded₂.interactions.filterMap (decodeOriginalInteraction count)).map
        (liftInteraction count) ++ hydrogenBonds count)
    (unpaired₁ : ∀ owner : V,
      (residual owner).unpairedElectronPositions =
        ((restore count expanded₁).atomData owner).unpairedElectrons)
    (unpaired₂ : ∀ owner : V,
      (residual owner).unpairedElectronPositions =
        ((restore count expanded₂).atomData owner).unpairedElectrons) :
    (⟨count, residual, expanded₁, atomData₁, interactions₁, unpaired₁⟩ :
        MaterializedOutput V) =
      ⟨count, residual, expanded₂, atomData₂, interactions₂, unpaired₂⟩ := by
  cases expanded
  have atomDataEq : atomData₁ = atomData₂ := funext fun h => Subsingleton.elim _ _
  have interactionsEq : interactions₁ = interactions₂ := Subsingleton.elim _ _
  have unpairedEq : unpaired₁ = unpaired₂ := funext fun owner => Subsingleton.elim _ _
  cases atomDataEq
  cases interactionsEq
  cases unpairedEq
  rfl

/-- Decoding followed by materialization recovers the whole materialized output.  The correlated
set is the whole output type because `MaterializedOutput` itself carries exactly the coherence
conditions used by the reconstruction. -/
theorem materialize_decode (output : MaterializedOutput V) :
    materialize (decode output) = output := by
  rcases output with ⟨count, residual, expanded, hydrogenAtomData, interactionCoherent,
    unpairedCoherent⟩
  have expandedEq :
      (materialize (decode
        (⟨count, residual, expanded, hydrogenAtomData, interactionCoherent,
          unpairedCoherent⟩ : MaterializedOutput V))).expanded = expanded := by
    apply graph_ext
    · funext w
      cases w with
      | inl v => rfl
      | inr h => exact (hydrogenAtomData h).symm
    · change (restore count expanded).interactions.map (liftInteraction count) ++
          hydrogenBonds count = expanded.interactions
      rw [restore_interactions]
      exact interactionCoherent.symm
  exact MaterializedOutput.extEq expandedEq _ _ _ _ _ _

/-! ## Injectivity, surjectivity and the correlated set -/

theorem materialize_injective : Function.Injective (materialize (V := V)) := by
  intro first second equal
  rw [← decode_materialize first, ← decode_materialize second, equal]

theorem decode_injective : Function.Injective (decode (V := V)) := by
  intro first second equal
  rw [← materialize_decode first, ← materialize_decode second, equal]

theorem materialize_surjective : Function.Surjective (materialize (V := V)) :=
  fun output => ⟨decode output, materialize_decode output⟩

theorem decode_surjective : Function.Surjective (decode (V := V)) :=
  fun input => ⟨materialize input, decode_materialize input⟩

/-- The whole input/output pair is an equivalence: the materialized output type is a faithful
representation of the independently supplied source type. -/
noncomputable def wholeSourceEquiv : WholeSource V ≃ MaterializedOutput V where
  toFun := materialize
  invFun := decode
  left_inv := decode_materialize
  right_inv := materialize_decode

/-- The correlated set of outputs decoded by a fixed input. -/
def correlatedOutputs (input : WholeSource V) : Set (MaterializedOutput V) :=
  {output | decode output = input}

/-- The actual materialization lies in the correlated set. -/
theorem materialize_mem_correlatedOutputs (input : WholeSource V) :
    materialize input ∈ correlatedOutputs input :=
  decode_materialize input

/-- The correlated set of an input is exactly the singleton of its materialization. -/
theorem correlatedOutputs_eq_singleton (input : WholeSource V) :
    correlatedOutputs input = {materialize input} := by
  ext output
  constructor
  · intro correlated
    rw [Set.mem_singleton_iff]
    calc
      output = materialize (decode output) := (materialize_decode output).symm
      _ = materialize input := congrArg materialize correlated
  · intro singleton
    rw [Set.mem_singleton_iff] at singleton
    subst singleton
    exact decode_materialize input

/-- Inverse image of the correlated set under materialization is exactly the original input. -/
theorem materialize_preimage_correlatedOutputs (input : WholeSource V) :
    materialize ⁻¹' correlatedOutputs input = {input} := by
  ext candidate
  constructor
  · intro correlated
    rw [Set.mem_singleton_iff]
    change decode (materialize candidate) = input at correlated
    rw [decode_materialize] at correlated
    exact correlated
  · intro singleton
    rw [Set.mem_singleton_iff] at singleton
    rw [singleton]
    exact materialize_mem_correlatedOutputs input

/-- Decoding the correlated set recovers exactly the input. -/
theorem decode_image_correlatedOutputs (input : WholeSource V) :
    decode '' correlatedOutputs input = {input} := by
  ext candidate
  constructor
  · rintro ⟨output, correlated, rfl⟩
    rw [Set.mem_singleton_iff]
    exact correlated
  · intro singleton
    rw [Set.mem_singleton_iff] at singleton
    rw [singleton]
    exact ⟨materialize input, decode_materialize input, decode_materialize input⟩

/-- Set-level left inverse: decoding after materializing any set of inputs gives that set back. -/
theorem decode_image_materialize_image (inputs : Set (WholeSource V)) :
    decode '' (materialize '' inputs) = inputs := by
  rw [Set.image_image]
  change (decode ∘ materialize (V := V)) '' inputs = inputs
  have composition : (decode ∘ materialize (V := V)) = id := funext decode_materialize
  rw [composition, Set.image_id]

/-- Set-level right inverse: materializing after decoding any set of outputs gives that set back. -/
theorem materialize_image_decode_image (outputs : Set (MaterializedOutput V)) :
    materialize '' (decode '' outputs) = outputs := by
  rw [Set.image_image]
  change (materialize ∘ decode (V := V)) '' outputs = outputs
  have composition : (materialize ∘ decode (V := V)) = id := funext materialize_decode
  rw [composition, Set.image_id]

theorem decode_image_univ :
    decode '' (Set.univ : Set (MaterializedOutput V)) = Set.univ :=
  Set.image_univ_of_surjective decode_surjective

theorem materialize_image_univ :
    materialize '' (Set.univ : Set (WholeSource V)) = Set.univ :=
  Set.image_univ_of_surjective materialize_surjective

/-! ## Non-protium fields are counts, never atoms -/

/-- The expanded atom type adds only the implicit-protium slots: its cardinality is the old atom
count plus the total protium count.  No lone-pair, vacancy, unpaired or CIP field contributes an
atom. -/
theorem expandedLabel_card (count : V → ℕ) :
    Fintype.card (ExpandedLabel count) =
      Fintype.card V + (Finset.univ : Finset V).sum count := by
  rw [Fintype.card_sum, hydrogenSlot_card]

/-- The number of expanded atoms materialized from an input is the old atom count plus the total
supplied implicit-protium count. -/
theorem materialize_expanded_card (input : WholeSource V) :
    Fintype.card (ExpandedLabel (materialize input).implicitCount) =
      Fintype.card V +
        (Finset.univ : Finset V).sum fun owner =>
          (input.siteSource.siteCounts.counts owner).implicitProtia := by
  rw [materialize_implicitCount, expandedLabel_card]
  rfl

/-- Materialization preserves every non-protium field of every old owner exactly. -/
theorem materialize_residual_fields (input : WholeSource V) (owner : V) :
    (materialize input).residual owner =
      { lonePairs := (input.siteSource.siteCounts.counts owner).lonePairs
        vacancies := (input.siteSource.siteCounts.counts owner).vacancies
        unpairedElectronPositions :=
          (input.siteSource.siteCounts.counts owner).unpairedElectronPositions
        cipNotionalPhantoms :=
          (input.siteSource.siteCounts.counts owner).cipNotionalPhantoms
        cipVirtualDuplicates :=
          (input.siteSource.siteCounts.counts owner).cipVirtualDuplicates } :=
  rfl

/-- Decoding after materialization preserves every non-protium field of every old owner exactly. -/
theorem decode_materialize_counts (input : WholeSource V) :
    (decode (materialize input)).siteSource.siteCounts = input.siteSource.siteCounts := by
  rw [decode_materialize]

/-! ## The concrete `CHBrClF` fixture from the approved module -/

/-- The existing heavy-atom `CHBrClF` input package: the approved fixture graph and its supplied
site source (one implicit protium on carbon, three lone pairs on each halogen). -/
def chbrclfInput : WholeSource (Fin 4) :=
  ⟨fixtureGraph, fixtureSiteSource⟩

/-- Its actual materialization. -/
noncomputable def chbrclfOutput : MaterializedOutput (Fin 4) :=
  materialize chbrclfInput

@[simp] theorem chbrclfOutput_implicitCount :
    chbrclfOutput.implicitCount = fixtureImplicitCount :=
  rfl

@[simp] theorem chbrclfOutput_expanded :
    chbrclfOutput.expanded = fixtureExpandedGraph :=
  rfl

/-- Whole-source recovery for the concrete fixture. -/
theorem chbrclf_decode_materialize :
    decode chbrclfOutput = chbrclfInput :=
  decode_materialize chbrclfInput

/-- The materialized graph is the approved five-atom expanded graph. -/
theorem chbrclf_five_atoms :
    Fintype.card (ExpandedLabel chbrclfOutput.implicitCount) = 5 := by
  rw [chbrclfOutput_implicitCount]
  exact fixtureExpanded_five_atoms

/-- Exactly one hydrogen slot was introduced, and its introduced-slot readback is the approved
fixture hydrogen. -/
theorem chbrclf_introducedSlots :
    introducedSlots chbrclfOutput.implicitCount chbrclfOutput.expanded =
      [fixtureHydrogen] := by
  rw [introducedSlots_eq_hydrogenOccurrences]
  change hydrogenOccurrences fixtureImplicitCount = [fixtureHydrogen]
  exact fixture_hydrogenOccurrences

/-- The explicit count witness at carbon is exactly the supplied one. -/
theorem chbrclf_implicitCount_zero : chbrclfOutput.implicitCount 0 = 1 := by
  rw [chbrclfOutput_implicitCount]
  exact fixtureImplicitCount_zero

/-- The residual non-protium fields still record the three lone pairs on bromine: they were not
turned into hydrogen atoms. -/
theorem chbrclf_bromine_lonePairs :
    (chbrclfOutput.residual 1).lonePairs = 3 :=
  rfl

/-- The residual non-protium fields still record the three lone pairs on chlorine. -/
theorem chbrclf_chlorine_lonePairs :
    (chbrclfOutput.residual 2).lonePairs = 3 :=
  rfl

/-- The residual non-protium fields still record the three lone pairs on fluorine. -/
theorem chbrclf_fluorine_lonePairs :
    (chbrclfOutput.residual 3).lonePairs = 3 :=
  rfl

/-- Decoding the fixture output recovers the exact supplied halogen counts, including their lone
pairs. -/
theorem chbrclf_decoded_halogen_counts :
    (decode chbrclfOutput).siteSource.siteCounts.counts 1 = fixtureHalogenCounts := by
  rw [chbrclf_decode_materialize]
  rfl

/-- Decoding the fixture output recovers the exact supplied carbon counts. -/
theorem chbrclf_decoded_carbon_counts :
    (decode chbrclfOutput).siteSource.siteCounts.counts 0 = fixtureCarbonCounts := by
  rw [chbrclf_decode_materialize]
  rfl

/-- The approved `CHBrClF` detector result is still available for the materialized graph: the
expanded carbon has four distinct direct CIP neighbour labels and the detected one-center molecule
is `StereogenicByCIP`. -/
theorem chbrclf_detected_stereogenic :
    OneCenterMolecule.StereogenicByCIP fixtureOneCenterMolecule :=
  fixtureOneCenter_stereogenicByCIP

/-! ## A nonzero non-protium formal inventory

This formal one-atom source has no implicit protium at all, but carries two lone pairs, one
vacancy, and one slot of each CIP-reference kind.  It demonstrates that those fields survive the
whole round trip and create no hydrogen atom.  No physical-realizability claim is made. -/

/-- A formal one-atom graph with a carbon atom and no interactions. -/
def nonProtiumGraph : FiniteAtomInteractionHypergraph (Fin 1) where
  atomData _ := fixtureCarbon
  interactions := []
  arity_ge_two := by simp
  participants_nodup := by simp

/-- The nonzero non-protium supplied inventory. -/
def nonProtiumCounts : SuppliedSiteCounts where
  implicitProtia := 0
  lonePairs := 2
  vacancies := 1
  unpairedElectronPositions := 0
  cipNotionalPhantoms := 1
  cipVirtualDuplicates := 1

/-- The source tie is satisfied: the graph's carbon atom has zero unpaired electrons and the
supplied unpaired position count is zero. -/
def nonProtiumSource : IndependentElectronicSiteSource nonProtiumGraph where
  siteCounts := { counts := fun _ => nonProtiumCounts }
  unpaired_tied := by
    intro owner
    rfl

/-- The formal non-protium input package. -/
def nonProtiumInput : WholeSource (Fin 1) :=
  ⟨nonProtiumGraph, nonProtiumSource⟩

/-- Its actual materialization. -/
noncomputable def nonProtiumOutput : MaterializedOutput (Fin 1) :=
  materialize nonProtiumInput

/-- No protium slot is supplied. -/
theorem nonProtium_implicitCount_zero : nonProtiumOutput.implicitCount 0 = 0 :=
  rfl

/-- Therefore there are no materialized hydrogen slots at all. -/
theorem nonProtium_no_hydrogen_slots :
    Fintype.card (HydrogenSlot nonProtiumOutput.implicitCount) = 0 := by
  rw [hydrogenSlot_card]
  rw [Fin.sum_univ_one]
  exact nonProtium_implicitCount_zero

/-- The expanded graph still has exactly one atom: the two lone pairs, the vacancy and the two CIP
reference slots did not become hydrogen atoms. -/
theorem nonProtium_one_atom :
    Fintype.card (ExpandedLabel nonProtiumOutput.implicitCount) = 1 := by
  rw [Fintype.card_sum, nonProtium_no_hydrogen_slots, Fintype.card_fin, Nat.add_zero]

/-- The residual output still records the two lone pairs. -/
theorem nonProtium_lonePairs : (nonProtiumOutput.residual 0).lonePairs = 2 :=
  rfl

/-- The residual output still records the vacancy position. -/
theorem nonProtium_vacancies : (nonProtiumOutput.residual 0).vacancies = 1 :=
  rfl

/-- The residual output still records the zero unpaired positions. -/
theorem nonProtium_unpairedElectronPositions :
    (nonProtiumOutput.residual 0).unpairedElectronPositions = 0 :=
  rfl

/-- The residual output still records the CIP notional phantom. -/
theorem nonProtium_cipNotionalPhantoms :
    (nonProtiumOutput.residual 0).cipNotionalPhantoms = 1 :=
  rfl

/-- The residual output still records the CIP virtual duplicate. -/
theorem nonProtium_cipVirtualDuplicates :
    (nonProtiumOutput.residual 0).cipVirtualDuplicates = 1 :=
  rfl

/-- Whole-source recovery for the nonzero non-protium formal source. -/
theorem nonProtium_decode_materialize :
    decode nonProtiumOutput = nonProtiumInput :=
  decode_materialize nonProtiumInput

/-- The decoded counts still carry the two lone pairs exactly. -/
theorem nonProtium_decoded_lonePairs :
    ((decode nonProtiumOutput).siteSource.siteCounts.counts 0).lonePairs = 2 := by
  rw [nonProtium_decode_materialize]
  rfl

/-- The decoded counts still carry the vacancy exactly. -/
theorem nonProtium_decoded_vacancies :
    ((decode nonProtiumOutput).siteSource.siteCounts.counts 0).vacancies = 1 := by
  rw [nonProtium_decode_materialize]
  rfl

/-- The decoded counts still carry both CIP reference fields exactly. -/
theorem nonProtium_decoded_cip_fields :
    ((decode nonProtiumOutput).siteSource.siteCounts.counts 0).cipNotionalPhantoms = 1 ∧
      ((decode nonProtiumOutput).siteSource.siteCounts.counts 0).cipVirtualDuplicates = 1 := by
  rw [nonProtium_decode_materialize]
  exact ⟨rfl, rfl⟩

/-! ## Kernel-checked API assertions -/

#check WholeSource
#check MaterializedOutput
#check materialize
#check decode
#check decode_materialize
#check materialize_decode
#check introducedSlots_eq_hydrogenOccurrences
#check introducedOwnerSlots_length
#check materialize_image_decode_image

example (input : WholeSource V) : decode (materialize input) = input :=
  decode_materialize input

example (output : MaterializedOutput V) : materialize (decode output) = output :=
  materialize_decode output

example (input : WholeSource V) (owner : V) :
    ((decode (materialize input)).siteSource.siteCounts.counts owner).lonePairs =
      (input.siteSource.siteCounts.counts owner).lonePairs := by
  rw [decode_materialize]

end OrganicStereoMaterializedSiteSourceRecovery
end OneCenter
end TetraStereo
