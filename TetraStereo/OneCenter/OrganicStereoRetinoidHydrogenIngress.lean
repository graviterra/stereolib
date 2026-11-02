import TetraStereo.OneCenter.OrganicStereoCertifiedSourceCoreCompletion
import TetraStereo.OneCenter.OrganicStereoInventoryImplicitHMaterialization
import TetraStereo.OneCenter.Retinoid1981FigureCatalogImplicitHydrogen
import TetraStereo.KernelOnly
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace RetinoidHydrogenIngress

open FigureGraphTranscription
open FigureAuthorityInput
open StereoparentTableAuthorityInput
open StereoparentTableImplicitHydrogen
open FigureCatalogImplicitHydrogen

open OrganicStereoInventoryImplicitHMaterialization
open OrganicStereoCertifiedSourceCoreCompletion
open OrganicStereoMolecularEvidenceAssembly

/-!
# Ingress of the completed retinoid implicit-hydrogen records into the universal materializer

The two actual completion batches

* `StereoparentTableImplicitHydrogen.CompletedStereoparentTableImplicitHydrogen` (ten Ret-2 table
  structures), and
* `FigureCatalogImplicitHydrogen.CompletedSourceSpecificFigureImplicitHydrogen` (seventeen
  figure-catalog compounds),

each carry a heavy-atom graph, an explicit implicit-hydrogen list, a molecular formula and the
exactness certificates tying them together.  This module composes those records with the *existing*
universal materializer
`OrganicStereoInventoryImplicitHMaterialization.expand` and with the approved molecular core
`OrganicStereoCertifiedSourceCoreCompletion.constructedCore`.

No second expansion, decoder or codec is introduced.  `expand`, `restore`, `introducedSlots`,
`FiniteAtomInteractionHypergraph.certifiedEncoding`,
`CertifiedAuthoritativeChemicalInput.decode` and `constructedCore` are exactly the existing ones.

## The count/connectivity frontier

`CertifiedGraphAuthorityInput` and `CertifiedStereoparentTableAuthorityInput` record only atom and
interaction *count* equalities.  Counts never identify elements or connectivity, so every
materialization theorem below takes an explicit actual conversion witness

`heavyAtomGraphToAuthoritativeChemicalInput? graph = some certified.input`

and derives the fieldwise graph conversion facts from it.  Counts are never used to guess the
formula, the element distribution or the bond structure.  `certifiedConversion_of_stereoparent_certify?`
and `certifiedConversion_of_figure_certify?` supply the same witness from the actual `certify?`
computations when a caller has one.

## Scope

This is representation-only: it does not consult a descriptor oracle, does not decide chemical
admissibility, and does not touch the existing `toMoleculeGraph` / Rule-2 isotope question.  The
source identifier, formula and count payload is retained as typed data in the source-bound output;
the graph decoder never takes it, and no claim is made that graph-only encoding recovers naming
identifiers.
-/

/-! ## List plumbing -/

/-- A successful `List.mapM` over `Option` preserves the length of the input list. -/
theorem mapM_some_length {α β : Type*} {f : α → Option β} {items : List α} {out : List β}
    (h : items.mapM f = some out) : out.length = items.length := by
  induction items generalizing out with
  | nil =>
      simp only [List.mapM_nil, Option.some.injEq] at h
      cases h
      rfl
  | cons head tail ih =>
      rw [List.mapM_cons] at h
      change (f head).bind
          (fun item => (tail.mapM f).bind (fun rest => some (item :: rest))) = some out at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨item, _hitem, htail⟩ := h
      rw [Option.bind_eq_some_iff] at htail
      obtain ⟨rest, hrest, hout⟩ := htail
      rw [Option.some.injEq] at hout
      cases hout
      simp [ih hrest]

/-! ## Fieldwise facts of the actual heavy-graph conversion -/

/-- **Fieldwise conversion facts.**  A successful conversion of a `HeavyAtomGraph` produces
exactly the `mapM` image of the node list and of the bond list, and the stored molecule is exactly
that image.  These are the facts from which all later element/count consequences are derived. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_fields
    {graph : HeavyAtomGraph} {input : AuthoritativeChemicalInput}
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    ∃ (atoms : List SemanticAtom) (interactions : List SemanticInteraction),
      graph.nodes.mapM atomNodeToSemanticAtom? = some atoms ∧
        graph.bonds.mapM (graphBondToSemanticInteraction? graph) = some interactions ∧
          input.molecule.atoms = atoms ∧ input.molecule.interactions = interactions := by
  unfold heavyAtomGraphToAuthoritativeChemicalInput? at converted
  change (graph.nodes.mapM atomNodeToSemanticAtom?).bind
      (fun atoms => (graph.bonds.mapM (graphBondToSemanticInteraction? graph)).bind
        (fun interactions =>
          some { molecule := { atoms := atoms, interactions := interactions } })) =
      some input at converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨atoms, hatoms, converted⟩ := converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨interactions, hbonds, hvalue⟩ := converted
  rw [Option.some.injEq] at hvalue
  cases hvalue
  exact ⟨atoms, interactions, hatoms, hbonds, rfl, rfl⟩

/-- Atom cardinality from the actual conversion, not from a supplied count certificate. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_atomCount
    {graph : HeavyAtomGraph} {input : AuthoritativeChemicalInput}
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    input.molecule.atomCount = graph.nodes.length := by
  obtain ⟨atoms, _interactions, hatoms, _hbonds, hatomsEq, _hinteractionsEq⟩ :=
    heavyAtomGraphToAuthoritativeChemicalInput?_fields converted
  change input.molecule.atoms.length = graph.nodes.length
  rw [hatomsEq]
  exact mapM_some_length hatoms

/-- Interaction cardinality from the actual conversion, not from a supplied count certificate. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_interactionCount
    {graph : HeavyAtomGraph} {input : AuthoritativeChemicalInput}
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    input.molecule.interactions.length = graph.bonds.length := by
  obtain ⟨_atoms, interactions, _hatoms, hbonds, _hatomsEq, hinteractionsEq⟩ :=
    heavyAtomGraphToAuthoritativeChemicalInput?_fields converted
  rw [hinteractionsEq]
  exact mapM_some_length hbonds

/-- Bridge from the actual stereoparent-table `certify?` computation to the raw conversion
witness. -/
theorem certifiedConversion_of_stereoparent_certify?
    (candidate : StereoparentTableGraphEntry)
    (entry : CertifiedStereoparentTableAuthorityInput)
    (certified : candidate.certify? = some entry) :
    heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph = some entry.certified.input := by
  unfold StereoparentTableGraphEntry.certify? at certified
  change (heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph).bind
      (fun input => (input.certify?).bind
        (fun certified =>
          if atomCountExact :
              certified.input.molecule.atoms.length = candidate.graph.nodes.length then
            if interactionCountExact :
                certified.input.molecule.interactions.length = candidate.graph.bonds.length then
              some
                { candidate := candidate
                  certified := certified
                  atomCountExact := atomCountExact
                  interactionCountExact := interactionCountExact }
            else none
          else none)) = some entry at certified
  rw [Option.bind_eq_some_iff] at certified
  obtain ⟨input, hconverted, certified⟩ := certified
  rw [Option.bind_eq_some_iff] at certified
  obtain ⟨certifiedInput, hcertified, hrest⟩ := certified
  split at hrest
  · split at hrest
    · rw [Option.some.injEq] at hrest
      cases hrest
      unfold AuthoritativeChemicalInput.certify? at hcertified
      split at hcertified
      · rw [Option.some.injEq] at hcertified
        cases hcertified
        simpa using hconverted
      · cases hcertified
    · cases hrest
  · cases hrest

/-- Bridge from the actual figure-catalog `certify?` computation to the raw conversion
witness. -/
theorem certifiedConversion_of_figure_certify?
    (candidate : AuthorityInputCandidate)
    (entry : CertifiedGraphAuthorityInput)
    (certified : candidate.certify? = some entry) :
    heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph = some entry.certified.input := by
  unfold AuthorityInputCandidate.certify? at certified
  change (heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph).bind
      (fun input => (input.certify?).bind
        (fun certified =>
          if atomCountExact :
              certified.input.molecule.atoms.length = candidate.graph.nodes.length then
            if interactionCountExact :
                certified.input.molecule.interactions.length = candidate.graph.bonds.length then
              some
                { candidate := candidate
                  certified := certified
                  atomCountExact := atomCountExact
                  interactionCountExact := interactionCountExact }
            else none
          else none)) = some entry at certified
  rw [Option.bind_eq_some_iff] at certified
  obtain ⟨input, hconverted, certified⟩ := certified
  rw [Option.bind_eq_some_iff] at certified
  obtain ⟨certifiedInput, hcertified, hrest⟩ := certified
  split at hrest
  · split at hrest
    · rw [Option.some.injEq] at hrest
      cases hrest
      unfold AuthoritativeChemicalInput.certify? at hcertified
      split at hcertified
      · rw [Option.some.injEq] at hcertified
        cases hcertified
        simpa using hconverted
      · cases hcertified
    · cases hrest
  · cases hrest

/-! ## The shared completed record -/

/-- The common shape of the two actual completed implicit-hydrogen records.  The four certificates
are *transported* from the source record; nothing is re-derived and no count is guessed. -/
structure HydrogenCompletionRecord where
  /-- The actual heavy-atom graph. -/
  graph : HeavyAtomGraph
  /-- The explicit per-heavy-atom implicit-hydrogen list, in node order. -/
  implicitHydrogens : List Nat
  /-- The molecular formula computed by the source completion. -/
  formula : MolecularFormula
  /-- The source's own local-valence certificate. -/
  hydrogenCountsExact : implicitHydrogenCounts? graph = some implicitHydrogens
  /-- The source's own formula certificate. -/
  formulaExact : formula = formulaFromImplicitHydrogens graph implicitHydrogens
  /-- The source's own one-entry-per-node certificate. -/
  atomCoverageExact : implicitHydrogens.length = graph.nodes.length
  /-- The source's own heavy-atom total certificate. -/
  heavyAtomCountExact : formula.heavyAtomCount = graph.nodes.length

/-- Projection of the actual Ret-2 stereoparent-table completion records. -/
def ofStereoparentTable (entry : CompletedStereoparentTableImplicitHydrogen) :
    HydrogenCompletionRecord where
  graph := entry.candidate.graph
  implicitHydrogens := entry.implicitHydrogens
  formula := entry.formula
  hydrogenCountsExact := entry.implicitHydrogensExact
  formulaExact := entry.formulaExact
  atomCoverageExact := entry.atomCoverageExact
  heavyAtomCountExact := entry.heavyAtomCountExact

/-- Projection of the actual figure-catalog completion records. -/
def ofSourceSpecificFigure (entry : CompletedSourceSpecificFigureImplicitHydrogen) :
    HydrogenCompletionRecord where
  graph := entry.candidate.candidate.graph
  implicitHydrogens := entry.implicitHydrogens
  formula := entry.formula
  hydrogenCountsExact := entry.implicitHydrogensExact
  formulaExact := entry.formulaExact
  atomCoverageExact := entry.atomCoverageExact
  heavyAtomCountExact := entry.heavyAtomCountExact

/-- The source formula's hydrogen total is exactly the supplied list sum. -/
theorem completion_formula_hydrogen (record : HydrogenCompletionRecord) :
    record.formula.hydrogen = record.implicitHydrogens.sum := by
  rw [record.formulaExact]
  rfl

/-! ## Indexing the actual hydrogen list by the actual heavy atoms -/

/-- The actual atom count equals the actual hydrogen-list length: the atom count comes from the
successful conversion, the list length from the source completion certificate. -/
def completionLength (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    certified.input.molecule.atomCount = record.implicitHydrogens.length :=
  (heavyAtomGraphToAuthoritativeChemicalInput?_atomCount converted).trans
    record.atomCoverageExact.symm

/-- The supplied implicit-hydrogen multiplicity, indexed by the actual heavy atom `Fin` label.
The list is read at the index carried by the source completion's coverage certificate. -/
def completionCount (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    Fin certified.input.molecule.atomCount → ℕ :=
  fun index =>
    record.implicitHydrogens.get (Fin.cast (completionLength record certified converted) index)

/-- The indexed multiplicity list is exactly the source's implicit-hydrogen list, in order. -/
theorem ofFn_completionCount (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    List.ofFn (completionCount record certified converted) = record.implicitHydrogens := by
  let lengthExact := completionLength record certified converted
  change List.ofFn
      (fun index : Fin certified.input.molecule.atomCount =>
        record.implicitHydrogens.get (Fin.cast lengthExact index)) =
    record.implicitHydrogens
  rw [List.ofFn_congr lengthExact]
  have functionEq :
      (fun index : Fin record.implicitHydrogens.length =>
          record.implicitHydrogens.get
            (Fin.cast lengthExact (Fin.cast lengthExact.symm index))) =
        (fun index => record.implicitHydrogens.get index) := by
    funext index
    exact congrArg record.implicitHydrogens.get (Fin.ext rfl)
  rw [functionEq, List.ofFn_get]

/-- **Total hydrogen count.**  The indexed multiplicities sum to the source formula's hydrogen
field.  Together with `ofFn_completionCount` this is the chain
`sum (indexed counts) = sum (supplied list) = formula.hydrogen`. -/
theorem completionCount_total (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (Finset.univ : Finset (Fin certified.input.molecule.atomCount)).sum
        (completionCount record certified converted) =
      record.formula.hydrogen := by
  rw [← Fin.sum_ofFn]
  rw [ofFn_completionCount]
  exact (completion_formula_hydrogen record).symm

/-- The same total expressed as the plain list sum of the source record. -/
theorem completionCount_total_eq_listSum (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (Finset.univ : Finset (Fin certified.input.molecule.atomCount)).sum
        (completionCount record certified converted) =
      record.implicitHydrogens.sum :=
  (completionCount_total record certified converted).trans
    (completion_formula_hydrogen record)

/-! ## Expansion by the existing universal materializer -/

/-- The expanded graph: the existing `expand` applied to the decoded certified graph and the actual
source hydrogen list indexed by the actual heavy atoms. -/
noncomputable def expandedGraph (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    FiniteAtomInteractionHypergraph
      (ExpandedLabel (completionCount record certified converted)) :=
  expand (CertifiedAuthoritativeChemicalInput.decode certified).graph
    (completionCount record certified converted)

/-- Cardinality of the dependent expanded label type. -/
theorem card_expandedLabel {V : Type*} [DecidableEq V] [Fintype V] (count : V → ℕ) :
    Fintype.card (ExpandedLabel count) = Fintype.card V + (Finset.univ : Finset V).sum count := by
  change Fintype.card (V ⊕ HydrogenSlot count) = Fintype.card V + _
  rw [Fintype.card_sum, hydrogenSlot_card]

/-- Heavy atoms keep their exact decoded semantic data. -/
@[simp] theorem expandedGraph_atomData_old (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    (v : Fin certified.input.molecule.atomCount) :
    (expandedGraph record certified converted).atomData (Sum.inl v) =
      (CertifiedAuthoritativeChemicalInput.decode certified).graph.atomData v := rfl

/-- Every new expanded atom is the materialized protium record. -/
@[simp] theorem expandedGraph_atomData_hydrogen (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    (h : HydrogenSlot (completionCount record certified converted)) :
    (expandedGraph record certified converted).atomData (Sum.inr h) = materializedHydrogenAtom := rfl

/-- Original isotope fields are preserved on every heavy atom. -/
theorem expandedGraph_preserves_heavy_isotope (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    (v : Fin certified.input.molecule.atomCount) :
    ((expandedGraph record certified converted).atomData (Sum.inl v)).isotopeMassNumber? =
      ((CertifiedAuthoritativeChemicalInput.decode certified).graph.atomData v).isotopeMassNumber? := by
  rw [expandedGraph_atomData_old]

/-- Every new hydrogen carries no isotope label. -/
@[simp] theorem expandedGraph_hydrogen_isotope (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    (h : HydrogenSlot (completionCount record certified converted)) :
    ((expandedGraph record certified converted).atomData (Sum.inr h)).isotopeMassNumber? = none :=
  materializedHydrogenAtom_isotopeMassNumber

/-- **Slot materialization.**  Every supplied slot gets its tagged hydrogen atom, its selected
single covalent interaction, the exact participant list `[owner, hydrogen]` and the exact kind
`covalent 1`. -/
theorem expandedGraph_materializes_slot (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    (h : HydrogenSlot (completionCount record certified converted)) :
    (expandedGraph record certified converted).atomData (Sum.inr h) = materializedHydrogenAtom ∧
      hydrogenBond (completionCount record certified converted) h ∈
        (expandedGraph record certified converted).interactions ∧
      (hydrogenBond (completionCount record certified converted) h).1 =
        [(Sum.inl h.1 : ExpandedLabel (completionCount record certified converted)), Sum.inr h] ∧
      (hydrogenBond (completionCount record certified converted) h).2 =
        SemanticInteractionKind.covalent 1 := by
  simpa only [expandedGraph] using
    expand_materializes_slot (CertifiedAuthoritativeChemicalInput.decode certified).graph
      (completionCount record certified converted) h

/-- Every original interaction survives with its participants tagged as heavy atoms and its kind
unchanged. -/
theorem expandedGraph_original_mem (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    {edge : List (Fin certified.input.molecule.atomCount) × SemanticInteractionKind}
    (member : edge ∈ (CertifiedAuthoritativeChemicalInput.decode certified).graph.interactions) :
    liftInteraction (completionCount record certified converted) edge ∈
      (expandedGraph record certified converted).interactions := by
  rw [expandedGraph]
  exact expand_lift_mem _ _ member

/-- Heavy–heavy pair bond orders are unchanged by the expansion. -/
theorem expandedGraph_pairBond_heavy (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    (a b : Fin certified.input.molecule.atomCount) :
    pairBond (expandedGraph record certified converted) (Sum.inl a) (Sum.inl b) =
      pairBond (CertifiedAuthoritativeChemicalInput.decode certified).graph a b := by
  rw [expandedGraph]
  exact pairBond_expand_inl_inl _ _ a b

/-- The selected interaction makes each materialized hydrogen a positive-bond neighbor of its
owner. -/
theorem expandedGraph_pairBond_hydrogen (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input)
    (h : HydrogenSlot (completionCount record certified converted)) :
    0 < pairBond (expandedGraph record certified converted) (Sum.inl h.1) (Sum.inr h) := by
  rw [expandedGraph]
  exact pairBond_expand_selected_pos _ _ h

/-- **Exact heavy-graph recovery.**  The existing `restore` projection reads the expanded graph
alone and recovers exactly the decoded heavy graph.  The source record, the formula and the
identifier are not passed to the decoder. -/
theorem expandedGraph_restore (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    restore (completionCount record certified converted)
        (expandedGraph record certified converted) =
      (CertifiedAuthoritativeChemicalInput.decode certified).graph := by
  rw [expandedGraph, restore_expand]

/-- The number of interactions in the decoded certified graph is the stored interaction count. -/
theorem decode_graph_interactions_length (certified : CertifiedAuthoritativeChemicalInput) :
    (CertifiedAuthoritativeChemicalInput.decode certified).graph.interactions.length =
      certified.input.molecule.interactions.length := by
  rw [CertifiedAuthoritativeChemicalInput.decode_graph, reconstructGraph_interactions]
  unfold reconstructInteractions
  rw [List.length_pmap]

/-- Interaction count of the expanded graph: every original interaction plus one selected bond per
supplied hydrogen slot. -/
theorem expandedGraph_interactions_length (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (expandedGraph record certified converted).interactions.length =
      certified.input.molecule.interactions.length + record.formula.hydrogen := by
  rw [expandedGraph, expand_interactions_length, hydrogenSlot_card, completionCount_total,
    decode_graph_interactions_length]

/-- The introduced slot family decoded from the expanded interactions alone has exactly the source
formula's hydrogen cardinality. -/
theorem expandedGraph_introducedSlots_length (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (introducedSlots (completionCount record certified converted)
        (expandedGraph record certified converted)).length =
      record.formula.hydrogen := by
  rw [expandedGraph, introducedSlots_expand_length, completionCount_total]

/-! ## The actual molecular representation -/

/-- The expanded graph certified by the existing `certifiedEncoding` at the canonical
enumeration. -/
noncomputable def expandedCertified (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    CertifiedAuthoritativeChemicalInput :=
  (expandedGraph record certified converted).certifiedEncoding
    (FiniteAtomInteractionHypergraph.canonicalEnumeration
      (ExpandedLabel (completionCount record certified converted)))

@[simp] theorem expandedCertified_input_molecule (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (expandedCertified record certified converted).input.molecule =
      (expandedGraph record certified converted).encode
        (FiniteAtomInteractionHypergraph.canonicalEnumeration
          (ExpandedLabel (completionCount record certified converted))) := rfl

/-- The certified expanded molecule has exactly the heavy atoms plus one atom per supplied
implicit hydrogen. -/
theorem expandedCertified_atomCount (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (expandedCertified record certified converted).input.molecule.atomCount =
      certified.input.molecule.atomCount + record.formula.hydrogen := by
  rw [expandedCertified, FiniteAtomInteractionHypergraph.certifiedEncoding_input,
    FiniteAtomInteractionHypergraph.encodeAuthoritative_molecule,
    FiniteAtomInteractionHypergraph.encode_atomCount]
  rw [card_expandedLabel, Fintype.card_fin, completionCount_total]

/-- The certified expanded molecule has exactly the original interactions plus one selected bond
per supplied implicit hydrogen. -/
theorem expandedCertified_interactionCount (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (expandedCertified record certified converted).input.molecule.interactions.length =
      certified.input.molecule.interactions.length + record.formula.hydrogen := by
  rw [expandedCertified, FiniteAtomInteractionHypergraph.certifiedEncoding_input,
    FiniteAtomInteractionHypergraph.encodeAuthoritative_molecule]
  simp only [FiniteAtomInteractionHypergraph.encode, List.length_map]
  rw [expandedGraph_interactions_length]

/-- The heavy-atom total carried by the certified molecule is the source formula's heavy-atom
total. -/
theorem expandedCertified_heavyAtomCount (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    record.formula.heavyAtomCount = certified.input.molecule.atomCount := by
  rw [record.heavyAtomCountExact]
  exact (heavyAtomGraphToAuthoritativeChemicalInput?_atomCount converted).symm

/-- The actual independent molecular core of the expanded certified input, via the approved
`constructedCore`. -/
noncomputable def expandedCore (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    OrganicMolecularEvidence
      (Fin (expandedCertified record certified converted).input.molecule.atomCount) :=
  constructedCore (expandedCertified record certified converted)

/-- The constructed expanded core carries exactly the expanded certified input through the existing
`recoveredSource` at the constructed enumeration. -/
theorem expandedCore_recovers_source (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    recoveredSource (expandedCore record certified converted)
        (constructedEnumeration (expandedCertified record certified converted)) =
      (expandedCertified record certified converted).input := by
  rw [expandedCore]
  exact recoveredSource_constructedCore _

/-- The expanded core's finite graph is the decoded expanded graph. -/
theorem expandedCore_graph (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (expandedCore record certified converted).graph =
      (CertifiedAuthoritativeChemicalInput.decode
        (expandedCertified record certified converted)).graph := by
  rw [expandedCore]
  exact constructedCore_graph _

/-- The approved common molecular core of the original certified input. -/
noncomputable def sourceCore (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicMolecularEvidence (Fin certified.input.molecule.atomCount) :=
  constructedCore certified

/-- The original common core recovers the original certified input exactly. -/
theorem sourceCore_recovers_source (certified : CertifiedAuthoritativeChemicalInput) :
    recoveredSource (sourceCore certified) (constructedEnumeration certified) =
      certified.input := by
  rw [sourceCore]
  exact recoveredSource_constructedCore certified

/-- The expansion's restored heavy graph encodes back to exactly the certified molecule. -/
theorem expandedGraph_restores_certified_molecule (record : HydrogenCompletionRecord)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input) :
    (restore (completionCount record certified converted)
        (expandedGraph record certified converted)).encode
        (identityEnumeration certified.input.molecule.atomCount) =
      certified.input.molecule := by
  rw [expandedGraph_restore]
  exact CertifiedAuthoritativeChemicalInput.encode_decode_molecule certified

/-! ## Source-bound materialization -/

/-- The typed source payload: identifier, formula, actual hydrogen list and heavy-atom total,
together with the source certificates.  This is ordinary typed data, not an opaque blob. -/
structure SourcePayload (Identity : Type*) where
  /-- The source identifier (structure number or artifact/variant pair). -/
  identity : Identity
  /-- The source molecular formula. -/
  formula : MolecularFormula
  /-- The source implicit-hydrogen list. -/
  implicitHydrogens : List Nat
  /-- The source heavy-atom total. -/
  graphNodeCount : Nat
  /-- The formula's hydrogen field is the list sum. -/
  hydrogenExact : formula.hydrogen = implicitHydrogens.sum
  /-- The list has one entry per heavy atom. -/
  atomCoverage : implicitHydrogens.length = graphNodeCount
  /-- The formula's heavy-atom total is the node count. -/
  heavyAtomCountExact : formula.heavyAtomCount = graphNodeCount

/-- A completed retinoid hydrogen record together with its actual certified conversion.  The
identifier is retained in the output; it is never needed by the graph decoder. -/
structure SourceBoundMaterialization (Identity : Type*) where
  /-- The exact source identifier. -/
  identity : Identity
  /-- The actual completed hydrogen record. -/
  record : HydrogenCompletionRecord
  /-- The actual certified authoritative input obtained from the heavy graph. -/
  certified : CertifiedAuthoritativeChemicalInput
  /-- The actual conversion witness: the certified input is the conversion image of the graph. -/
  conversion : heavyAtomGraphToAuthoritativeChemicalInput? record.graph = some certified.input

/-- **Native materialization output.**  This is the source-free side of the boundary: it carries
the expanded graph built by the universal materializer, the *expanded* certified input and core,
and the explicit count/formula/native metadata.  It does **not** carry the original heavy record or
the original certified input.  The decoder (`restore`, `introducedSlots`) accepts only the `count`
and `expanded` fields of this structure. -/
structure NativeMaterializedOutput (Identity : Type*) where
  /-- The exact source identifier, retained as typed metadata. -/
  identity : Identity
  /-- The source molecular formula, retained as typed metadata. -/
  formula : MolecularFormula
  /-- The source implicit-hydrogen list, retained as typed metadata. -/
  implicitHydrogens : List Nat
  /-- The explicit number of heavy atoms. -/
  heavyAtomCount : Nat
  /-- The formula's hydrogen field is the list sum. -/
  hydrogenExact : formula.hydrogen = implicitHydrogens.sum
  /-- The list has one entry per heavy atom. -/
  atomCoverage : implicitHydrogens.length = heavyAtomCount
  /-- The formula's heavy-atom total is the explicit heavy count. -/
  heavyAtomCountExact : formula.heavyAtomCount = heavyAtomCount
  /-- The explicit per-heavy-atom hydrogen multiplicities. -/
  count : Fin heavyAtomCount → Nat
  /-- The count function is exactly the retained hydrogen list. -/
  countExact : List.ofFn count = implicitHydrogens
  /-- The expanded graph produced by the existing universal materializer. -/
  expanded : FiniteAtomInteractionHypergraph (ExpandedLabel count)
  /-- The expanded certified input obtained from the expanded graph. -/
  expandedCertified : CertifiedAuthoritativeChemicalInput
  /-- The expanded certified input is exactly the encoding of the expanded graph. -/
  expandedCertifiedExact :
    expandedCertified =
      expanded.certifiedEncoding
        (FiniteAtomInteractionHypergraph.canonicalEnumeration (ExpandedLabel count))
  /-- The actual molecular core constructed from the expanded certified input. -/
  core : OrganicMolecularEvidence (Fin expandedCertified.input.molecule.atomCount)
  /-- The core is exactly the approved `constructedCore` of the expanded certified input. -/
  coreExact : core = constructedCore expandedCertified

namespace NativeMaterializedOutput

variable {Identity : Type*} (output : NativeMaterializedOutput Identity)

/-- Native heavy-graph readback: the existing `restore` applied only to output fields. -/
noncomputable def heavyGraph : FiniteAtomInteractionHypergraph (Fin output.heavyAtomCount) :=
  restore output.count output.expanded

/-- Native introduced-hydrogen readback: the existing `introducedSlots` applied only to output
fields. -/
noncomputable def hydrogenSlots : List (HydrogenSlot output.count) :=
  introducedSlots output.count output.expanded

/-- The explicit count function sums to the retained formula's hydrogen total. -/
theorem sum_count :
    (Finset.univ : Finset (Fin output.heavyAtomCount)).sum output.count =
      output.formula.hydrogen := by
  rw [← Fin.sum_ofFn, output.countExact]
  exact output.hydrogenExact.symm

/-- The expanded certified input is exactly the encoding of the expanded graph. -/
theorem expandedCertified_input_molecule :
    output.expandedCertified.input.molecule =
      output.expanded.encode
        (FiniteAtomInteractionHypergraph.canonicalEnumeration
          (ExpandedLabel output.count)) := by
  rw [output.expandedCertifiedExact]
  rfl

/-- The core carried by native output recovers its expanded certified input, using no original
source record and no original certified field. -/
theorem core_recovers_source :
    recoveredSource output.core
        (constructedEnumeration output.expandedCertified) =
      output.expandedCertified.input := by
  rw [output.coreExact]
  exact recoveredSource_constructedCore output.expandedCertified

end NativeMaterializedOutput

namespace SourceBoundMaterialization

variable {Identity : Type*} (self : SourceBoundMaterialization Identity)

/-- The typed source payload. -/
def payload : SourcePayload Identity where
  identity := self.identity
  formula := self.record.formula
  implicitHydrogens := self.record.implicitHydrogens
  graphNodeCount := self.record.graph.nodes.length
  hydrogenExact := completion_formula_hydrogen self.record
  atomCoverage := self.record.atomCoverageExact
  heavyAtomCountExact := self.record.heavyAtomCountExact

@[simp] theorem payload_implicitHydrogens :
    self.payload.implicitHydrogens = self.record.implicitHydrogens := rfl

@[simp] theorem payload_formula : self.payload.formula = self.record.formula := rfl

@[simp] theorem payload_identity : self.payload.identity = self.identity := rfl

/-- The actual implicit-hydrogen multiplicity indexed by the heavy atoms. -/
def count : Fin self.certified.input.molecule.atomCount → ℕ :=
  completionCount self.record self.certified self.conversion

/-- The indexed multiplicity list is the record's own hydrogen list. -/
theorem count_ofFn : List.ofFn self.count = self.record.implicitHydrogens :=
  ofFn_completionCount self.record self.certified self.conversion

/-- The indexed multiplicities sum to the payload formula's hydrogen total. -/
theorem count_total :
    (Finset.univ : Finset (Fin self.certified.input.molecule.atomCount)).sum self.count =
      self.payload.formula.hydrogen :=
  completionCount_total self.record self.certified self.conversion

/-- The expanded graph built by the existing universal materializer. -/
noncomputable def expanded :
    FiniteAtomInteractionHypergraph
      (ExpandedLabel (completionCount self.record self.certified self.conversion)) :=
  expandedGraph self.record self.certified self.conversion

/-- The expanded certified input. -/
noncomputable def expandedCertified : CertifiedAuthoritativeChemicalInput :=
  (expandedGraph self.record self.certified self.conversion).certifiedEncoding
    (FiniteAtomInteractionHypergraph.canonicalEnumeration
      (ExpandedLabel (completionCount self.record self.certified self.conversion)))

/-- The expanded actual molecular core. -/
noncomputable def expandedCore :
    OrganicMolecularEvidence (Fin self.expandedCertified.input.molecule.atomCount) :=
  constructedCore self.expandedCertified

/-- Exact heavy-graph recovery from the expanded graph alone. -/
theorem expanded_restore :
    restore self.count self.expanded =
      (CertifiedAuthoritativeChemicalInput.decode self.certified).graph :=
  expandedGraph_restore self.record self.certified self.conversion

/-- The introduced slot family of the expanded graph has the payload's hydrogen cardinality. -/
theorem expanded_introducedSlots_length :
    (introducedSlots self.count self.expanded).length = self.payload.formula.hydrogen :=
  expandedGraph_introducedSlots_length self.record self.certified self.conversion

/-- Expanded atom count. -/
theorem expanded_atomCount :
    self.expandedCertified.input.molecule.atomCount =
      self.certified.input.molecule.atomCount + self.payload.formula.hydrogen :=
  expandedCertified_atomCount self.record self.certified self.conversion

/-- Expanded interaction count. -/
theorem expanded_interactionCount :
    self.expandedCertified.input.molecule.interactions.length =
      self.certified.input.molecule.interactions.length + self.payload.formula.hydrogen :=
  expandedCertified_interactionCount self.record self.certified self.conversion

/-- Native readback uses only the supplied count function and the expanded graph: the existing
`restore` recovers the decoded heavy graph and the existing `introducedSlots` recovers the full
materialized hydrogen family.  The original certified heavy source is neither a decoder argument nor
re-encoded into the output. -/
theorem native_readback :
    restore self.count self.expanded =
        (CertifiedAuthoritativeChemicalInput.decode self.certified).graph ∧
      (introducedSlots self.count self.expanded).length =
        self.payload.formula.hydrogen :=
  ⟨expanded_restore self, expanded_introducedSlots_length self⟩

/-- The expanded core recovers exactly the expanded certified input. -/
theorem expandedCore_recovers_source :
    recoveredSource self.expandedCore
        (constructedEnumeration self.expandedCertified) =
      self.expandedCertified.input := by
  dsimp only [expandedCore]
  exact recoveredSource_constructedCore _

/-- **Native output construction.**  The original record and original certified input are used
only here, to build the output; they are not stored.  Every readback function below consumes only
native output fields. -/
noncomputable def nativeOutput : NativeMaterializedOutput Identity where
  identity := self.identity
  formula := self.payload.formula
  implicitHydrogens := self.payload.implicitHydrogens
  heavyAtomCount := self.certified.input.molecule.atomCount
  hydrogenExact := self.payload.hydrogenExact
  atomCoverage := (completionLength self.record self.certified self.conversion).symm
  heavyAtomCountExact :=
    expandedCertified_heavyAtomCount self.record self.certified self.conversion
  count := self.count
  countExact := self.count_ofFn
  expanded := self.expanded
  expandedCertified := self.expandedCertified
  expandedCertifiedExact := rfl
  core := self.expandedCore
  coreExact := rfl

/-- **Decoded source equality.**  The native heavy graph (the existing `restore` applied only to
native output fields) is exactly the decoded graph of the original certified input.  The actual
conversion witness is the input proof used to build the output, not a decoder argument. -/
theorem nativeOutput_heavyGraph :
    self.nativeOutput.heavyGraph =
      (CertifiedAuthoritativeChemicalInput.decode self.certified).graph :=
  self.expanded_restore

/-- Re-encoding the natively decoded heavy graph yields exactly the *original* certified
molecule. -/
theorem nativeOutput_decodes_original_molecule :
    self.nativeOutput.heavyGraph.encode
        (identityEnumeration self.certified.input.molecule.atomCount) =
      self.certified.input.molecule :=
  expandedGraph_restores_certified_molecule self.record self.certified self.conversion

/-- The introduced hydrogen family read back from native output alone has the retained formula's
hydrogen cardinality. -/
theorem nativeOutput_hydrogenSlots_length :
    self.nativeOutput.hydrogenSlots.length =
      self.nativeOutput.formula.hydrogen :=
  self.expanded_introducedSlots_length

/-- The molecular core recovered from native output alone is exactly the expanded certified
input. -/
theorem nativeOutput_core_recovers :
    recoveredSource self.nativeOutput.core
        (constructedEnumeration self.nativeOutput.expandedCertified) =
      self.nativeOutput.expandedCertified.input :=
  self.expandedCore_recovers_source

/-- The native count function sums to the retained formula's hydrogen total. -/
theorem nativeOutput_count_total :
    (Finset.univ : Finset (Fin self.nativeOutput.heavyAtomCount)).sum
        self.nativeOutput.count =
      self.nativeOutput.formula.hydrogen :=
  NativeMaterializedOutput.sum_count self.nativeOutput

end SourceBoundMaterialization

/-- Materialize an actual Ret-2 stereoparent-table completion record at its structure number. -/
def materializeStereoparent (entry : CompletedStereoparentTableImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.graph =
      some certified.input) :
    SourceBoundMaterialization Nat where
  identity := entry.candidate.row.structureNumber
  record := ofStereoparentTable entry
  certified := certified
  conversion := converted

/-- Materialize an actual figure-catalog completion record at its artifact/variant pair. -/
def materializeFigure (entry : CompletedSourceSpecificFigureImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.candidate.graph =
      some certified.input) :
    SourceBoundMaterialization (SourceAudit.ImageArtifact × SourceSpecificVariant) where
  identity := (entry.candidate.candidate.artifact, entry.candidate.variant)
  record := ofSourceSpecificFigure entry
  certified := certified
  conversion := converted

@[simp] theorem materializeStereoparent_identity
    (entry : CompletedStereoparentTableImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.graph =
      some certified.input) :
    (materializeStereoparent entry certified converted).identity =
      entry.candidate.row.structureNumber := rfl

@[simp] theorem materializeStereoparent_formula
    (entry : CompletedStereoparentTableImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.graph =
      some certified.input) :
    (materializeStereoparent entry certified converted).payload.formula = entry.formula := rfl

@[simp] theorem materializeStereoparent_hydrogens
    (entry : CompletedStereoparentTableImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.graph =
      some certified.input) :
    (materializeStereoparent entry certified converted).payload.implicitHydrogens =
      entry.implicitHydrogens := rfl

@[simp] theorem materializeStereoparent_count_ofFn
    (entry : CompletedStereoparentTableImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.graph =
      some certified.input) :
    List.ofFn (materializeStereoparent entry certified converted).count =
      entry.implicitHydrogens :=
  SourceBoundMaterialization.count_ofFn _

@[simp] theorem materializeFigure_identity
    (entry : CompletedSourceSpecificFigureImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.candidate.graph =
      some certified.input) :
    (materializeFigure entry certified converted).identity =
      (entry.candidate.candidate.artifact, entry.candidate.variant) := rfl

@[simp] theorem materializeFigure_formula
    (entry : CompletedSourceSpecificFigureImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.candidate.graph =
      some certified.input) :
    (materializeFigure entry certified converted).payload.formula = entry.formula := rfl

@[simp] theorem materializeFigure_hydrogens
    (entry : CompletedSourceSpecificFigureImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.candidate.graph =
      some certified.input) :
    (materializeFigure entry certified converted).payload.implicitHydrogens =
      entry.implicitHydrogens := rfl

@[simp] theorem materializeFigure_count_ofFn
    (entry : CompletedSourceSpecificFigureImplicitHydrogen)
    (certified : CertifiedAuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? entry.candidate.candidate.graph =
      some certified.input) :
    List.ofFn (materializeFigure entry certified converted).count =
      entry.implicitHydrogens :=
  SourceBoundMaterialization.count_ofFn _

end RetinoidHydrogenIngress
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.heavyAtomGraphToAuthoritativeChemicalInput?_fields
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.heavyAtomGraphToAuthoritativeChemicalInput?_atomCount
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.certifiedConversion_of_stereoparent_certify?
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.certifiedConversion_of_figure_certify?
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.completion_formula_hydrogen
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.ofFn_completionCount
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.completionCount_total
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.expandedGraph_restore
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.expandedGraph_materializes_slot
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.expandedGraph_interactions_length
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.expandedGraph_introducedSlots_length
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.expandedCertified_atomCount
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.expandedCertified_interactionCount
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.expandedCore_recovers_source
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.SourceBoundMaterialization.native_readback
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.NativeMaterializedOutput.sum_count
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.NativeMaterializedOutput.core_recovers_source
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.NativeMaterializedOutput.expandedCertified_input_molecule
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.SourceBoundMaterialization.nativeOutput_heavyGraph
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.SourceBoundMaterialization.nativeOutput_decodes_original_molecule
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.SourceBoundMaterialization.nativeOutput_hydrogenSlots_length
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.SourceBoundMaterialization.nativeOutput_core_recovers
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.SourceBoundMaterialization.nativeOutput_count_total
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.materializeStereoparent_count_ofFn
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.RetinoidHydrogenIngress.materializeFigure_count_ofFn
