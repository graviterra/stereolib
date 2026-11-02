import Mathlib.Tactic
import TetraStereo.OneCenter.OrganicStereoFragmentSourceData
import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
import TetraStereo.OneCenter.OrganicStereoSpecialistAnnotations
import TetraStereo.OneCenter.OrganicStereoRetinoidConversionBridge
import TetraStereo.OneCenter.Retinoid1981ExplicitCenterLabelCatalog
import TetraStereo.OneCenter.Retinoid1981StereoparentTableAuthorityInput
import TetraStereo.OneCenter.Retinoid1981SourceSpecificAuthorityInput
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter
namespace OrganicStereoNaturalProductAnnotationIngress

open Retinoid1981
open Retinoid1981.FigureGraphTranscription
open Retinoid1981.ExplicitCenterLabelCatalog
open Retinoid1981.FigureAuthorityInput
open Retinoid1981.StereoparentTableAuthorityInput
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport

/-- Observe the original centre-label payload of a natural-product source datum. -/
def naturalCenterLabel? {V : Type} :
    FragmentSourceDatum V → Option LocatedSourceCenterLabel
  | .naturalCenter _ label => some label
  | _ => none

/-- Observe the original double-bond configuration claim of a natural-product source datum. -/
def naturalDoubleBondClaim? {V : Type} :
    FragmentSourceDatum V → Option DoubleBondConfigurationClaim
  | .naturalDoubleBond _ _ claim => some claim
  | _ => none

@[simp] theorem naturalCenterLabel?_naturalCenter {V : Type} (atom : V)
    (label : LocatedSourceCenterLabel) :
    naturalCenterLabel? (.naturalCenter atom label) = some label := rfl

@[simp] theorem naturalCenterLabel?_naturalDoubleBond {V : Type} (source target : V)
    (claim : DoubleBondConfigurationClaim) :
    naturalCenterLabel? (.naturalDoubleBond source target claim) = none := rfl

@[simp] theorem naturalDoubleBondClaim?_naturalDoubleBond {V : Type} (source target : V)
    (claim : DoubleBondConfigurationClaim) :
    naturalDoubleBondClaim? (.naturalDoubleBond source target claim) = some claim := rfl

@[simp] theorem naturalDoubleBondClaim?_naturalCenter {V : Type} (atom : V)
    (label : LocatedSourceCenterLabel) :
    naturalDoubleBondClaim? (.naturalCenter atom label) = none := rfl

/-!
# Retinoid 1981 natural-product annotation ingress

This module is the resolved source-annotation ingress for the actual Ret-1981 excluded-center
labels (`Retinoid1981.ExplicitCenterLabelCatalog.LocatedSourceCenterLabel`) and the actual
configuration claims (`Retinoid1981.FigureGraphTranscription.DoubleBondConfigurationClaim`).

Source locants are resolved through the actual
`Retinoid1981.FigureAuthorityInput.heavyAtomNodeIndex?` locant search into the finite atom labels
of the **actual request core** `FiniteAtomInteractionHypergraph V`.  An explicit
`SourceGraphEmbedding` records, fieldwise, that every source heavy atom carries the core's own
semantic atom record and that every source bond carries its actual ordered endpoint interaction
in `core.interactions`.  The annotation's fragment carries the exact numbered source bindings,
and its `FragmentAnnotation.sourceData` channel is populated with the actual
`FragmentSourceDatum.naturalCenter` and `FragmentSourceDatum.naturalDoubleBond` payloads.

`AuthoritativeConversionBinding` records an actual successful
`heavyAtomGraphToAuthoritativeChemicalInput?` conversion and derives its exact atom and
interaction lists; count equalities are never treated as a structural tie.  The canonical core
used by concrete examples is built from that actual conversion's per-node semantic atoms.

Nothing here derives a CIP label from a source label, materializes hydrogens, or approves a
drawing.  The source D/L, alpha/beta and R/S payloads remain the distinguished source
constructors; E/Z remains a separate field of the actual claim record.
-/

/-! ## Locant-to-index facts for the actual source locant search

`heavyAtomNodeIndex?` is the existing locant search from
`Retinoid1981CertifiedAuthorityInput`.  These are facts about that actual function; no second
locant resolver is introduced. -/

theorem nodeIndexAux?_ge :
    ∀ (nodes : List AtomNode) (locant start index : Nat),
      nodeIndexAux? nodes locant start = some index → start ≤ index := by
  intro nodes
  induction nodes with
  | nil =>
      intro locant start index h
      simp [nodeIndexAux?] at h
  | cons head tail ih =>
      intro locant start index h
      by_cases headEq : head.locant = locant
      · simp only [nodeIndexAux?, headEq, if_pos] at h
        have hindex : index = start := (Option.some.inj h).symm
        omega
      · simp only [nodeIndexAux?, headEq] at h
        have hle := ih locant (start + 1) index h
        omega

theorem nodeIndexAux?_lt_length :
    ∀ (nodes : List AtomNode) (locant start index : Nat),
      nodeIndexAux? nodes locant start = some index → index - start < nodes.length := by
  intro nodes
  induction nodes with
  | nil =>
      intro locant start index h
      simp [nodeIndexAux?] at h
  | cons head tail ih =>
      intro locant start index h
      by_cases headEq : head.locant = locant
      · simp only [nodeIndexAux?, headEq, if_pos] at h
        have hindex : index = start := (Option.some.inj h).symm
        rw [hindex]
        simp
      · simp only [nodeIndexAux?, headEq] at h
        have htail := ih locant (start + 1) index h
        have hge : start + 1 ≤ index := nodeIndexAux?_ge tail locant (start + 1) index h
        simp only [List.length_cons]
        omega

theorem nodeIndexAux?_exists_of_mem (nodes : List AtomNode) (locant start : Nat)
    (h : locant ∈ nodes.map AtomNode.locant) :
    ∃ index, nodeIndexAux? nodes locant start = some index := by
  induction nodes generalizing start with
  | nil => simp at h
  | cons head tail ih =>
      rcases List.mem_map.mp h with ⟨node, hnode, hloc⟩
      by_cases headEq : head.locant = locant
      · exact ⟨start, by simp [nodeIndexAux?, headEq]⟩
      · have hnodeTail : node ∈ tail := by
          rcases List.mem_cons.mp hnode with hhead | htail
          · subst hhead
            exact absurd hloc headEq
          · exact htail
        obtain ⟨index, hindex⟩ :=
          ih (start + 1) (List.mem_map.mpr ⟨node, hnodeTail, hloc⟩)
        exact ⟨index, by simp [nodeIndexAux?, headEq, hindex]⟩

theorem nodeIndexAux?_locant_unique :
    ∀ (nodes : List AtomNode) (first second firstIndex secondIndex start : Nat),
      nodeIndexAux? nodes first start = some firstIndex →
      nodeIndexAux? nodes second start = some secondIndex →
      firstIndex = secondIndex → first = second := by
  intro nodes
  induction nodes with
  | nil =>
      intro first second firstIndex secondIndex start hfirst _ _
      simp [nodeIndexAux?] at hfirst
  | cons head tail ih =>
      intro first second firstIndex secondIndex start hfirst hsecond equal
      by_cases firstEq : head.locant = first
      · by_cases secondEq : head.locant = second
        · simp only [nodeIndexAux?, firstEq, if_pos] at hfirst
          simp only [nodeIndexAux?, secondEq, if_pos] at hsecond
          have hfirstIndex : firstIndex = start := (Option.some.inj hfirst).symm
          have hsecondIndex : secondIndex = start := (Option.some.inj hsecond).symm
          rw [hfirstIndex, hsecondIndex] at equal
          calc
            first = head.locant := firstEq.symm
            _ = second := secondEq
        · simp only [nodeIndexAux?, firstEq, if_pos] at hfirst
          simp only [nodeIndexAux?, secondEq] at hsecond
          have hfirstIndex : firstIndex = start := (Option.some.inj hfirst).symm
          have hsecondGe : start + 1 ≤ secondIndex :=
            nodeIndexAux?_ge tail second (start + 1) secondIndex hsecond
          rw [hfirstIndex] at equal
          omega
      · by_cases secondEq : head.locant = second
        · simp only [nodeIndexAux?, firstEq] at hfirst
          simp only [nodeIndexAux?, secondEq, if_pos] at hsecond
          have hsecondIndex : secondIndex = start := (Option.some.inj hsecond).symm
          have hfirstGe : start + 1 ≤ firstIndex :=
            nodeIndexAux?_ge tail first (start + 1) firstIndex hfirst
          rw [hsecondIndex] at equal
          omega
        · simp only [nodeIndexAux?, firstEq] at hfirst
          simp only [nodeIndexAux?, secondEq] at hsecond
          exact ih first second firstIndex secondIndex (start + 1) hfirst hsecond equal

theorem nodeIndexAux?_get? :
    ∀ (nodes : List AtomNode) (locant start index : Nat),
      nodeIndexAux? nodes locant start = some index →
        ∃ node, nodes[index - start]? = some node ∧ node.locant = locant := by
  intro nodes
  induction nodes with
  | nil =>
      intro locant start index h
      simp [nodeIndexAux?] at h
  | cons head tail ih =>
      intro locant start index h
      by_cases headEq : head.locant = locant
      · simp only [nodeIndexAux?, headEq, if_pos] at h
        have hindex : index = start := (Option.some.inj h).symm
        refine ⟨head, ?_, headEq⟩
        rw [hindex]
        simp
      · simp only [nodeIndexAux?, headEq] at h
        obtain ⟨node, hget, hloc⟩ := ih locant (start + 1) index h
        have hge : start + 1 ≤ index := nodeIndexAux?_ge tail locant (start + 1) index h
        refine ⟨node, ?_, hloc⟩
        have harith : index - start = (index - (start + 1)) + 1 := by omega
        rw [harith]
        simpa using hget

theorem heavyAtomNodeIndex?_ge (graph : HeavyAtomGraph) {locant index : Nat}
    (h : heavyAtomNodeIndex? graph locant = some index) : 0 ≤ index :=
  nodeIndexAux?_ge graph.nodes locant 0 index h

theorem heavyAtomNodeIndex?_lt_length (graph : HeavyAtomGraph) {locant index : Nat}
    (h : heavyAtomNodeIndex? graph locant = some index) : index < graph.nodes.length := by
  have hlt := nodeIndexAux?_lt_length graph.nodes locant 0 index h
  simpa using hlt

theorem heavyAtomNodeIndex?_locant_unique (graph : HeavyAtomGraph) {first second : Nat}
    {firstIndex secondIndex : Nat}
    (hfirst : heavyAtomNodeIndex? graph first = some firstIndex)
    (hsecond : heavyAtomNodeIndex? graph second = some secondIndex)
    (equal : firstIndex = secondIndex) : first = second :=
  nodeIndexAux?_locant_unique graph.nodes first second firstIndex secondIndex 0
    hfirst hsecond equal

theorem heavyAtomNodeIndex?_get? (graph : HeavyAtomGraph) {locant index : Nat}
    (h : heavyAtomNodeIndex? graph locant = some index) :
    ∃ node, graph.nodes[index]? = some node ∧ node.locant = locant := by
  have hget := nodeIndexAux?_get? graph.nodes locant 0 index h
  simpa using hget

/-- Two source nodes whose printed locants agree are the same node whenever the graph is well
formed.  This is the element-identity tie used by the semantic-atom embedding. -/
theorem AtomNode.eq_of_mem_of_locant_eq {nodes : List AtomNode}
    (nodup : (nodes.map AtomNode.locant).Nodup)
    {first second : AtomNode} (hfirst : first ∈ nodes) (hsecond : second ∈ nodes)
    (locantEq : first.locant = second.locant) : first = second :=
  List.inj_on_of_nodup_map nodup hfirst hsecond locantEq

/-! ## Canonical resolution into `Fin graph.nodes.length` -/

/-- Read a natural index back as a finite atom of the same length, failing out of range. -/
def indexToFin? (n index : Nat) : Option (Fin n) :=
  if h : index < n then some ⟨index, h⟩ else none

theorem indexToFin?_eq_some_iff {n index : Nat} {atom : Fin n} :
    indexToFin? n index = some atom ↔ index < n ∧ atom.val = index := by
  unfold indexToFin?
  by_cases h : index < n
  · rw [dif_pos h]
    constructor
    · intro equal
      have atomEq : (⟨index, h⟩ : Fin n) = atom := Option.some.inj equal
      exact ⟨h, by rw [← atomEq]⟩
    · rintro ⟨_, rfl⟩
      rfl
  · rw [dif_neg h]
    simp [h]

/-- Resolve a printed source locant to a finite atom of the source graph. -/
def canonicalAtomOf (graph : HeavyAtomGraph) (locant : Nat) : Option (Fin graph.nodes.length) :=
  (heavyAtomNodeIndex? graph locant).bind fun index =>
    indexToFin? graph.nodes.length index

theorem canonicalAtomOf_eq_some_iff {graph : HeavyAtomGraph} {locant : Nat}
    {atom : Fin graph.nodes.length} :
    canonicalAtomOf graph locant = some atom ↔
      ∃ index, heavyAtomNodeIndex? graph locant = some index ∧
        index < graph.nodes.length ∧ atom.val = index := by
  unfold canonicalAtomOf
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨index, hindex, hfin⟩
    have hfin' := indexToFin?_eq_some_iff.mp hfin
    exact ⟨index, hindex, hfin'.1, hfin'.2⟩
  · rintro ⟨index, hindex, hlt, hval⟩
    refine ⟨index, hindex, ?_⟩
    exact indexToFin?_eq_some_iff.mpr ⟨hlt, hval⟩

theorem canonicalAtomOf_exists (graph : HeavyAtomGraph) {locant : Nat}
    (hmem : locant ∈ graph.locants) :
    ∃ atom, canonicalAtomOf graph locant = some atom := by
  obtain ⟨index, hindex⟩ := nodeIndexAux?_exists_of_mem graph.nodes locant 0 hmem
  have hlt : index < graph.nodes.length := heavyAtomNodeIndex?_lt_length graph hindex
  refine ⟨⟨index, hlt⟩, ?_⟩
  unfold canonicalAtomOf heavyAtomNodeIndex?
  rw [hindex]
  simp [indexToFin?, hlt]

theorem canonicalAtomOf_injective_on_resolved (graph : HeavyAtomGraph) :
    ∀ {first second : Nat} {atom : Fin graph.nodes.length},
      canonicalAtomOf graph first = some atom →
      canonicalAtomOf graph second = some atom → first = second := by
  intro first second atom hfirst hsecond
  rw [canonicalAtomOf_eq_some_iff] at hfirst hsecond
  obtain ⟨firstIndex, hfirstIndex, _hfirstLt, hfirstVal⟩ := hfirst
  obtain ⟨secondIndex, hsecondIndex, _hsecondLt, hsecondVal⟩ := hsecond
  have hIndex : firstIndex = secondIndex := by omega
  exact heavyAtomNodeIndex?_locant_unique graph hfirstIndex hsecondIndex hIndex

theorem canonicalAtomOf_ne_of_ne (graph : HeavyAtomGraph) {first second : Nat}
    {firstAtom secondAtom : Fin graph.nodes.length}
    (hfirst : canonicalAtomOf graph first = some firstAtom)
    (hsecond : canonicalAtomOf graph second = some secondAtom)
    (hne : first ≠ second) : firstAtom ≠ secondAtom := by
  intro equal
  apply hne
  apply canonicalAtomOf_injective_on_resolved graph hfirst
  rwa [← equal] at hsecond

theorem canonicalAtomOf_node_get? (graph : HeavyAtomGraph) (wellFormed : graph.WellFormed)
    {node : AtomNode} (hmem : node ∈ graph.nodes) {atom : Fin graph.nodes.length}
    (hatom : canonicalAtomOf graph node.locant = some atom) :
    graph.nodes[atom.val]? = some node := by
  rw [canonicalAtomOf_eq_some_iff] at hatom
  obtain ⟨index, hindex, _hlt, hval⟩ := hatom
  obtain ⟨node', hget, hloc⟩ := heavyAtomNodeIndex?_get? graph hindex
  have hnode' : node' ∈ graph.nodes := List.mem_of_getElem? hget
  have hEq : node' = node :=
    AtomNode.eq_of_mem_of_locant_eq wellFormed.1 hnode' hmem hloc
  simpa [hval, hEq] using hget

/-- The canonical ordered interaction of a source bond. -/
def canonicalInteraction? (graph : HeavyAtomGraph) (bond : GraphBond) :
    Option (List (Fin graph.nodes.length) × SemanticInteractionKind) :=
  (canonicalAtomOf graph bond.low).bind fun low =>
    (canonicalAtomOf graph bond.high).bind fun high =>
      some ([low, high], .covalent (bondOrderToNat bond.order))

theorem canonicalInteraction?_spec {graph : HeavyAtomGraph} {bond : GraphBond}
    {edge : List (Fin graph.nodes.length) × SemanticInteractionKind}
    (h : canonicalInteraction? graph bond = some edge) :
    ∃ low high, canonicalAtomOf graph bond.low = some low ∧
      canonicalAtomOf graph bond.high = some high ∧
      edge = ([low, high], .covalent (bondOrderToNat bond.order)) := by
  unfold canonicalInteraction? at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨low, hlow, h⟩ := h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨high, hhigh, hedge⟩ := h
  exact ⟨low, high, hlow, hhigh, (Option.some.inj hedge).symm⟩

/-- All canonical source-bond interactions. -/
def canonicalInteractions (graph : HeavyAtomGraph) :
    List (List (Fin graph.nodes.length) × SemanticInteractionKind) :=
  graph.bonds.filterMap (canonicalInteraction? graph)

theorem bond_endpoints_mem_locants {graph : HeavyAtomGraph} (wellFormed : graph.WellFormed)
    {bond : GraphBond} (hbond : bond ∈ graph.bonds) :
    bond.low ∈ graph.locants ∧ bond.high ∈ graph.locants := by
  have hall := (List.all_eq_true.mp wellFormed.2.2.2) bond hbond
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  exact ⟨hall.1.2, hall.2⟩

theorem canonicalInteractions_arity (graph : HeavyAtomGraph) :
    ∀ edge ∈ canonicalInteractions graph, 2 ≤ edge.1.length := by
  intro edge hedge
  obtain ⟨bond, _hbond, hsome⟩ := List.mem_filterMap.mp hedge
  obtain ⟨low, high, _hlow, _hhigh, rfl⟩ := canonicalInteraction?_spec hsome
  simp

theorem canonicalInteractions_nodup (graph : HeavyAtomGraph) (wellFormed : graph.WellFormed) :
    ∀ edge ∈ canonicalInteractions graph, edge.1.Nodup := by
  intro edge hedge
  obtain ⟨bond, hbond, hsome⟩ := List.mem_filterMap.mp hedge
  obtain ⟨low, high, hlow, hhigh, rfl⟩ := canonicalInteraction?_spec hsome
  have hlt : bond.low < bond.high := by
    have hall := (List.all_eq_true.mp wellFormed.2.2.2) bond hbond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
    exact hall.1.1
  have hne : bond.low ≠ bond.high := by omega
  have hres : low ≠ high := canonicalAtomOf_ne_of_ne graph hlow hhigh hne
  simpa using hres

/-! ## Explicit fieldwise source-graph embedding into the actual core -/

/-- An explicit embedding of the actual source heavy-atom graph into the finite atom labels of
an actual `FiniteAtomInteractionHypergraph` core.

There is no independent "target atom" or "target interaction" field: `atom_exact` states that
the core's own `atomData` at the resolved atom is exactly the source node's
`atomNodeToSemanticAtom?` record, and `bond_exact` states that the actual ordered endpoint
interaction lies in the core's own `interactions`.  In particular, when the core is
`request.graph`, every derived membership theorem is about the actual request. -/
structure SourceGraphEmbedding {V : Type} [DecidableEq V] [Fintype V]
    (graph : HeavyAtomGraph) (core : FiniteAtomInteractionHypergraph V) where
  atomOf : Nat → Option V
  node_resolved : ∀ node ∈ graph.nodes, ∃ atom, atomOf node.locant = some atom
  resolved_injective : ∀ {first second : Nat} {atom : V},
    atomOf first = some atom → atomOf second = some atom → first = second
  atom_exact : ∀ node ∈ graph.nodes, ∀ atom : V, atomOf node.locant = some atom →
    some (core.atomData atom) = atomNodeToSemanticAtom? node
  bond_exact : ∀ bond ∈ graph.bonds, ∃ low high : V,
    atomOf bond.low = some low ∧ atomOf bond.high = some high ∧
      ([low, high], .covalent (bondOrderToNat bond.order)) ∈ core.interactions

/-! ## Fragments carrying the resolved source atoms in source order -/

/-- One ordered binding per source node, in source order, keyed by the printed locant. -/
def sourceBindings {V : Type} [DecidableEq V] [Fintype V] {graph : HeavyAtomGraph}
    {core : FiniteAtomInteractionHypergraph V}
    (embedding : SourceGraphEmbedding graph core) : List (ScopeId × Option V) :=
  graph.nodes.map fun node => (⟨node.locant⟩, embedding.atomOf node.locant)

/-- The finite support of the resolved source atoms. -/
def sourceSupport {V : Type} [DecidableEq V] [Fintype V] {graph : HeavyAtomGraph}
    {core : FiniteAtomInteractionHypergraph V}
    (embedding : SourceGraphEmbedding graph core) : Finset V :=
  (graph.nodes.filterMap fun node => embedding.atomOf node.locant).toFinset

/-- The fragment annotation whose ordered bindings are exactly the source-node resolutions. -/
def sourceFragmentAnnotation {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    (embedding : SourceGraphEmbedding graph core) : FragmentAnnotation V where
  support := sourceSupport embedding
  bindings := sourceBindings embedding
  resolved_mem_support := by
    intro binding hbinding atom hatom
    obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hbinding
    exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨node, hnode, hatom⟩)

@[simp] theorem sourceFragmentAnnotation_support {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    (embedding : SourceGraphEmbedding graph core) :
    (sourceFragmentAnnotation embedding).support = sourceSupport embedding := rfl

@[simp] theorem sourceFragmentAnnotation_bindings {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    (embedding : SourceGraphEmbedding graph core) :
    (sourceFragmentAnnotation embedding).bindings = sourceBindings embedding := rfl

@[simp] theorem sourceFragmentAnnotation_sourceData {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    (embedding : SourceGraphEmbedding graph core) :
    (sourceFragmentAnnotation embedding).sourceData = [] := rfl

/-- Every source node resolution is exactly one of the ordered fragment bindings, with the
printed source locant retained as the scope token. -/
theorem mem_sourceBindings_iff {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    {embedding : SourceGraphEmbedding graph core} {binding : ScopeId × Option V} :
    binding ∈ sourceBindings embedding ↔
      ∃ node ∈ graph.nodes,
        (⟨node.locant⟩, embedding.atomOf node.locant) = binding := by
  simp [sourceBindings]

/-- A source locant present in the actual graph resolves to a target atom. -/
theorem locant_atom {V : Type} [DecidableEq V] [Fintype V] {graph : HeavyAtomGraph}
    {core : FiniteAtomInteractionHypergraph V}
    (embedding : SourceGraphEmbedding graph core) {locant : Nat}
    (hmem : locant ∈ graph.locants) :
    ∃ atom, embedding.atomOf locant = some atom := by
  obtain ⟨node, hnode, hloc⟩ := List.mem_map.mp hmem
  obtain ⟨atom, hatom⟩ := embedding.node_resolved node hnode
  exact ⟨atom, by simpa [hloc] using hatom⟩

/-- A centre locant that occurs in the actual source graph resolves into the fragment support. -/
theorem center_atom_mem_support {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    {embedding : SourceGraphEmbedding graph core} {claim : LocatedSourceCenterLabel}
    (hmem : claim.atomId ∈ graph.locants) :
    ∃ atom, embedding.atomOf claim.atomId = some atom ∧
      atom ∈ (sourceFragmentAnnotation embedding).support := by
  obtain ⟨node, hnode, hloc⟩ := List.mem_map.mp hmem
  obtain ⟨atom, hatom⟩ := embedding.node_resolved node hnode
  have hatom' : embedding.atomOf claim.atomId = some atom := by
    simpa [hloc] using hatom
  refine ⟨atom, hatom', ?_⟩
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨node, hnode, hatom⟩)

/-- A source node's target semantic atom is exactly its actual source element record. -/
theorem source_atom_target_exact {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    {embedding : SourceGraphEmbedding graph core} {node : AtomNode}
    (hnode : node ∈ graph.nodes) {atom : V}
    (hatom : embedding.atomOf node.locant = some atom) :
    some (core.atomData atom) = atomNodeToSemanticAtom? node :=
  embedding.atom_exact node hnode atom hatom

/-- A source bond's target interaction has the actual ordered endpoints and bond order. -/
theorem source_bond_target_exact {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    {embedding : SourceGraphEmbedding graph core} {bond : GraphBond}
    (hbond : bond ∈ graph.bonds) :
    ∃ low high : V,
      embedding.atomOf bond.low = some low ∧
      embedding.atomOf bond.high = some high ∧
      ([low, high], .covalent (bondOrderToNat bond.order)) ∈ core.interactions :=
  embedding.bond_exact bond hbond

/-- A retained double-bond configuration claim accepted by the actual source graph yields the
actual ordered endpoint interaction `[source, target]` with bond order two. -/
theorem doubleBond_ordered_interaction {V : Type} [DecidableEq V] [Fintype V]
    {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}
    {embedding : SourceGraphEmbedding graph core} {claims : List DoubleBondConfigurationClaim}
    (hclaims : DoubleBondConfigurationClaimsWellFormed graph claims)
    {claim : DoubleBondConfigurationClaim} (hclaim : claim ∈ claims) :
    ∃ source target : V,
      embedding.atomOf claim.low = some source ∧
      embedding.atomOf claim.high = some target ∧
      ([source, target], .covalent 2) ∈ core.interactions := by
  have hcontains : (doubleBondEdges graph).contains (claim.low, claim.high) = true :=
    (List.all_eq_true.mp hclaims) claim hclaim
  have hmemEdges : (claim.low, claim.high) ∈ doubleBondEdges graph :=
    List.contains_iff_mem.mp hcontains
  obtain ⟨bond, hbondFilter, hedge⟩ := List.mem_map.mp hmemEdges
  have hbondMem : bond ∈ graph.bonds := (List.mem_filter.mp hbondFilter).1
  have hdouble : (bond.order == .double) = true := (List.mem_filter.mp hbondFilter).2
  have horder : bond.order = .double := beq_iff_eq.mp hdouble
  have hedge' : bond.low = claim.low ∧ bond.high = claim.high := by
    simpa [GraphBond.edge] using Prod.mk.inj hedge
  obtain ⟨source, target, hsource, htarget, hinter⟩ := embedding.bond_exact bond hbondMem
  refine ⟨source, target, ?_, ?_, ?_⟩
  · simpa [hedge'.1] using hsource
  · simpa [hedge'.2] using htarget
  · simpa [horder, bondOrderToNat] using hinter

/-! ## The annotation bundle, its source data, and payload recovery -/

/-- A natural-product annotation bundle for the actual request core `core`.

The graph, the exact centre-label list, the exact configuration-claim list, the explicit
source embedding into `core`, and the source-data attachment are stored simultaneously. -/
structure NaturalProductAnnotation {V : Type} [DecidableEq V] [Fintype V]
    (graph : HeavyAtomGraph) (core : FiniteAtomInteractionHypergraph V) where
  graphWellFormed : graph.WellFormed
  embedding : SourceGraphEmbedding graph core
  centers : List LocatedSourceCenterLabel
  doubleBonds : List DoubleBondConfigurationClaim
  centerLocants : ∀ claim ∈ centers, claim.atomId ∈ graph.locants
  doubleBondClaims : DoubleBondConfigurationClaimsWellFormed graph doubleBonds

namespace NaturalProductAnnotation

variable {V : Type} [DecidableEq V] [Fintype V]
variable {graph : HeavyAtomGraph} {core : FiniteAtomInteractionHypergraph V}

/-- The fragment annotation induced by the explicit source embedding. -/
def annotation (data : NaturalProductAnnotation graph core) : FragmentAnnotation V :=
  sourceFragmentAnnotation data.embedding

/-- Resolve a locant present in the source graph through the explicit embedding. -/
noncomputable def resolvedAtom (data : NaturalProductAnnotation graph core) (locant : Nat)
    (hmem : locant ∈ graph.locants) : V :=
  (locant_atom data.embedding hmem).choose

theorem resolvedAtom_spec (data : NaturalProductAnnotation graph core) (locant : Nat)
    (hmem : locant ∈ graph.locants) :
    data.embedding.atomOf locant = some (data.resolvedAtom locant hmem) :=
  (locant_atom data.embedding hmem).choose_spec

theorem resolvedAtom_mem_support (data : NaturalProductAnnotation graph core) (locant : Nat)
    (hmem : locant ∈ graph.locants) :
    data.resolvedAtom locant hmem ∈ data.annotation.support := by
  obtain ⟨node, hnode, hloc⟩ := List.mem_map.mp hmem
  obtain ⟨atom, hatom⟩ := data.embedding.node_resolved node hnode
  have hatom' : data.embedding.atomOf locant = some atom := by
    simpa [hloc] using hatom
  have hEq : atom = data.resolvedAtom locant hmem := by
    have hsome : some atom = some (data.resolvedAtom locant hmem) := by
      rw [← hatom', data.resolvedAtom_spec locant hmem]
    exact Option.some.inj hsome
  rw [← hEq]
  exact List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨node, hnode, hatom⟩)

/-- The resolved centre anchor of one exact supplied centre label. -/
noncomputable def centerAnchor (data : NaturalProductAnnotation graph core)
    (claim : {claim : LocatedSourceCenterLabel // claim ∈ data.centers}) : V :=
  data.resolvedAtom claim.1.atomId (data.centerLocants claim.1 claim.2)

theorem centerAnchor_spec (data : NaturalProductAnnotation graph core)
    (claim : {claim : LocatedSourceCenterLabel // claim ∈ data.centers}) :
    data.embedding.atomOf claim.1.atomId = some (data.centerAnchor claim) :=
  data.resolvedAtom_spec claim.1.atomId (data.centerLocants claim.1 claim.2)

theorem centerAnchor_mem_support (data : NaturalProductAnnotation graph core)
    (claim : {claim : LocatedSourceCenterLabel // claim ∈ data.centers}) :
    data.centerAnchor claim ∈ data.annotation.support :=
  data.resolvedAtom_mem_support claim.1.atomId (data.centerLocants claim.1 claim.2)

/-- The actual centre payloads in supplied order, anchored at the resolved atoms. -/
noncomputable def centerData (data : NaturalProductAnnotation graph core) :
    List (FragmentSourceDatum V) :=
  data.centers.attach.map fun claim =>
    .naturalCenter (data.centerAnchor claim) claim.1

/-- Both original locants of a retained double-bond claim are actual graph locants. -/
theorem doubleBondEndpointLocants (data : NaturalProductAnnotation graph core)
    (claim : {claim : DoubleBondConfigurationClaim // claim ∈ data.doubleBonds}) :
    claim.1.low ∈ graph.locants ∧ claim.1.high ∈ graph.locants := by
  have hcontains : (doubleBondEdges graph).contains (claim.1.low, claim.1.high) = true :=
    (List.all_eq_true.mp data.doubleBondClaims) claim.1 claim.2
  have hmemEdges : (claim.1.low, claim.1.high) ∈ doubleBondEdges graph :=
    List.contains_iff_mem.mp hcontains
  obtain ⟨bond, hbondFilter, hedge⟩ := List.mem_map.mp hmemEdges
  have hbondMem : bond ∈ graph.bonds := (List.mem_filter.mp hbondFilter).1
  have hloc := bond_endpoints_mem_locants data.graphWellFormed hbondMem
  have hedge' : bond.low = claim.1.low ∧ bond.high = claim.1.high := by
    simpa [GraphBond.edge] using Prod.mk.inj hedge
  exact ⟨by simpa [hedge'.1] using hloc.1, by simpa [hedge'.2] using hloc.2⟩

/-- The resolved ordered source anchor of one retained double-bond claim. -/
noncomputable def doubleBondSource (data : NaturalProductAnnotation graph core)
    (claim : {claim : DoubleBondConfigurationClaim // claim ∈ data.doubleBonds}) : V :=
  data.resolvedAtom claim.1.low (data.doubleBondEndpointLocants claim).1

/-- The resolved ordered target anchor of one retained double-bond claim. -/
noncomputable def doubleBondTarget (data : NaturalProductAnnotation graph core)
    (claim : {claim : DoubleBondConfigurationClaim // claim ∈ data.doubleBonds}) : V :=
  data.resolvedAtom claim.1.high (data.doubleBondEndpointLocants claim).2

theorem doubleBondSource_spec (data : NaturalProductAnnotation graph core)
    (claim : {claim : DoubleBondConfigurationClaim // claim ∈ data.doubleBonds}) :
    data.embedding.atomOf claim.1.low = some (data.doubleBondSource claim) :=
  data.resolvedAtom_spec claim.1.low (data.doubleBondEndpointLocants claim).1

theorem doubleBondTarget_spec (data : NaturalProductAnnotation graph core)
    (claim : {claim : DoubleBondConfigurationClaim // claim ∈ data.doubleBonds}) :
    data.embedding.atomOf claim.1.high = some (data.doubleBondTarget claim) :=
  data.resolvedAtom_spec claim.1.high (data.doubleBondEndpointLocants claim).2

theorem doubleBondSource_mem_support (data : NaturalProductAnnotation graph core)
    (claim : {claim : DoubleBondConfigurationClaim // claim ∈ data.doubleBonds}) :
    data.doubleBondSource claim ∈ data.annotation.support :=
  data.resolvedAtom_mem_support claim.1.low (data.doubleBondEndpointLocants claim).1

theorem doubleBondTarget_mem_support (data : NaturalProductAnnotation graph core)
    (claim : {claim : DoubleBondConfigurationClaim // claim ∈ data.doubleBonds}) :
    data.doubleBondTarget claim ∈ data.annotation.support :=
  data.resolvedAtom_mem_support claim.1.high (data.doubleBondEndpointLocants claim).2

/-- The actual double-bond payloads in supplied order, with ordered source/target anchors. -/
noncomputable def doubleBondData (data : NaturalProductAnnotation graph core) :
    List (FragmentSourceDatum V) :=
  data.doubleBonds.attach.map fun claim =>
    .naturalDoubleBond (data.doubleBondSource claim) (data.doubleBondTarget claim) claim.1

/-- The source data attached to the fragment: exact supplied centre labels followed by exact
supplied double-bond claims, both in supplied order. -/
noncomputable def sourceData (data : NaturalProductAnnotation graph core) :
    List (FragmentSourceDatum V) :=
  data.centerData ++ data.doubleBondData

theorem sourceData_supported (data : NaturalProductAnnotation graph core) :
    ∀ datum ∈ data.sourceData,
      ∀ atom ∈ datum.atomReferences, atom ∈ data.annotation.support := by
  intro datum hdatum atom hatom
  rw [sourceData, List.mem_append] at hdatum
  rcases hdatum with hcenter | hdouble
  · obtain ⟨claim, _hclaim, hdatumEq⟩ := List.mem_map.mp hcenter
    rw [← hdatumEq] at hatom
    simp only [FragmentSourceDatum.atomReferences_naturalCenter,
      List.mem_singleton] at hatom
    rw [hatom]
    exact data.centerAnchor_mem_support claim
  · obtain ⟨claim, _hclaim, hdatumEq⟩ := List.mem_map.mp hdouble
    rw [← hdatumEq] at hatom
    simp only [FragmentSourceDatum.atomReferences_naturalDoubleBond, List.mem_cons,
      List.not_mem_nil, or_false] at hatom
    rcases hatom with hsource | htarget
    · rw [hsource]
      exact data.doubleBondSource_mem_support claim
    · rw [htarget]
      exact data.doubleBondTarget_mem_support claim

/-- The induced fragment with the actual source data attached. -/
noncomputable def annotatedFragment (data : NaturalProductAnnotation graph core) :
    FragmentAnnotation V :=
  data.annotation.withSourceData data.sourceData data.sourceData_supported

@[simp] theorem annotatedFragment_support (data : NaturalProductAnnotation graph core) :
    data.annotatedFragment.support = data.annotation.support := by
  simp [annotatedFragment]

@[simp] theorem annotatedFragment_bindings (data : NaturalProductAnnotation graph core) :
    data.annotatedFragment.bindings = data.annotation.bindings := by
  simp [annotatedFragment]

@[simp] theorem annotatedFragment_sourceData (data : NaturalProductAnnotation graph core) :
    data.annotatedFragment.sourceData = data.sourceData := by
  simp [annotatedFragment, annotation, sourceFragmentAnnotation]

/-- The centre payload list, read back from the attached source data, is exactly the supplied
centre-label list. -/
theorem centerData_naturalCenterLabel? (data : NaturalProductAnnotation graph core) :
    data.centerData.filterMap naturalCenterLabel? = data.centers := by
  unfold centerData
  rw [List.filterMap_map]
  simp only [Function.comp_def, naturalCenterLabel?_naturalCenter]
  have hfun : (fun claim : {x // x ∈ data.centers} => some claim.1) =
      (some ∘ Subtype.val) := rfl
  rw [hfun, List.filterMap_eq_map, List.attach_map_subtype_val]

/-- The double-bond payload list, read back from the attached source data, is exactly the
supplied configuration-claim list. -/
theorem doubleBondData_naturalDoubleBondClaim? (data : NaturalProductAnnotation graph core) :
    data.doubleBondData.filterMap naturalDoubleBondClaim? =
      data.doubleBonds := by
  unfold doubleBondData
  rw [List.filterMap_map]
  simp only [Function.comp_def, naturalDoubleBondClaim?_naturalDoubleBond]
  have hfun : (fun claim : {x // x ∈ data.doubleBonds} => some claim.1) =
      (some ∘ Subtype.val) := rfl
  rw [hfun, List.filterMap_eq_map, List.attach_map_subtype_val]

theorem annotatedFragment_center_labels (data : NaturalProductAnnotation graph core) :
    data.annotatedFragment.sourceData.filterMap naturalCenterLabel? =
      data.centers := by
  rw [annotatedFragment_sourceData, sourceData, List.filterMap_append,
    centerData_naturalCenterLabel?]
  have hnone : data.doubleBondData.filterMap naturalCenterLabel? = [] := by
    unfold doubleBondData
    rw [List.filterMap_map]
    simp [naturalCenterLabel?]
  rw [hnone, List.append_nil]

theorem annotatedFragment_doubleBond_claims (data : NaturalProductAnnotation graph core) :
    data.annotatedFragment.sourceData.filterMap
      naturalDoubleBondClaim? = data.doubleBonds := by
  rw [annotatedFragment_sourceData, sourceData, List.filterMap_append,
    doubleBondData_naturalDoubleBondClaim?]
  have hnone : data.centerData.filterMap naturalDoubleBondClaim? = [] := by
    unfold centerData
    rw [List.filterMap_map]
    simp [naturalDoubleBondClaim?]
  rw [hnone, List.nil_append]

/-- Every retained centre resolves to an atom in the induced fragment support. -/
theorem center_mem_support (data : NaturalProductAnnotation graph core)
    {claim : LocatedSourceCenterLabel} (hclaim : claim ∈ data.centers) :
    ∃ atom, data.embedding.atomOf claim.atomId = some atom ∧
      atom ∈ data.annotation.support :=
  center_atom_mem_support (data.centerLocants claim hclaim)

/-- The exact source node and actual core semantic atom attached to a retained centre. -/
theorem center_source_atom_exact (data : NaturalProductAnnotation graph core)
    {claim : LocatedSourceCenterLabel} (hclaim : claim ∈ data.centers) :
    ∃ node atom,
      node ∈ graph.nodes ∧ node.locant = claim.atomId ∧
      data.embedding.atomOf claim.atomId = some atom ∧
      some (core.atomData atom) = atomNodeToSemanticAtom? node := by
  obtain ⟨node, hnode, hloc⟩ := List.mem_map.mp (data.centerLocants claim hclaim)
  obtain ⟨atom, hatom⟩ := data.embedding.node_resolved node hnode
  have hatom' : data.embedding.atomOf claim.atomId = some atom := by
    simpa [hloc] using hatom
  exact ⟨node, atom, hnode, hloc, hatom',
    data.embedding.atom_exact node hnode atom hatom⟩

/-- Every retained double-bond claim produces the actual ordered endpoint interaction in the
actual core. -/
theorem doubleBonds_orderedInteraction (data : NaturalProductAnnotation graph core)
    {claim : DoubleBondConfigurationClaim} (hclaim : claim ∈ data.doubleBonds) :
    ∃ source target : V,
      data.embedding.atomOf claim.low = some source ∧
      data.embedding.atomOf claim.high = some target ∧
      ([source, target], .covalent 2) ∈ core.interactions :=
  doubleBond_ordered_interaction data.doubleBondClaims hclaim

/-- Simultaneous package: exact centre support, exact ordered bond interactions, and the exact
source graph and ordered source lists all retained together. -/
theorem source_correspondence (data : NaturalProductAnnotation graph core) :
    (∀ claim ∈ data.centers,
        ∃ atom, data.embedding.atomOf claim.atomId = some atom ∧
          atom ∈ data.annotation.support) ∧
      (∀ claim ∈ data.doubleBonds,
        ∃ source target : V,
          data.embedding.atomOf claim.low = some source ∧
          data.embedding.atomOf claim.high = some target ∧
          ([source, target], .covalent 2) ∈ core.interactions) ∧
      (data.annotatedFragment.sourceData.filterMap
          naturalCenterLabel? = data.centers) ∧
      (data.annotatedFragment.sourceData.filterMap
          naturalDoubleBondClaim? = data.doubleBonds) ∧
      (data.annotatedFragment.bindings = data.annotation.bindings) :=
  ⟨fun _claim hclaim => data.center_mem_support hclaim,
   fun _claim hclaim => data.doubleBonds_orderedInteraction hclaim,
   data.annotatedFragment_center_labels,
   data.annotatedFragment_doubleBond_claims,
   data.annotatedFragment_bindings⟩

end NaturalProductAnnotation

/-! ## Membership exactness for the actual converter's `mapM`

These use the shared bridge's index-exactness theorem rather than restating the generic
`List.mapM` induction. -/

theorem forall_mem_mapM_some {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') {x : α} (hx : x ∈ l) :
    ∃ y, f x = some y ∧ y ∈ l' := by
  obtain ⟨index, rfl⟩ := List.get_of_mem hx
  have indexed := OptionMapM.list_mapM_option_listGet? (f := f)
    (source := l) (target := l') h index.val
  have sourceLookup : listGet? l index.val = some (l.get index) :=
    listGet?_eq_some_get l index
  have chained : listGet? l' index.val = f (l.get index) := by
    simpa [sourceLookup] using indexed
  have hlen : l'.length = l.length :=
    OptionMapM.list_mapM_option_length (f := f) (source := l) (target := l') h
  cases observed : f (l.get index) with
  | none =>
      obtain ⟨value, hvalue⟩ :=
        listGet?_exists_of_lt l' index.val (by rw [hlen]; exact index.isLt)
      rw [chained, observed] at hvalue
      simp at hvalue
  | some value =>
      have chainedSome : listGet? l' index.val = some value := by
        rw [chained, observed]
      exact ⟨value, rfl,
        listGet?_eq_some_implies_mem l' index.val value chainedSome⟩

theorem mem_of_mapM_some {α β : Type} {f : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM f = some l') {x : α} (hx : x ∈ l) {y : β} (hxy : f x = some y) :
    y ∈ l' := by
  obtain ⟨y', hy', hy'mem⟩ := forall_mem_mapM_some h hx
  have hyEq : y' = y := Option.some.inj (hy'.symm.trans hxy)
  rwa [hyEq] at hy'mem

/-! ## Actual authoritative-conversion binding -/

/-- An actual successful heavy-atom-graph-to-authoritative-input conversion.

`conversion` is the real result of
`Retinoid1981.FigureAuthorityInput.heavyAtomGraphToAuthoritativeChemicalInput?`.  The count
equalities below are *derived*; they are never a hypothesis replacing the structural tie. -/
structure AuthoritativeConversionBinding (graph : HeavyAtomGraph) where
  input : AuthoritativeChemicalInput
  conversion : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input

namespace AuthoritativeConversionBinding

variable {graph : HeavyAtomGraph}

/-- Build the binding from actual converter success. -/
def ofIsSome (graph : HeavyAtomGraph)
    (h : (heavyAtomGraphToAuthoritativeChemicalInput? graph).isSome = true) :
    AuthoritativeConversionBinding graph := by
  let h' : (heavyAtomGraphToAuthoritativeChemicalInput? graph).isSome = true := by
    simpa using h
  exact
    { input := (heavyAtomGraphToAuthoritativeChemicalInput? graph).get h'
      conversion := Option.eq_some_of_isSome h' }

/-- The actual converter's atom computation succeeds, and its list is exactly the input atom
list.  This is fieldwise exactness, not a length equality. -/
theorem atoms_exact (binding : AuthoritativeConversionBinding graph) :
    ∃ atoms, graph.nodes.mapM atomNodeToSemanticAtom? = some atoms ∧
      binding.input.molecule.atoms = atoms := by
  rcases binding with ⟨input, conversion⟩
  exact heavyAtomGraphToAuthoritativeChemicalInput?_atoms_eq_mapM graph input conversion

/-- The actual converter's interaction computation succeeds, and its list is exactly the input
interaction list. -/
theorem interactions_exact (binding : AuthoritativeConversionBinding graph) :
    ∃ interactions,
      graph.bonds.mapM (graphBondToSemanticInteraction? graph) = some interactions ∧
        binding.input.molecule.interactions = interactions := by
  rcases binding with ⟨input, conversion⟩
  exact heavyAtomGraphToAuthoritativeChemicalInput?_interactions_eq_mapM graph input conversion

/-- Every source node has the actual semantic atom, placed at its actual converter position. -/
theorem atomOfNode (binding : AuthoritativeConversionBinding graph)
    {node : AtomNode} (hnode : node ∈ graph.nodes) :
    ∃ atom, atomNodeToSemanticAtom? node = some atom ∧
      atom ∈ binding.input.molecule.atoms := by
  obtain ⟨atoms, hmap, hEq⟩ := binding.atoms_exact
  obtain ⟨atom, hatom, _⟩ := forall_mem_mapM_some hmap (x := node) hnode
  refine ⟨atom, hatom, ?_⟩
  rw [hEq]
  exact mem_of_mapM_some hmap hnode hatom

/-- Every source bond has the actual ordered endpoint interaction, with the exact participant
order `[low, high]` and the actual bond order. -/
theorem ordered_endpoints (binding : AuthoritativeConversionBinding graph)
    {bond : GraphBond} (hbond : bond ∈ graph.bonds) :
    ∃ low high interaction,
      heavyAtomNodeIndex? graph bond.low = some low ∧
      heavyAtomNodeIndex? graph bond.high = some high ∧
      graphBondToSemanticInteraction? graph bond = some interaction ∧
      interaction ∈ binding.input.molecule.interactions ∧
      interaction.participants = [low, high] ∧
      interaction.kind = .covalent (bondOrderToNat bond.order) := by
  obtain ⟨interactions, hmap, hEq⟩ := binding.interactions_exact
  obtain ⟨interaction, hsome, hinter⟩ := forall_mem_mapM_some hmap (x := bond) hbond
  have hinterInput : interaction ∈ binding.input.molecule.interactions := by
    rw [hEq]
    exact hinter
  obtain ⟨low, high, hlow, hhigh, hparticipants, hkind⟩ :=
    graphBondToSemanticInteraction?_exact graph bond interaction hsome
  exact ⟨low, high, interaction, hlow, hhigh, hsome, hinterInput, hparticipants, hkind⟩

/-- The derived atom-count equality. -/
theorem atom_count_exact (binding : AuthoritativeConversionBinding graph) :
    binding.input.molecule.atoms.length = graph.nodes.length := by
  rcases binding with ⟨input, conversion⟩
  exact heavyAtomGraphToAuthoritativeChemicalInput?_atoms_length graph input conversion

/-- The derived interaction-count equality. -/
theorem interaction_count_exact (binding : AuthoritativeConversionBinding graph) :
    binding.input.molecule.interactions.length = graph.bonds.length := by
  rcases binding with ⟨input, conversion⟩
  exact heavyAtomGraphToAuthoritativeChemicalInput?_interactionCount graph input conversion

/-- A semantic atom for one source node, chosen from the actual conversion's success. -/
noncomputable def semanticAtomOfNode (binding : AuthoritativeConversionBinding graph)
    (node : AtomNode) (hnode : node ∈ graph.nodes) : SemanticAtom :=
  (binding.atomOfNode hnode).choose

theorem semanticAtomOfNode_spec (binding : AuthoritativeConversionBinding graph)
    (node : AtomNode) (hnode : node ∈ graph.nodes) :
    atomNodeToSemanticAtom? node = some (binding.semanticAtomOfNode node hnode) :=
  (binding.atomOfNode hnode).choose_spec.1

/-- The actual converted semantic atom at a canonical source position. -/
noncomputable def canonicalAtomData (binding : AuthoritativeConversionBinding graph)
    (index : Fin graph.nodes.length) : SemanticAtom :=
  binding.semanticAtomOfNode (graph.nodes.get index) (List.get_mem graph.nodes index)

/-- The canonical core induced by the actual conversion: every atom is the actual converted
semantic atom at that source position, and every interaction is the ordered image of an actual
source bond. -/
noncomputable def canonicalCoreOfBinding (binding : AuthoritativeConversionBinding graph)
    (wellFormed : graph.WellFormed) :
    FiniteAtomInteractionHypergraph (Fin graph.nodes.length) where
  atomData := binding.canonicalAtomData
  interactions := canonicalInteractions graph
  arity_ge_two := canonicalInteractions_arity graph
  participants_nodup := canonicalInteractions_nodup graph wellFormed

/-- The explicit source embedding into the conversion-derived canonical core. -/
noncomputable def canonicalEmbeddingOfBinding (binding : AuthoritativeConversionBinding graph)
    (wellFormed : graph.WellFormed) :
    SourceGraphEmbedding graph (binding.canonicalCoreOfBinding wellFormed) where
  atomOf := canonicalAtomOf graph
  node_resolved := by
    intro node hnode
    have hmem : node.locant ∈ graph.locants :=
      List.mem_map.mpr ⟨node, hnode, rfl⟩
    obtain ⟨atom, hatom⟩ := canonicalAtomOf_exists graph hmem
    exact ⟨atom, hatom⟩
  resolved_injective := by
    intro first second atom hfirst hsecond
    exact canonicalAtomOf_injective_on_resolved graph hfirst hsecond
  atom_exact := by
    intro node hnode atom hatom
    have hget := canonicalAtomOf_node_get? graph wellFormed hnode hatom
    rw [List.getElem?_eq_some_iff] at hget
    obtain ⟨_hbound, hgetEq⟩ := hget
    have hnodeGet : graph.nodes.get atom = node := by simpa using hgetEq
    have hspec := binding.semanticAtomOfNode_spec (graph.nodes.get atom)
      (List.get_mem graph.nodes atom)
    show some ((binding.canonicalCoreOfBinding wellFormed).atomData atom) =
      atomNodeToSemanticAtom? node
    rw [← hnodeGet, hspec]
    rfl
  bond_exact := by
    intro bond hbond
    obtain ⟨hlowMem, hhighMem⟩ := bond_endpoints_mem_locants wellFormed hbond
    obtain ⟨low, hlow⟩ := canonicalAtomOf_exists graph hlowMem
    obtain ⟨high, hhigh⟩ := canonicalAtomOf_exists graph hhighMem
    refine ⟨low, high, hlow, hhigh, ?_⟩
    change ([low, high], .covalent (bondOrderToNat bond.order)) ∈ canonicalInteractions graph
    exact List.mem_filterMap.mpr ⟨bond, hbond, by
      simp [canonicalInteraction?, hlow, hhigh]⟩

/-- Simultaneous exact atom support, exact ordered interactions, and the derived counts. -/
theorem conversion_package (binding : AuthoritativeConversionBinding graph) :
    (∀ node ∈ graph.nodes,
      ∃ atom, atomNodeToSemanticAtom? node = some atom ∧
        atom ∈ binding.input.molecule.atoms) ∧
      (∀ bond ∈ graph.bonds,
        ∃ low high interaction,
          heavyAtomNodeIndex? graph bond.low = some low ∧
          heavyAtomNodeIndex? graph bond.high = some high ∧
          graphBondToSemanticInteraction? graph bond = some interaction ∧
          interaction ∈ binding.input.molecule.interactions ∧
          interaction.participants = [low, high] ∧
          interaction.kind = .covalent (bondOrderToNat bond.order)) ∧
      binding.input.molecule.atoms.length = graph.nodes.length ∧
      binding.input.molecule.interactions.length = graph.bonds.length :=
  ⟨fun _node hnode => binding.atomOfNode hnode,
   fun _bond hbond => binding.ordered_endpoints hbond,
   binding.atom_count_exact,
   binding.interaction_count_exact⟩

end AuthoritativeConversionBinding

/-! ## Concrete Ret-1981 annotations -/

variable {graph : HeavyAtomGraph}

/-- Convert an actual checked `all` predicate over centre locants into the annotation field. -/
theorem centerLocants_of_all {graph : HeavyAtomGraph} {centers : List LocatedSourceCenterLabel}
    (h : centers.all (fun claim => graph.locants.contains claim.atomId) = true) :
    ∀ claim ∈ centers, claim.atomId ∈ graph.locants := by
  intro claim hclaim
  have hcontains : graph.locants.contains claim.atomId = true :=
    (List.all_eq_true.mp h) claim hclaim
  exact List.contains_iff_mem.mp hcontains

/-- Build an annotation for the actual conversion-derived canonical core of `graph`. -/
noncomputable def annotationOfBinding (binding : AuthoritativeConversionBinding graph)
    (wellFormed : graph.WellFormed)
    (centers : List LocatedSourceCenterLabel)
    (doubleBonds : List DoubleBondConfigurationClaim)
    (centerLocants : ∀ claim ∈ centers, claim.atomId ∈ graph.locants)
    (doubleBondClaims : DoubleBondConfigurationClaimsWellFormed graph doubleBonds) :
    NaturalProductAnnotation graph (binding.canonicalCoreOfBinding wellFormed) where
  graphWellFormed := wellFormed
  embedding := binding.canonicalEmbeddingOfBinding wellFormed
  centers := centers
  doubleBonds := doubleBonds
  centerLocants := centerLocants
  doubleBondClaims := doubleBondClaims

theorem hydroxyRetinolGraph_wellFormed : hydroxyRetinolGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

theorem acetoxyRetinolGraph_wellFormed : acetoxyRetinolGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

theorem lysylIminomethylGraph_wellFormed : lysylIminomethylGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

theorem retinoylGlucuronideGraph_wellFormed : retinoylGlucuronideGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

theorem fluororetinoateGraph_wellFormed : fluororetinoateGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

theorem cisRetinolGraph_wellFormed : cisRetinolGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

theorem cisRetinoicAcidGraph_wellFormed : cisRetinoicAcidGraph.WellFormed := by
  rw [← HeavyAtomGraph.wellFormed?_eq_true_iff]
  decide

def hydroxyRetinolConversion : AuthoritativeConversionBinding hydroxyRetinolGraph :=
  AuthoritativeConversionBinding.ofIsSome hydroxyRetinolGraph (by decide)

def acetoxyRetinolConversion : AuthoritativeConversionBinding acetoxyRetinolGraph :=
  AuthoritativeConversionBinding.ofIsSome acetoxyRetinolGraph (by decide)

def retinylideneLLysineConversion :
    AuthoritativeConversionBinding lysylIminomethylGraph :=
  AuthoritativeConversionBinding.ofIsSome lysylIminomethylGraph (by decide)

def retinoylBetaDGlucopyranuronateConversion :
    AuthoritativeConversionBinding retinoylGlucuronideGraph :=
  AuthoritativeConversionBinding.ofIsSome retinoylGlucuronideGraph (by decide)

def fluororetinoateConversion : AuthoritativeConversionBinding fluororetinoateGraph :=
  AuthoritativeConversionBinding.ofIsSome fluororetinoateGraph (by decide)

def cisRetinolConversion : AuthoritativeConversionBinding cisRetinolGraph :=
  AuthoritativeConversionBinding.ofIsSome cisRetinolGraph (by decide)

def cisRetinoicAcidConversion : AuthoritativeConversionBinding cisRetinoicAcidGraph :=
  AuthoritativeConversionBinding.ofIsSome cisRetinoicAcidGraph (by decide)

/-- A51 (3R)-3-hydroxyretinol with the source R/S label retained. -/
noncomputable def hydroxyRetinolAnnotation :
    NaturalProductAnnotation hydroxyRetinolGraph
      (hydroxyRetinolConversion.canonicalCoreOfBinding hydroxyRetinolGraph_wellFormed) :=
  annotationOfBinding hydroxyRetinolConversion hydroxyRetinolGraph_wellFormed
    (ExplicitCenterLabelCatalog.claimsFor .hydroxyRetinol3R)
    []
    (centerLocants_of_all (by decide))
    (by unfold DoubleBondConfigurationClaimsWellFormed; decide)

/-- A51 (3R)-3-acetoxyretinol with the source R/S label retained. -/
noncomputable def acetoxyRetinolAnnotation :
    NaturalProductAnnotation acetoxyRetinolGraph
      (acetoxyRetinolConversion.canonicalCoreOfBinding acetoxyRetinolGraph_wellFormed) :=
  annotationOfBinding acetoxyRetinolConversion acetoxyRetinolGraph_wellFormed
    (ExplicitCenterLabelCatalog.claimsFor .acetoxyRetinol3R)
    []
    (centerLocants_of_all (by decide))
    (by unfold DoubleBondConfigurationClaimsWellFormed; decide)

/-- Structure (8): N6-retinylidene-L-lysine, retaining the amino-acid L series label. -/
noncomputable def retinylideneLLysineAnnotation :
    NaturalProductAnnotation lysylIminomethylGraph
      (retinylideneLLysineConversion.canonicalCoreOfBinding lysylIminomethylGraph_wellFormed) :=
  annotationOfBinding retinylideneLLysineConversion lysylIminomethylGraph_wellFormed
    (ExplicitCenterLabelCatalog.claimsFor .retinylideneLLysine)
    []
    (centerLocants_of_all (by decide))
    (by unfold DoubleBondConfigurationClaimsWellFormed; decide)

/-- Structure (10): 1-O-retinoyl-beta-D-glucopyranuronic acid.  The `beta` anomer label and the
`D` carbohydrate-series label remain two distinct `SourceCenterLabel` constructors. -/
noncomputable def retinoylBetaDGlucopyranuronateAnnotation :
    NaturalProductAnnotation retinoylGlucuronideGraph
      (retinoylBetaDGlucopyranuronateConversion.canonicalCoreOfBinding
        retinoylGlucuronideGraph_wellFormed) :=
  annotationOfBinding retinoylBetaDGlucopyranuronateConversion
    retinoylGlucuronideGraph_wellFormed
    (ExplicitCenterLabelCatalog.claimsFor .retinoylBetaDGlucopyranuronate)
    []
    (centerLocants_of_all (by decide))
    (by unfold DoubleBondConfigurationClaimsWellFormed; decide)

/-- A44b ethyl 12-fluororetinoate with the four actual parent-geometry/E-Z claims. -/
noncomputable def fluororetinoateAnnotation :
    NaturalProductAnnotation fluororetinoateGraph
      (fluororetinoateConversion.canonicalCoreOfBinding fluororetinoateGraph_wellFormed) :=
  annotationOfBinding fluororetinoateConversion fluororetinoateGraph_wellFormed
    []
    fluororetinoateConfigurationClaims
    (centerLocants_of_all (by decide))
    (by unfold DoubleBondConfigurationClaimsWellFormed; decide)

/-- A52a 13-cis-retinol with the actual cis-retinoid claims. -/
noncomputable def cisRetinolAnnotation :
    NaturalProductAnnotation cisRetinolGraph
      (cisRetinolConversion.canonicalCoreOfBinding cisRetinolGraph_wellFormed) :=
  annotationOfBinding cisRetinolConversion cisRetinolGraph_wellFormed
    []
    cisRetinoidConfigurationClaims
    (centerLocants_of_all (by decide))
    (by unfold DoubleBondConfigurationClaimsWellFormed; decide)

/-- A52a 13-cis-retinoic acid with the actual cis-retinoid claims. -/
noncomputable def cisRetinoicAcidAnnotation :
    NaturalProductAnnotation cisRetinoicAcidGraph
      (cisRetinoicAcidConversion.canonicalCoreOfBinding cisRetinoicAcidGraph_wellFormed) :=
  annotationOfBinding cisRetinoicAcidConversion cisRetinoicAcidGraph_wellFormed
    []
    cisRetinoidConfigurationClaims
    (centerLocants_of_all (by decide))
    (by unfold DoubleBondConfigurationClaimsWellFormed; decide)

/-! ### Exact supplied lists are retained literally -/

@[simp] theorem retinylideneLLysine_centers_exact :
    retinylideneLLysineAnnotation.centers = [⟨26, .aminoAcidSeries .L⟩] := rfl

@[simp] theorem retinoylBetaDGlucopyranuronate_centers_exact :
    retinoylBetaDGlucopyranuronateAnnotation.centers =
      [⟨21, .anomer .beta⟩, ⟨25, .carbohydrateSeries .D⟩] := rfl

@[simp] theorem hydroxyRetinol_centers_exact :
    hydroxyRetinolAnnotation.centers = [⟨3, .rs .R⟩] := rfl

@[simp] theorem acetoxyRetinol_centers_exact :
    acetoxyRetinolAnnotation.centers = [⟨3, .rs .R⟩] := rfl

@[simp] theorem fluororetinoate_doubleBonds_exact :
    fluororetinoateAnnotation.doubleBonds =
      [ ⟨7, 8, .trans, .E⟩
      , ⟨9, 10, .trans, .E⟩
      , ⟨11, 12, .trans, .Z⟩
      , ⟨13, 14, .trans, .E⟩ ] := rfl

@[simp] theorem cisRetinol_doubleBonds_exact :
    cisRetinolAnnotation.doubleBonds =
      [ ⟨7, 8, .trans, .E⟩
      , ⟨9, 10, .trans, .E⟩
      , ⟨11, 12, .trans, .E⟩
      , ⟨13, 14, .cis, .Z⟩ ] := rfl

@[simp] theorem cisRetinoicAcid_doubleBonds_exact :
    cisRetinoicAcidAnnotation.doubleBonds =
      [ ⟨7, 8, .trans, .E⟩
      , ⟨9, 10, .trans, .E⟩
      , ⟨11, 12, .trans, .E⟩
      , ⟨13, 14, .cis, .Z⟩ ] := rfl

/-- The 11=12 Z claim is retained exactly, separately from its `trans` parent geometry. -/
theorem fluororetinoate_11_12_claim :
    (⟨11, 12, .trans, .Z⟩ : DoubleBondConfigurationClaim) ∈
      fluororetinoateAnnotation.doubleBonds := by
  rw [fluororetinoate_doubleBonds_exact]
  simp

/-- The 13=14 cis/Z claim is retained exactly, with both fields intact. -/
theorem cisRetinol_13_14_claim :
    (⟨13, 14, .cis, .Z⟩ : DoubleBondConfigurationClaim) ∈
      cisRetinolAnnotation.doubleBonds := by
  rw [cisRetinol_doubleBonds_exact]
  simp

/-! ### Resolved centre support, collapsed source data, and ordered bond interactions -/

theorem hydroxyRetinol_3R_resolved :
    ∃ atom, hydroxyRetinolAnnotation.embedding.atomOf 3 = some atom ∧
      atom ∈ hydroxyRetinolAnnotation.annotation.support :=
  NaturalProductAnnotation.center_mem_support hydroxyRetinolAnnotation
    (claim := ⟨3, .rs .R⟩) (by rw [hydroxyRetinol_centers_exact]; simp)

theorem acetoxyRetinol_3R_resolved :
    ∃ atom, acetoxyRetinolAnnotation.embedding.atomOf 3 = some atom ∧
      atom ∈ acetoxyRetinolAnnotation.annotation.support :=
  NaturalProductAnnotation.center_mem_support acetoxyRetinolAnnotation
    (claim := ⟨3, .rs .R⟩) (by rw [acetoxyRetinol_centers_exact]; simp)

theorem retinylideneLLysine_L_resolved :
    ∃ atom, retinylideneLLysineAnnotation.embedding.atomOf 26 = some atom ∧
      atom ∈ retinylideneLLysineAnnotation.annotation.support :=
  NaturalProductAnnotation.center_mem_support retinylideneLLysineAnnotation
    (claim := ⟨26, .aminoAcidSeries .L⟩)
    (by rw [retinylideneLLysine_centers_exact]; simp)

theorem retinoylBetaDGlucopyranuronate_beta_resolved :
    ∃ atom, retinoylBetaDGlucopyranuronateAnnotation.embedding.atomOf 21 = some atom ∧
      atom ∈ retinoylBetaDGlucopyranuronateAnnotation.annotation.support :=
  NaturalProductAnnotation.center_mem_support
    retinoylBetaDGlucopyranuronateAnnotation
    (claim := ⟨21, .anomer .beta⟩)
    (by rw [retinoylBetaDGlucopyranuronate_centers_exact]; simp)

theorem retinoylBetaDGlucopyranuronate_D_resolved :
    ∃ atom, retinoylBetaDGlucopyranuronateAnnotation.embedding.atomOf 25 = some atom ∧
      atom ∈ retinoylBetaDGlucopyranuronateAnnotation.annotation.support :=
  NaturalProductAnnotation.center_mem_support
    retinoylBetaDGlucopyranuronateAnnotation
    (claim := ⟨25, .carbohydrateSeries .D⟩)
    (by rw [retinoylBetaDGlucopyranuronate_centers_exact]; simp)

/-- The L-lysine centre is read back exactly as its original source label payload. -/
theorem retinylideneLLysine_center_payload :
    retinylideneLLysineAnnotation.annotatedFragment.sourceData.filterMap
      naturalCenterLabel? = [⟨26, .aminoAcidSeries .L⟩] := by
  rw [NaturalProductAnnotation.annotatedFragment_center_labels,
    retinylideneLLysine_centers_exact]

/-- The beta-D-glucuronide fragment retains both distinct source-label constructors. -/
theorem retinoylBetaDGlucopyranuronate_center_payloads :
    retinoylBetaDGlucopyranuronateAnnotation.annotatedFragment.sourceData.filterMap
      naturalCenterLabel? =
      [⟨21, .anomer .beta⟩, ⟨25, .carbohydrateSeries .D⟩] := by
  rw [NaturalProductAnnotation.annotatedFragment_center_labels,
    retinoylBetaDGlucopyranuronate_centers_exact]

/-- The four fluororetinoate configuration claims are recovered from the attached source data
with their parent-geometry and E/Z fields intact. -/
theorem fluororetinoate_source_payloads :
    fluororetinoateAnnotation.annotatedFragment.sourceData.filterMap
      naturalDoubleBondClaim? =
      [ ⟨7, 8, .trans, .E⟩
      , ⟨9, 10, .trans, .E⟩
      , ⟨11, 12, .trans, .Z⟩
      , ⟨13, 14, .trans, .E⟩ ] := by
  rw [NaturalProductAnnotation.annotatedFragment_doubleBond_claims,
    fluororetinoate_doubleBonds_exact]

/-- The cis-retinol compound centres: the 13=14 cis/Z payload is exactly recovered. -/
theorem cisRetinol_source_payloads :
    cisRetinolAnnotation.annotatedFragment.sourceData.filterMap
      naturalDoubleBondClaim? =
      [ ⟨7, 8, .trans, .E⟩
      , ⟨9, 10, .trans, .E⟩
      , ⟨11, 12, .trans, .E⟩
      , ⟨13, 14, .cis, .Z⟩ ] := by
  rw [NaturalProductAnnotation.annotatedFragment_doubleBond_claims,
    cisRetinol_doubleBonds_exact]

/-- The actual ordered endpoint interaction of the 7=8 source bond is retained. -/
theorem fluororetinoate_7_8_ordered :
    ∃ source target,
      fluororetinoateAnnotation.embedding.atomOf 7 = some source ∧
      fluororetinoateAnnotation.embedding.atomOf 8 = some target ∧
      ([source, target], .covalent 2) ∈
        (fluororetinoateConversion.canonicalCoreOfBinding
          fluororetinoateGraph_wellFormed).interactions :=
  NaturalProductAnnotation.doubleBonds_orderedInteraction
    fluororetinoateAnnotation (claim := ⟨7, 8, .trans, .E⟩)
    (by rw [fluororetinoate_doubleBonds_exact]; simp)

/-- The 13=14 cis/Z claim still yields the actual ordered interaction; E/Z remains the supplied
claim field and is not replaced by a derived geometric answer. -/
theorem cisRetinol_13_14_ordered :
    ∃ source target,
      cisRetinolAnnotation.embedding.atomOf 13 = some source ∧
      cisRetinolAnnotation.embedding.atomOf 14 = some target ∧
      ([source, target], .covalent 2) ∈
        (cisRetinolConversion.canonicalCoreOfBinding cisRetinolGraph_wellFormed).interactions :=
  NaturalProductAnnotation.doubleBonds_orderedInteraction
    cisRetinolAnnotation (claim := ⟨13, 14, .cis, .Z⟩)
    (by rw [cisRetinol_doubleBonds_exact]; simp)

/-! ### Actual authoritative-conversion bindings for the concrete graphs -/

@[simp] theorem retinylideneLLysine_conversion_atom_count :
    retinylideneLLysineConversion.input.molecule.atoms.length =
      lysylIminomethylGraph.nodes.length :=
  AuthoritativeConversionBinding.atom_count_exact retinylideneLLysineConversion

@[simp] theorem retinoylBetaDGlucopyranuronate_conversion_atom_count :
    retinoylBetaDGlucopyranuronateConversion.input.molecule.atoms.length =
      retinoylGlucuronideGraph.nodes.length :=
  AuthoritativeConversionBinding.atom_count_exact
    retinoylBetaDGlucopyranuronateConversion

@[simp] theorem fluororetinoate_conversion_atom_count :
    fluororetinoateConversion.input.molecule.atoms.length =
      fluororetinoateGraph.nodes.length :=
  AuthoritativeConversionBinding.atom_count_exact fluororetinoateConversion

/-- The actual converter maps the source bond 7--8 to an ordered semantic interaction. -/
theorem fluororetinoate_conversion_bond7_8 :
    ∃ low high interaction,
      heavyAtomNodeIndex? fluororetinoateGraph 7 = some low ∧
      heavyAtomNodeIndex? fluororetinoateGraph 8 = some high ∧
      graphBondToSemanticInteraction? fluororetinoateGraph ⟨7, 8, .double⟩ =
        some interaction ∧
      interaction ∈ fluororetinoateConversion.input.molecule.interactions ∧
      interaction.participants = [low, high] ∧
      interaction.kind = .covalent 2 := by
  simpa using
    AuthoritativeConversionBinding.ordered_endpoints
      (graph := fluororetinoateGraph) fluororetinoateConversion
      (bond := ⟨7, 8, .double⟩) (by decide)

/-- Every concrete node of the L-lysine graph has an exact semantic atom in the actual
authoritative input. -/
theorem retinylideneLLysine_conversion_atom_exact :
    ∀ node ∈ lysylIminomethylGraph.nodes,
      ∃ atom, atomNodeToSemanticAtom? node = some atom ∧
        atom ∈ retinylideneLLysineConversion.input.molecule.atoms :=
  fun _node hnode =>
    AuthoritativeConversionBinding.atomOfNode retinylideneLLysineConversion hnode

/-- The actual conversion of the glucuronide graph retains every ordered bond interaction. -/
theorem retinoylBetaDGlucopyranuronate_conversion_interactions :
    ∀ bond ∈ retinoylGlucuronideGraph.bonds,
      ∃ low high interaction,
        heavyAtomNodeIndex? retinoylGlucuronideGraph bond.low = some low ∧
        heavyAtomNodeIndex? retinoylGlucuronideGraph bond.high = some high ∧
        graphBondToSemanticInteraction? retinoylGlucuronideGraph bond = some interaction ∧
        interaction ∈
          retinoylBetaDGlucopyranuronateConversion.input.molecule.interactions ∧
        interaction.participants = [low, high] ∧
        interaction.kind = .covalent (bondOrderToNat bond.order) :=
  fun _bond hbond =>
    AuthoritativeConversionBinding.ordered_endpoints
      retinoylBetaDGlucopyranuronateConversion hbond

/-! ## Request-relative ingress and canonical-core preservation -/

/-- An ingress bundle relative to one actual molecular-evidence request.  The annotation is
typed against `request.graph`, so its source embedding, centre support and ordered bond
interactions are all facts about the actual request core. -/
structure RequestIngress {V : Type} [DecidableEq V] [Fintype V]
    (request : OrganicMolecularEvidence V) (graph : HeavyAtomGraph) where
  data : NaturalProductAnnotation graph request.graph

namespace RequestIngress

variable {V : Type} [DecidableEq V] [Fintype V]
variable {request : OrganicMolecularEvidence V} {graph : HeavyAtomGraph}

/-- Append exactly the source-data-bearing fragment to the request.  No other request field is
touched. -/
noncomputable def augment (ingress : RequestIngress request graph) :
    OrganicMolecularEvidence V :=
  { request with fragments := request.fragments ++ [ingress.data.annotatedFragment] }

/-- Every retained centre's core atom is exactly the request core's `atomData`, and its source
node is the actual graph node. -/
theorem center_request_core_exact (ingress : RequestIngress request graph)
    {claim : LocatedSourceCenterLabel} (hclaim : claim ∈ ingress.data.centers) :
    ∃ node atom,
      node ∈ graph.nodes ∧ node.locant = claim.atomId ∧
      ingress.data.embedding.atomOf claim.atomId = some atom ∧
      some (request.graph.atomData atom) = atomNodeToSemanticAtom? node :=
  NaturalProductAnnotation.center_source_atom_exact ingress.data hclaim

/-- Every retained configuration claim's ordered interaction lies in the actual request core's
interaction list. -/
theorem doubleBond_request_core_interaction (ingress : RequestIngress request graph)
    {claim : DoubleBondConfigurationClaim} (hclaim : claim ∈ ingress.data.doubleBonds) :
    ∃ source target,
      ingress.data.embedding.atomOf claim.low = some source ∧
      ingress.data.embedding.atomOf claim.high = some target ∧
      ([source, target], .covalent 2) ∈ request.graph.interactions :=
  NaturalProductAnnotation.doubleBonds_orderedInteraction ingress.data hclaim

end RequestIngress

/-- The actual upstream `decode` of the canonical assembly returns exactly the augmented
fragment list.  This composes the existing `decode_canonicalAssemble`; no codec is reproved. -/
theorem canonicalCore_augment_fragments {V : Type} [DecidableEq V] [Fintype V]
    {request : OrganicMolecularEvidence V} {graph : HeavyAtomGraph}
    (ingress : RequestIngress request graph)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (decode (canonicalDecode (canonicalAssemble enumeration ingress.augment))).fragments =
      request.fragments ++ [ingress.data.annotatedFragment] := by
  rw [decode_canonicalAssemble]
  rfl

/-- The natural-product fragment occurs at exactly the first new position of the decoded
canonical output. -/
theorem canonicalCore_augment_fragment_at {V : Type} [DecidableEq V] [Fintype V]
    {request : OrganicMolecularEvidence V} {graph : HeavyAtomGraph}
    (ingress : RequestIngress request graph)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (decode (canonicalDecode (canonicalAssemble enumeration ingress.augment))).fragments[
        request.fragments.length]? = some ingress.data.annotatedFragment := by
  rw [canonicalCore_augment_fragments ingress enumeration]
  exact List.getElem?_concat_length

/-- The original source payloads are recovered from the actual canonical output: the decoded
fragment's `sourceData` is exactly the attached source data, its filtered centre labels are
exactly the supplied centre list, and its filtered configuration claims are exactly the
supplied claim list. -/
theorem canonicalCore_source_payloads_recovered {V : Type} [DecidableEq V] [Fintype V]
    {request : OrganicMolecularEvidence V} {graph : HeavyAtomGraph}
    (ingress : RequestIngress request graph)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    ∃ recovered : FragmentAnnotation V,
      (decode (canonicalDecode (canonicalAssemble enumeration ingress.augment))).fragments[
          request.fragments.length]? = some recovered ∧
      recovered.sourceData = ingress.data.sourceData ∧
      recovered.support = ingress.data.annotation.support ∧
      recovered.bindings = ingress.data.annotation.bindings ∧
      recovered.sourceData.filterMap naturalCenterLabel? =
        ingress.data.centers ∧
      recovered.sourceData.filterMap naturalDoubleBondClaim? =
        ingress.data.doubleBonds := by
  refine ⟨ingress.data.annotatedFragment,
    canonicalCore_augment_fragment_at ingress enumeration, ?_, ?_, ?_, ?_, ?_⟩
  · exact NaturalProductAnnotation.annotatedFragment_sourceData ingress.data
  · exact NaturalProductAnnotation.annotatedFragment_support ingress.data
  · exact NaturalProductAnnotation.annotatedFragment_bindings ingress.data
  · exact NaturalProductAnnotation.annotatedFragment_center_labels ingress.data
  · exact NaturalProductAnnotation.annotatedFragment_doubleBond_claims ingress.data

/-! ## Concrete request ingress and canonical recovery -/

/-- Build the actual request whose core is the conversion-derived canonical core of `graph`.
Every optional channel is genuinely absent. -/
noncomputable def requestOfCore {V : Type} [DecidableEq V] [Fintype V]
    (core : FiniteAtomInteractionHypergraph V) : OrganicMolecularEvidence V where
  graph := core
  conformation := fun _ => 0
  rationalPositions? := none
  rationalPositions_valid := by
    intro positions present
    cases present
  electronic? := none
  electronic_unpaired := by
    intro evidence present
    cases present
  paths? := none
  paths_graph_eq := by
    intro family present
    cases present
  paths_conformation_eq := by
    intro family present
    cases present
  bands? := none
  bands_graph_eq := by
    intro bands present
    cases present
  bands_conformation_eq := by
    intro bands present
    cases present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := none
  frames := []

/-- The request induced by the actual conversion-derived canonical core. -/
noncomputable def requestFromBinding (binding : AuthoritativeConversionBinding graph)
    (wellFormed : graph.WellFormed) :
    OrganicMolecularEvidence (Fin graph.nodes.length) :=
  requestOfCore (binding.canonicalCoreOfBinding wellFormed)

noncomputable def hydroxyRetinolRequest :
    OrganicMolecularEvidence (Fin hydroxyRetinolGraph.nodes.length) :=
  requestFromBinding hydroxyRetinolConversion hydroxyRetinolGraph_wellFormed

noncomputable def acetoxyRetinolRequest :
    OrganicMolecularEvidence (Fin acetoxyRetinolGraph.nodes.length) :=
  requestFromBinding acetoxyRetinolConversion acetoxyRetinolGraph_wellFormed

noncomputable def retinylideneLLysineRequest :
    OrganicMolecularEvidence (Fin lysylIminomethylGraph.nodes.length) :=
  requestFromBinding retinylideneLLysineConversion lysylIminomethylGraph_wellFormed

noncomputable def retinoylBetaDGlucopyranuronateRequest :
    OrganicMolecularEvidence (Fin retinoylGlucuronideGraph.nodes.length) :=
  requestFromBinding retinoylBetaDGlucopyranuronateConversion
    retinoylGlucuronideGraph_wellFormed

noncomputable def fluororetinoateRequest :
    OrganicMolecularEvidence (Fin fluororetinoateGraph.nodes.length) :=
  requestFromBinding fluororetinoateConversion fluororetinoateGraph_wellFormed

noncomputable def cisRetinolRequest :
    OrganicMolecularEvidence (Fin cisRetinolGraph.nodes.length) :=
  requestFromBinding cisRetinolConversion cisRetinolGraph_wellFormed

noncomputable def cisRetinoicAcidRequest :
    OrganicMolecularEvidence (Fin cisRetinoicAcidGraph.nodes.length) :=
  requestFromBinding cisRetinoicAcidConversion cisRetinoicAcidGraph_wellFormed

noncomputable def hydroxyRetinolIngress :
    RequestIngress hydroxyRetinolRequest hydroxyRetinolGraph :=
  ⟨hydroxyRetinolAnnotation⟩

noncomputable def acetoxyRetinolIngress :
    RequestIngress acetoxyRetinolRequest acetoxyRetinolGraph :=
  ⟨acetoxyRetinolAnnotation⟩

noncomputable def retinylideneLLysineIngress :
    RequestIngress retinylideneLLysineRequest lysylIminomethylGraph :=
  ⟨retinylideneLLysineAnnotation⟩

noncomputable def retinoylBetaDGlucopyranuronateIngress :
    RequestIngress retinoylBetaDGlucopyranuronateRequest retinoylGlucuronideGraph :=
  ⟨retinoylBetaDGlucopyranuronateAnnotation⟩

noncomputable def fluororetinoateIngress :
    RequestIngress fluororetinoateRequest fluororetinoateGraph :=
  ⟨fluororetinoateAnnotation⟩

noncomputable def cisRetinolIngress :
    RequestIngress cisRetinolRequest cisRetinolGraph :=
  ⟨cisRetinolAnnotation⟩

noncomputable def cisRetinoicAcidIngress :
    RequestIngress cisRetinoicAcidRequest cisRetinoicAcidGraph :=
  ⟨cisRetinoicAcidAnnotation⟩

/-- The concrete L-lysine ingress's centre fact is about the actual request core. -/
theorem retinylideneLLysine_ingress_center_exact :
    ∃ node atom,
      node ∈ lysylIminomethylGraph.nodes ∧ node.locant = 26 ∧
      retinylideneLLysineIngress.data.embedding.atomOf 26 = some atom ∧
      some (retinylideneLLysineRequest.graph.atomData atom) =
        atomNodeToSemanticAtom? node :=
  RequestIngress.center_request_core_exact retinylideneLLysineIngress
    (claim := ⟨26, .aminoAcidSeries .L⟩)
    (by simp [retinylideneLLysineIngress, retinylideneLLysine_centers_exact])

/-- The concrete 13-cis-retinol ingress's 13=14 interaction is in the actual request core. -/
theorem cisRetinol_ingress_13_14_request_interaction :
    ∃ source target,
      cisRetinolIngress.data.embedding.atomOf 13 = some source ∧
      cisRetinolIngress.data.embedding.atomOf 14 = some target ∧
      ([source, target], .covalent 2) ∈ cisRetinolRequest.graph.interactions :=
  RequestIngress.doubleBond_request_core_interaction cisRetinolIngress
    (claim := ⟨13, 14, .cis, .Z⟩)
    (by simp [cisRetinolIngress, cisRetinol_doubleBonds_exact])

/-- The canonical output of the concrete L-lysine request recovers the original L label. -/
theorem retinylideneLLysine_canonical_payload_recovery :
    ∃ recovered : FragmentAnnotation (Fin lysylIminomethylGraph.nodes.length),
      (decode (canonicalDecode (canonicalAssemble
          (Fintype.equivFin (Fin lysylIminomethylGraph.nodes.length))
          retinylideneLLysineIngress.augment))).fragments[
            retinylideneLLysineRequest.fragments.length]? = some recovered ∧
      recovered.sourceData.filterMap naturalCenterLabel? =
        [⟨26, .aminoAcidSeries .L⟩] := by
  obtain ⟨recovered, hAt, _hData, _hSupport, _hBindings, hCenters, _hClaims⟩ :=
    canonicalCore_source_payloads_recovered retinylideneLLysineIngress
      (Fintype.equivFin (Fin lysylIminomethylGraph.nodes.length))
  refine ⟨recovered, hAt, ?_⟩
  rw [hCenters]
  simp [retinylideneLLysineIngress, retinylideneLLysine_centers_exact]

/-! ## Simultaneous source-example catalog -/

/-- One actual source row: the exact graph and the exact ordered centre/configuration lists. -/
structure SourceExample where
  graph : HeavyAtomGraph
  centers : List LocatedSourceCenterLabel
  doubleBonds : List DoubleBondConfigurationClaim
  deriving DecidableEq, Repr

/-- The four explicit-centre examples and the three E/Z example graphs, in source order. -/
def naturalProductSourceExamples : List SourceExample :=
  [ ⟨lysylIminomethylGraph,
      ExplicitCenterLabelCatalog.claimsFor .retinylideneLLysine, []⟩
  , ⟨retinoylGlucuronideGraph,
      ExplicitCenterLabelCatalog.claimsFor .retinoylBetaDGlucopyranuronate, []⟩
  , ⟨hydroxyRetinolGraph,
      ExplicitCenterLabelCatalog.claimsFor .hydroxyRetinol3R, []⟩
  , ⟨acetoxyRetinolGraph,
      ExplicitCenterLabelCatalog.claimsFor .acetoxyRetinol3R, []⟩
  , ⟨fluororetinoateGraph, [], fluororetinoateConfigurationClaims⟩
  , ⟨cisRetinolGraph, [], cisRetinoidConfigurationClaims⟩
  , ⟨cisRetinoicAcidGraph, [], cisRetinoidConfigurationClaims⟩ ]

@[simp] theorem naturalProductSourceExamples_length :
    naturalProductSourceExamples.length = 7 := by
  decide

@[simp] theorem naturalProductSourceExamples_center_counts :
    naturalProductSourceExamples.map (fun row => row.centers.length) =
      [1, 2, 1, 1, 0, 0, 0] := by
  decide

@[simp] theorem naturalProductSourceExamples_doubleBond_counts :
    naturalProductSourceExamples.map (fun row => row.doubleBonds.length) =
      [0, 0, 0, 0, 4, 4, 4] := by
  decide

@[simp] theorem naturalProductSourceExamples_center_lists :
    naturalProductSourceExamples.map (fun row => row.centers) =
      [ [⟨26, .aminoAcidSeries .L⟩]
      , [⟨21, .anomer .beta⟩, ⟨25, .carbohydrateSeries .D⟩]
      , [⟨3, .rs .R⟩]
      , [⟨3, .rs .R⟩]
      , []
      , []
      , [] ] := rfl

@[simp] theorem naturalProductSourceExamples_doubleBond_lists :
    naturalProductSourceExamples.map (fun row => row.doubleBonds) =
      [ []
      , []
      , []
      , []
      , [ ⟨7, 8, .trans, .E⟩
        , ⟨9, 10, .trans, .E⟩
        , ⟨11, 12, .trans, .Z⟩
        , ⟨13, 14, .trans, .E⟩ ]
      , [ ⟨7, 8, .trans, .E⟩
        , ⟨9, 10, .trans, .E⟩
        , ⟨11, 12, .trans, .E⟩
        , ⟨13, 14, .cis, .Z⟩ ]
      , [ ⟨7, 8, .trans, .E⟩
        , ⟨9, 10, .trans, .E⟩
        , ⟨11, 12, .trans, .E⟩
        , ⟨13, 14, .cis, .Z⟩ ] ] := rfl

end OrganicStereoNaturalProductAnnotationIngress
end TetraStereo.OneCenter

/-! ## Kernel-only guards -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.nodeIndexAux?_ge
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.nodeIndexAux?_lt_length
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.nodeIndexAux?_exists_of_mem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.nodeIndexAux?_locant_unique
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.nodeIndexAux?_get?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.heavyAtomNodeIndex?_locant_unique
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.canonicalAtomOf_eq_some_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.canonicalAtomOf_injective_on_resolved
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.canonicalAtomOf_node_get?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.canonicalInteractions_nodup
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.center_atom_mem_support
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.doubleBond_ordered_interaction
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.NaturalProductAnnotation.sourceData_supported
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.NaturalProductAnnotation.annotatedFragment_center_labels
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.NaturalProductAnnotation.annotatedFragment_doubleBond_claims
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.NaturalProductAnnotation.center_source_atom_exact
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.NaturalProductAnnotation.doubleBonds_orderedInteraction
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.AuthoritativeConversionBinding.atoms_exact
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.AuthoritativeConversionBinding.interactions_exact
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.AuthoritativeConversionBinding.atomOfNode
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.AuthoritativeConversionBinding.ordered_endpoints
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.AuthoritativeConversionBinding.conversion_package
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.retinylideneLLysine_center_payload
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.retinoylBetaDGlucopyranuronate_center_payloads
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.fluororetinoate_source_payloads
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.fluororetinoate_7_8_ordered
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.cisRetinol_13_14_ordered
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.fluororetinoate_conversion_bond7_8
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.RequestIngress.center_request_core_exact
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.RequestIngress.doubleBond_request_core_interaction
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.canonicalCore_augment_fragments
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.canonicalCore_augment_fragment_at
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.canonicalCore_source_payloads_recovered
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.retinylideneLLysine_ingress_center_exact
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.cisRetinol_ingress_13_14_request_interaction
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoNaturalProductAnnotationIngress.retinylideneLLysine_canonical_payload_recovery
