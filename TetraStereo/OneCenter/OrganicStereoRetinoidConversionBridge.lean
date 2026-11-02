import TetraStereo.OneCenter.Retinoid1981CertifiedAuthorityInput
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact conversion bridge for the retinoid figure heavy-atom graphs

The certified frontier in `Retinoid1981CertifiedAuthorityInput.lean` records, for each concrete
figure graph, a `CertifiedAuthoritativeChemicalInput` together with **count** equalities
(`atomCountExact`, `interactionCountExact`).  Counts alone do not say that the certified input is
the image of `heavyAtomGraphToAuthoritativeChemicalInput?`.  This module proves the missing,
faithful bridge from the *actual* conversion definition.

Main results, for an arbitrary `HeavyAtomGraph` and an arbitrary `AuthoritativeChemicalInput`
with an actual success equality `heavyAtomGraphToAuthoritativeChemicalInput? graph = some input`:

* the atom list is exactly the checked, source-ordered `mapM` of the node list;
* the interaction list is exactly the checked, source-ordered `mapM` of the bond list;
* the output has no spatial or diagram evidence;
* every index is characterised by an exact `listGet?` equation (no `List.Forall2` premise);
* each converted atom has exactly the standard `SemanticAtom` defaults for the fields the graph
  does not carry, and its periodic element is the checked conversion of its source element;
* each converted bond preserves the ordered endpoint **indices** `[lowIndex, highIndex]` and the
  covalent order (`.single ↦ 1`, `.double ↦ 2`);
* node-locant lookup returns a list position (never the locant itself), bounded by the node count,
  whose node carries the requested original locant; under explicit source `Nodup` every node's own
  locant resolves back to its own position.

`AuthorityInputCandidate.certify?_exact` extracts the actual conversion witness and the
`certify?` tie from a real `certify? = some entry` success.  Nothing in this module treats the
stored count equalities as element or connectivity information.

This is a conversion-exactness bridge only.  It does not assign chemical identities, add implicit
hydrogens, produce a formula, recover source labels/formula/identifiers from a graph, decide
figure fidelity, or sign off any figure.  A `genericSubstituent` node has no conversion and no
element is invented for it.
-/

namespace TetraStereo.OneCenter
namespace Retinoid1981
namespace FigureAuthorityInput

open FigureGraphTranscription

/-! ## Generic `Option`-valued `mapM` lemmas -/

namespace OptionMapM

/-- Successful `Option`-`mapM` preserves the list length. -/
theorem list_mapM_option_length {α β : Type} (f : α → Option β) :
    ∀ {source : List α} {target : List β},
      source.mapM f = some target → target.length = source.length := by
  intro source
  induction source with
  | nil =>
      intro target converted
      simp [List.mapM_nil] at converted
      subst target
      rfl
  | cons head tail inductionHypothesis =>
      intro target converted
      cases headObserved : f head with
      | none => simp [List.mapM_cons, headObserved] at converted
      | some headValue =>
          cases tailObserved : tail.mapM f with
          | none => simp [List.mapM_cons, headObserved, tailObserved] at converted
          | some tailValues =>
              simp [List.mapM_cons, headObserved, tailObserved] at converted
              cases converted
              simp [inductionHypothesis tailObserved]

/-- Successful `Option`-`mapM` is exact at every index: the target lookup is the source lookup
composed with the checked single-element callback. -/
theorem list_mapM_option_listGet? {α β : Type} (f : α → Option β) :
    ∀ {source : List α} {target : List β},
      source.mapM f = some target → ∀ index : ℕ,
        listGet? target index = (listGet? source index).bind f := by
  intro source
  induction source with
  | nil =>
      intro target converted index
      simp [List.mapM_nil] at converted
      subst target
      simp [listGet?]
  | cons head tail inductionHypothesis =>
      intro target converted index
      cases headObserved : f head with
      | none => simp [List.mapM_cons, headObserved] at converted
      | some headValue =>
          cases tailObserved : tail.mapM f with
          | none => simp [List.mapM_cons, headObserved, tailObserved] at converted
          | some tailValues =>
              simp [List.mapM_cons, headObserved, tailObserved] at converted
              cases converted
              cases index with
              | zero => simp [listGet?, headObserved]
              | succ index =>
                  simpa [listGet?] using inductionHypothesis tailObserved index

/-- Every source element of a successful `Option`-`mapM` converts successfully. -/
theorem list_mapM_option_exists_of_mem {α β : Type} {f : α → Option β} :
    ∀ {source : List α} {target : List β}, source.mapM f = some target →
      ∀ {value : α}, value ∈ source → ∃ converted : β, f value = some converted := by
  intro source
  induction source with
  | nil =>
      intro target converted value member
      simp at member
  | cons head tail inductionHypothesis =>
      intro target converted value member
      cases headObserved : f head with
      | none => simp [List.mapM_cons, headObserved] at converted
      | some headValue =>
          cases tailObserved : tail.mapM f with
          | none => simp [List.mapM_cons, headObserved, tailObserved] at converted
          | some tailValues =>
              rcases List.mem_cons.mp member with same | tailMember
              · subst value
                exact ⟨headValue, headObserved⟩
              · exact inductionHypothesis tailObserved tailMember

end OptionMapM

/-! ## Source element conversion -/

/-- The checked atomic number of a concrete `AtomElement`.  It is `Option`-valued precisely
because a source-generic substituent has no element; no atomic number is invented for it. -/
def atomElementAtomicNumber? : AtomElement → Option ℕ
  | .carbon => some 6
  | .nitrogen => some 7
  | .oxygen => some 8
  | .fluorine => some 9
  | .genericSubstituent => none

@[simp] theorem atomElementToPeriodic?_genericSubstituent :
    atomElementToPeriodic? .genericSubstituent = none := rfl

@[simp] theorem atomElementToPeriodic?_isSome (element : AtomElement) :
    (atomElementToPeriodic? element).isSome = true ↔
      element ≠ .genericSubstituent := by
  cases element <;> decide

/-- The checked constructor `PeriodicElement.ofAtomicNumber?` preserves its atomic number. -/
theorem periodicElement_ofAtomicNumber?_atomicNumber (number : ℕ)
    (periodic : PeriodicElement)
    (converted : PeriodicElement.ofAtomicNumber? number = some periodic) :
    periodic.atomicNumber = number := by
  unfold PeriodicElement.ofAtomicNumber? at converted
  split at converted
  · split at converted
    · cases converted
      rfl
    · simp at converted
  · simp at converted

/-- Successful periodic-element conversion is one of the four concrete source elements.  The
generic substituent case is impossible, so this is not a total element assignment. -/
theorem atomElementToPeriodic?_exact (source : AtomElement) (periodic : PeriodicElement)
    (converted : atomElementToPeriodic? source = some periodic) :
    (source = .carbon ∧ periodic.atomicNumber = 6) ∨
      (source = .nitrogen ∧ periodic.atomicNumber = 7) ∨
      (source = .oxygen ∧ periodic.atomicNumber = 8) ∨
      (source = .fluorine ∧ periodic.atomicNumber = 9) := by
  cases source with
  | carbon =>
      left
      refine ⟨rfl, ?_⟩
      exact periodicElement_ofAtomicNumber?_atomicNumber 6 periodic
        (by simpa [atomElementToPeriodic?] using converted)
  | nitrogen =>
      right; left
      refine ⟨rfl, ?_⟩
      exact periodicElement_ofAtomicNumber?_atomicNumber 7 periodic
        (by simpa [atomElementToPeriodic?] using converted)
  | oxygen =>
      right; right; left
      refine ⟨rfl, ?_⟩
      exact periodicElement_ofAtomicNumber?_atomicNumber 8 periodic
        (by simpa [atomElementToPeriodic?] using converted)
  | fluorine =>
      right; right; right
      refine ⟨rfl, ?_⟩
      exact periodicElement_ofAtomicNumber?_atomicNumber 9 periodic
        (by simpa [atomElementToPeriodic?] using converted)
  | genericSubstituent => simp [atomElementToPeriodic?] at converted

/-- The atomic number carried by a successful checked conversion.  `None` on the generic
substituent; `some` exactly on concrete source elements. -/
theorem atomElementToPeriodic?_atomicNumber? (element : AtomElement)
    (periodic : PeriodicElement)
    (converted : atomElementToPeriodic? element = some periodic) :
    atomElementAtomicNumber? element = some periodic.atomicNumber := by
  cases element with
  | carbon =>
      have numberExact := periodicElement_ofAtomicNumber?_atomicNumber 6 periodic
        (by simpa [atomElementToPeriodic?] using converted)
      simp [atomElementAtomicNumber?, numberExact]
  | nitrogen =>
      have numberExact := periodicElement_ofAtomicNumber?_atomicNumber 7 periodic
        (by simpa [atomElementToPeriodic?] using converted)
      simp [atomElementAtomicNumber?, numberExact]
  | oxygen =>
      have numberExact := periodicElement_ofAtomicNumber?_atomicNumber 8 periodic
        (by simpa [atomElementToPeriodic?] using converted)
      simp [atomElementAtomicNumber?, numberExact]
  | fluorine =>
      have numberExact := periodicElement_ofAtomicNumber?_atomicNumber 9 periodic
        (by simpa [atomElementToPeriodic?] using converted)
      simp [atomElementAtomicNumber?, numberExact]
  | genericSubstituent => simp [atomElementToPeriodic?] at converted

/-! ## Single-atom exactness -/

@[simp] theorem atomNodeToSemanticAtom?_isSome (node : AtomNode) :
    (atomNodeToSemanticAtom? node).isSome = true ↔
      node.element ≠ .genericSubstituent := by
  cases observed : atomElementToPeriodic? node.element with
  | none =>
      have generic : node.element = .genericSubstituent := by
        by_contra concrete
        have present := (atomElementToPeriodic?_isSome node.element).mpr concrete
        simp [observed] at present
      have isSomeEq : (atomNodeToSemanticAtom? node).isSome = false := by
        simp [atomNodeToSemanticAtom?, observed]
      rw [isSomeEq]
      simp [generic]
  | some element =>
      have concrete : node.element ≠ .genericSubstituent := by
        apply (atomElementToPeriodic?_isSome node.element).mp
        simp [observed]
      have isSomeEq : (atomNodeToSemanticAtom? node).isSome = true := by
        simp [atomNodeToSemanticAtom?, observed]
      rw [isSomeEq]
      exact ⟨fun _ => concrete, fun _ => rfl⟩

/-- A successful node conversion exposes exactly the checked periodic element. -/
theorem atomNodeToSemanticAtom?_element (node : AtomNode) (atom : SemanticAtom)
    (converted : atomNodeToSemanticAtom? node = some atom) :
    atomElementToPeriodic? node.element = some atom.element := by
  unfold atomNodeToSemanticAtom? at converted
  change (atomElementToPeriodic? node.element).bind
      (fun element => some { element := element }) = some atom at converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨element, elementObserved, hvalue⟩ := converted
  rw [Option.some.injEq] at hvalue
  cases hvalue
  exact elementObserved

/-- The atomic number of a converted semantic atom is the checked source atomic number. -/
theorem atomNodeToSemanticAtom?_atomicNumber (node : AtomNode) (atom : SemanticAtom)
    (converted : atomNodeToSemanticAtom? node = some atom) :
    atomElementAtomicNumber? node.element = some atom.element.atomicNumber :=
  atomElementToPeriodic?_atomicNumber? node.element atom.element
    (atomNodeToSemanticAtom?_element node atom converted)

/-- The graph carries no isotope, charge, radical or aromatic evidence, so the actual conversion
materializes exactly the `SemanticAtom` defaults for those fields. -/
theorem atomNodeToSemanticAtom?_defaults (node : AtomNode) (atom : SemanticAtom)
    (converted : atomNodeToSemanticAtom? node = some atom) :
    atom.isotopeMassNumber? = none ∧ atom.formalCharge = 0 ∧
      atom.unpairedElectrons = 0 ∧ atom.aromaticInput = false := by
  unfold atomNodeToSemanticAtom? at converted
  change (atomElementToPeriodic? node.element).bind
      (fun element => some { element := element }) = some atom at converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨element, _elementObserved, hvalue⟩ := converted
  rw [Option.some.injEq] at hvalue
  cases hvalue
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Node-locant lookup specification

`heavyAtomNodeIndex?` returns the *list position* of the first node with the requested locant,
not the locant itself. -/

/-- Successful auxiliary lookup yields the absolute position, a bound, and the node carrying the
requested locant. -/
theorem nodeIndexAux?_spec (nodes : List AtomNode) :
    ∀ (locant start index : ℕ), nodeIndexAux? nodes locant start = some index →
      ∃ offset node, index = start + offset ∧ offset < nodes.length ∧
        listGet? nodes offset = some node ∧ node.locant = locant := by
  induction nodes with
  | nil =>
      intro locant start index found
      simp [nodeIndexAux?] at found
  | cons head tail inductionHypothesis =>
      intro locant start index found
      unfold nodeIndexAux? at found
      split at found
      · rename_i locantEqual
        have startEq : start = index := Option.some.inj found
        have indexEq : index = start := startEq.symm
        exact ⟨0, head, by omega, by simp, rfl, locantEqual⟩
      · rename_i locantDiffers
        obtain ⟨offset, node, indexEq, bound, lookup, locantEq⟩ :=
          inductionHypothesis locant (start + 1) index found
        exact ⟨offset + 1, node, by omega,
          by simpa [List.length_cons] using Nat.succ_lt_succ bound,
          by simpa [listGet?] using lookup, locantEq⟩

/-- Successful top-level lookup yields a bounded position and the node with the requested
original locant. -/
theorem heavyAtomNodeIndex?_spec (graph : HeavyAtomGraph) (locant index : ℕ)
    (found : heavyAtomNodeIndex? graph locant = some index) :
    index < graph.nodes.length ∧
      ∃ node, listGet? graph.nodes index = some node ∧ node.locant = locant := by
  obtain ⟨offset, node, indexEq, bound, lookup, locantEq⟩ :=
    nodeIndexAux?_spec graph.nodes locant 0 index found
  have indexEq' : index = offset := by simpa using indexEq
  rw [indexEq']
  exact ⟨bound, node, lookup, locantEq⟩

/-! ## Bond conversion exactness -/

@[simp] theorem bondOrderToNat_single : bondOrderToNat .single = 1 := rfl

@[simp] theorem bondOrderToNat_double : bondOrderToNat .double = 2 := rfl

/-- A successful bond conversion preserves the exact ordered endpoint indices and the covalent
bond order. -/
theorem graphBondToSemanticInteraction?_exact (graph : HeavyAtomGraph)
    (bond : GraphBond) (interaction : SemanticInteraction)
    (converted : graphBondToSemanticInteraction? graph bond = some interaction) :
    ∃ low high,
      heavyAtomNodeIndex? graph bond.low = some low ∧
        heavyAtomNodeIndex? graph bond.high = some high ∧
        interaction.participants = [low, high] ∧
        interaction.kind = .covalent (bondOrderToNat bond.order) := by
  unfold graphBondToSemanticInteraction? at converted
  change (heavyAtomNodeIndex? graph bond.low).bind
      (fun low => (heavyAtomNodeIndex? graph bond.high).bind
        (fun high => some
          { participants := [low, high]
            kind := .covalent (bondOrderToNat bond.order) })) =
      some interaction at converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨low, lowObserved, converted⟩ := converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨high, highObserved, hvalue⟩ := converted
  rw [Option.some.injEq] at hvalue
  cases hvalue
  exact ⟨low, high, lowObserved, highObserved, rfl, rfl⟩

/-- Endpoint specification: the returned indices are list positions below the node count, and the
nodes at those positions carry the original source locants.  The locant is never identified with
the target index. -/
theorem graphBondToSemanticInteraction?_endpoints_spec (graph : HeavyAtomGraph)
    (bond : GraphBond) (interaction : SemanticInteraction)
    (converted : graphBondToSemanticInteraction? graph bond = some interaction) :
    ∃ low high,
      heavyAtomNodeIndex? graph bond.low = some low ∧
        heavyAtomNodeIndex? graph bond.high = some high ∧
        low < graph.nodes.length ∧ high < graph.nodes.length ∧
        (∃ lowNode, listGet? graph.nodes low = some lowNode ∧ lowNode.locant = bond.low) ∧
        (∃ highNode, listGet? graph.nodes high = some highNode ∧ highNode.locant = bond.high) ∧
        interaction.participants = [low, high] ∧
        interaction.kind = .covalent (bondOrderToNat bond.order) := by
  obtain ⟨low, high, lowObserved, highObserved, participants, kind⟩ :=
    graphBondToSemanticInteraction?_exact graph bond interaction converted
  obtain ⟨lowBound, lowNode, lowLookup, lowLocant⟩ :=
    heavyAtomNodeIndex?_spec graph bond.low low lowObserved
  obtain ⟨highBound, highNode, highLookup, highLocant⟩ :=
    heavyAtomNodeIndex?_spec graph bond.high high highObserved
  exact ⟨low, high, lowObserved, highObserved, lowBound, highBound,
    ⟨lowNode, lowLookup, lowLocant⟩, ⟨highNode, highLookup, highLocant⟩,
    participants, kind⟩

/-- Single bonds convert to exactly `.covalent 1`. -/
theorem graphBondToSemanticInteraction?_single (graph : HeavyAtomGraph)
    (bond : GraphBond) (interaction : SemanticInteraction)
    (orderExact : bond.order = .single)
    (converted : graphBondToSemanticInteraction? graph bond = some interaction) :
    ∃ low high,
      heavyAtomNodeIndex? graph bond.low = some low ∧
        heavyAtomNodeIndex? graph bond.high = some high ∧
        interaction.participants = [low, high] ∧
        interaction.kind = .covalent 1 := by
  obtain ⟨low, high, lowObserved, highObserved, participants, kind⟩ :=
    graphBondToSemanticInteraction?_exact graph bond interaction converted
  refine ⟨low, high, lowObserved, highObserved, participants, ?_⟩
  rw [kind, orderExact]
  rfl

/-- Double bonds convert to exactly `.covalent 2`. -/
theorem graphBondToSemanticInteraction?_double (graph : HeavyAtomGraph)
    (bond : GraphBond) (interaction : SemanticInteraction)
    (orderExact : bond.order = .double)
    (converted : graphBondToSemanticInteraction? graph bond = some interaction) :
    ∃ low high,
      heavyAtomNodeIndex? graph bond.low = some low ∧
        heavyAtomNodeIndex? graph bond.high = some high ∧
        interaction.participants = [low, high] ∧
        interaction.kind = .covalent 2 := by
  obtain ⟨low, high, lowObserved, highObserved, participants, kind⟩ :=
    graphBondToSemanticInteraction?_exact graph bond interaction converted
  refine ⟨low, high, lowObserved, highObserved, participants, ?_⟩
  rw [kind, orderExact]
  rfl

/-! ## Node-locant lookup completeness

`heavyAtomNodeIndex?` returns the *list position* of the first node with the requested locant,
not the locant itself.  The specification lemmas `nodeIndexAux?_spec` and
`heavyAtomNodeIndex?_spec` live above, next to the bond conversion that uses them.

Under explicit source-locant `Nodup`, every node position resolves from that node's own
locant back to exactly that position. -/
theorem nodeIndexAux?_complete_of_nodup (nodes : List AtomNode) :
    ∀ (start : ℕ), (nodes.map AtomNode.locant).Nodup →
      ∀ (offset : ℕ) (node : AtomNode), offset < nodes.length →
        listGet? nodes offset = some node →
        nodeIndexAux? nodes node.locant start = some (start + offset) := by
  induction nodes with
  | nil =>
      intro start nodup offset node bound lookup
      simp at bound
  | cons head tail inductionHypothesis =>
      intro start nodup offset node bound lookup
      obtain ⟨headNotMem, tailNodup⟩ := List.nodup_cons.mp nodup
      cases offset with
      | zero =>
          have lookupHead : some head = some node := by simpa [listGet?] using lookup
          have headEq : head = node := Option.some.inj lookupHead
          subst node
          simp [nodeIndexAux?]
      | succ offset =>
          have lookupTail : listGet? tail offset = some node := by
            simpa [listGet?] using lookup
          have boundTail : offset < tail.length := by simpa using bound
          have nodeMember : node ∈ tail :=
            listGet?_eq_some_implies_mem tail offset node lookupTail
          have locantMember : node.locant ∈ tail.map AtomNode.locant :=
            List.mem_map_of_mem nodeMember
          have headDiffers : head.locant ≠ node.locant := by
            intro same
            apply headNotMem
            rw [same]
            exact locantMember
          rw [nodeIndexAux?]
          rw [if_neg headDiffers]
          have recursive :=
            inductionHypothesis (start + 1) tailNodup offset node boundTail lookupTail
          rw [recursive]
          congr 1
          omega

/-- Lookup completeness for every node position under source-locant `Nodup`. -/
theorem heavyAtomNodeIndex?_complete_of_nodup (graph : HeavyAtomGraph)
    (nodup : graph.locants.Nodup) (index : ℕ) (bound : index < graph.nodes.length) :
    heavyAtomNodeIndex? graph (graph.nodes.get ⟨index, bound⟩).locant = some index := by
  have lookup : listGet? graph.nodes index = some (graph.nodes.get ⟨index, bound⟩) :=
    listGet?_eq_some_get graph.nodes ⟨index, bound⟩
  have complete :=
    nodeIndexAux?_complete_of_nodup graph.nodes 0 nodup index
      (graph.nodes.get ⟨index, bound⟩) bound lookup
  simpa [heavyAtomNodeIndex?, Nat.zero_add] using complete

/-- Every node of a source-`Nodup` graph resolves from its own locant. -/
theorem heavyAtomNodeIndex?_isSome_of_mem_of_nodup (graph : HeavyAtomGraph)
    (nodup : graph.locants.Nodup) {node : AtomNode} (member : node ∈ graph.nodes) :
    ∃ index, heavyAtomNodeIndex? graph node.locant = some index := by
  obtain ⟨position, positionEq⟩ := List.get_of_mem member
  refine ⟨position.val, ?_⟩
  rw [← positionEq]
  exact heavyAtomNodeIndex?_complete_of_nodup graph nodup position.val position.isLt

/-! ## Whole-graph conversion exactness -/

/-- The actual conversion fixes every field of a successful output. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_fields
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    (∃ atoms : List SemanticAtom,
        graph.nodes.mapM atomNodeToSemanticAtom? = some atoms ∧
          input.molecule.atoms = atoms) ∧
      (∃ interactions : List SemanticInteraction,
        graph.bonds.mapM (graphBondToSemanticInteraction? graph) = some interactions ∧
          input.molecule.interactions = interactions) ∧
      input.spatial? = none ∧
      input.diagram? = none := by
  unfold heavyAtomGraphToAuthoritativeChemicalInput? at converted
  change (graph.nodes.mapM atomNodeToSemanticAtom?).bind
      (fun atoms => (graph.bonds.mapM (graphBondToSemanticInteraction? graph)).bind
        (fun interactions =>
          some { molecule := { atoms := atoms, interactions := interactions } })) =
      some input at converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨atoms, atomsObserved, converted⟩ := converted
  rw [Option.bind_eq_some_iff] at converted
  obtain ⟨interactions, interactionsObserved, hvalue⟩ := converted
  rw [Option.some.injEq] at hvalue
  cases hvalue
  exact ⟨⟨atoms, atomsObserved, rfl⟩,
    ⟨interactions, interactionsObserved, rfl⟩, rfl, rfl⟩

/-- Alias of `heavyAtomGraphToAuthoritativeChemicalInput?_fields`. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_exact
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    (∃ atoms : List SemanticAtom,
        graph.nodes.mapM atomNodeToSemanticAtom? = some atoms ∧
          input.molecule.atoms = atoms) ∧
      (∃ interactions : List SemanticInteraction,
        graph.bonds.mapM (graphBondToSemanticInteraction? graph) = some interactions ∧
          input.molecule.interactions = interactions) ∧
      input.spatial? = none ∧
      input.diagram? = none :=
  heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted

/-- The atom list of a successful conversion is exactly the source-ordered checked node
conversion. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_atoms_eq_mapM
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    ∃ atoms : List SemanticAtom,
      graph.nodes.mapM atomNodeToSemanticAtom? = some atoms ∧
        input.molecule.atoms = atoms :=
  (heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted).1

/-- The interaction list of a successful conversion is exactly the source-ordered checked bond
conversion. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_interactions_eq_mapM
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    ∃ interactions : List SemanticInteraction,
      graph.bonds.mapM (graphBondToSemanticInteraction? graph) = some interactions ∧
        input.molecule.interactions = interactions :=
  (heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted).2.1

/-- No spatial evidence is invented by the graph conversion. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_spatial
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    input.spatial? = none :=
  (heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted).2.2.1

/-- No diagram evidence is invented by the graph conversion. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_diagram
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    input.diagram? = none :=
  (heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted).2.2.2

/-- Successful conversion preserves the exact atom count. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_atomCount
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    input.molecule.atomCount = graph.nodes.length := by
  obtain ⟨⟨atoms, atomsObserved, atomsEq⟩, _, _, _⟩ :=
    heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted
  change input.molecule.atoms.length = graph.nodes.length
  rw [atomsEq]
  exact OptionMapM.list_mapM_option_length atomNodeToSemanticAtom? atomsObserved

/-- Successful conversion preserves the exact interaction count. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_interactionCount
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    input.molecule.interactions.length = graph.bonds.length := by
  obtain ⟨_, ⟨interactions, interactionsObserved, interactionsEq⟩, _, _⟩ :=
    heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted
  rw [interactionsEq]
  exact OptionMapM.list_mapM_option_length
    (graphBondToSemanticInteraction? graph) interactionsObserved

/-- Atom-count alias in terms of the raw atom list. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_atoms_length
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    input.molecule.atoms.length = graph.nodes.length :=
  heavyAtomGraphToAuthoritativeChemicalInput?_atomCount graph input converted

/-- Every index of a successful conversion is exact. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_atomAt?
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input)
    (index : ℕ) :
    listGet? input.molecule.atoms index =
      (listGet? graph.nodes index).bind atomNodeToSemanticAtom? := by
  obtain ⟨⟨atoms, atomsObserved, atomsEq⟩, _, _, _⟩ :=
    heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted
  rw [atomsEq]
  exact OptionMapM.list_mapM_option_listGet? atomNodeToSemanticAtom? atomsObserved index

/-- Every interaction index of a successful conversion is exact. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_interactionAt?
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input)
    (index : ℕ) :
    listGet? input.molecule.interactions index =
      (listGet? graph.bonds index).bind (graphBondToSemanticInteraction? graph) := by
  obtain ⟨_, ⟨interactions, interactionsObserved, interactionsEq⟩, _, _⟩ :=
    heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted
  rw [interactionsEq]
  exact OptionMapM.list_mapM_option_listGet?
    (graphBondToSemanticInteraction? graph) interactionsObserved index

/-- In-range atom index exactness: the source node, its checked conversion and the target atom
are tied together, including the standard `SemanticAtom` defaults. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_atomAt?_exact_of_lt
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input)
    (index : ℕ) (bound : index < graph.nodes.length) :
    ∃ node atom,
      listGet? graph.nodes index = some node ∧
        atomNodeToSemanticAtom? node = some atom ∧
        listGet? input.molecule.atoms index = some atom ∧
        atomElementToPeriodic? node.element = some atom.element ∧
        atom.isotopeMassNumber? = none ∧ atom.formalCharge = 0 ∧
        atom.unpairedElectrons = 0 ∧ atom.aromaticInput = false := by
  have atomsLength :=
    heavyAtomGraphToAuthoritativeChemicalInput?_atoms_length graph input converted
  obtain ⟨node, nodeLookup⟩ := listGet?_exists_of_lt graph.nodes index bound
  obtain ⟨atom, atomLookup⟩ :=
    listGet?_exists_of_lt input.molecule.atoms index (by rw [atomsLength]; exact bound)
  have indexed :=
    heavyAtomGraphToAuthoritativeChemicalInput?_atomAt? graph input converted index
  rw [nodeLookup] at indexed
  have conversion : atomNodeToSemanticAtom? node = some atom := by
    have chained := indexed.symm.trans atomLookup
    simpa using chained
  have elementExact := atomNodeToSemanticAtom?_element node atom conversion
  obtain ⟨isotopeExact, chargeExact, radicalExact, aromaticExact⟩ :=
    atomNodeToSemanticAtom?_defaults node atom conversion
  exact ⟨node, atom, nodeLookup, conversion, atomLookup, elementExact,
    isotopeExact, chargeExact, radicalExact, aromaticExact⟩

/-- In-range interaction index exactness: the source bond, its checked conversion and the target
interaction are tied together with the exact ordered endpoint indices and bond order. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_interactionAt?_exact_of_lt
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input)
    (index : ℕ) (bound : index < graph.bonds.length) :
    ∃ bond interaction,
      listGet? graph.bonds index = some bond ∧
        graphBondToSemanticInteraction? graph bond = some interaction ∧
        listGet? input.molecule.interactions index = some interaction ∧
        ∃ low high,
          heavyAtomNodeIndex? graph bond.low = some low ∧
            heavyAtomNodeIndex? graph bond.high = some high ∧
            interaction.participants = [low, high] ∧
            interaction.kind = .covalent (bondOrderToNat bond.order) := by
  have interactionsLength :=
    heavyAtomGraphToAuthoritativeChemicalInput?_interactionCount graph input converted
  obtain ⟨bond, bondLookup⟩ := listGet?_exists_of_lt graph.bonds index bound
  obtain ⟨interaction, interactionLookup⟩ :=
    listGet?_exists_of_lt input.molecule.interactions index
      (by rw [interactionsLength]; exact bound)
  have indexed :=
    heavyAtomGraphToAuthoritativeChemicalInput?_interactionAt? graph input converted index
  rw [bondLookup] at indexed
  have conversion : graphBondToSemanticInteraction? graph bond = some interaction := by
    have chained := indexed.symm.trans interactionLookup
    simpa using chained
  obtain ⟨low, high, lowObserved, highObserved, participants, kind⟩ :=
    graphBondToSemanticInteraction?_exact graph bond interaction conversion
  exact ⟨bond, interaction, bondLookup, conversion, interactionLookup,
    ⟨low, high, lowObserved, highObserved, participants, kind⟩⟩

/-- Every node of a successfully converted graph has a concrete source element.  This is the
positive counterpart of the generic-substituent boundary. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_node_concrete
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input)
    {node : AtomNode} (member : node ∈ graph.nodes) :
    node.element ≠ .genericSubstituent := by
  obtain ⟨⟨atoms, atomsObserved, _⟩, _, _, _⟩ :=
    heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted
  obtain ⟨atom, atomConverted⟩ :=
    OptionMapM.list_mapM_option_exists_of_mem atomsObserved member
  exact (atomNodeToSemanticAtom?_isSome node).mp (by simp [atomConverted])

/-! ## Generic-substituent boundary -/

/-- A node list containing a generic substituent does not convert: no element is invented. -/
theorem mapM_atomNodeToSemanticAtom?_eq_none_of_mem_generic {nodes : List AtomNode}
    {node : AtomNode} (member : node ∈ nodes)
    (generic : node.element = .genericSubstituent) :
    nodes.mapM atomNodeToSemanticAtom? = none := by
  induction nodes with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [List.mapM_cons]
      rcases List.mem_cons.mp member with same | tailMember
      · subst node
        simp [atomNodeToSemanticAtom?, generic, atomElementToPeriodic?]
      · rw [inductionHypothesis tailMember]
        cases atomNodeToSemanticAtom? head <;> simp

/-- A graph containing a generic substituent node does not convert. -/
theorem heavyAtomGraphToAuthoritativeChemicalInput?_none_of_generic
    (graph : HeavyAtomGraph) {node : AtomNode}
    (member : node ∈ graph.nodes) (generic : node.element = .genericSubstituent) :
    heavyAtomGraphToAuthoritativeChemicalInput? graph = none := by
  unfold heavyAtomGraphToAuthoritativeChemicalInput?
  rw [mapM_atomNodeToSemanticAtom?_eq_none_of_mem_generic member generic]
  rfl

/-- Consequently such a candidate cannot be certified. -/
theorem AuthorityInputCandidate.certify?_eq_none_of_generic_node
    (candidate : AuthorityInputCandidate) {node : AtomNode}
    (member : node ∈ candidate.graph.nodes)
    (generic : node.element = .genericSubstituent) :
    candidate.certify? = none := by
  unfold AuthorityInputCandidate.certify?
  rw [heavyAtomGraphToAuthoritativeChemicalInput?_none_of_generic
    candidate.graph member generic]
  rfl

/-! ## Certified-input extraction -/

/-- A successful `certify?` exposes its input literally. -/
theorem AuthoritativeChemicalInput.certify?_input
    (input : AuthoritativeChemicalInput) (certified : CertifiedAuthoritativeChemicalInput)
    (converted : input.certify? = some certified) :
    certified.input = input := by
  unfold AuthoritativeChemicalInput.certify? at converted
  split at converted
  · cases converted
    rfl
  · simp at converted

/-- A certified input is structurally well formed in its own right. -/
theorem AuthoritativeChemicalInput.certify?_structurallyWellFormed
    (input : AuthoritativeChemicalInput) (certified : CertifiedAuthoritativeChemicalInput)
    (converted : input.certify? = some certified) :
    input.StructurallyWellFormed := by
  have wellFormed := certified.structurallyWellFormed
  rwa [AuthoritativeChemicalInput.certify?_input input certified converted] at wellFormed

/-- From an actual `AuthorityInputCandidate.certify? = some entry` success, extract the actual
graph-conversion witness and the `certify?` tie.  The final count equalities are re-derived from
the generic conversion exactness, never from the stored `CertifiedGraphAuthorityInput` fields. -/
theorem AuthorityInputCandidate.certify?_exact
    (candidate : AuthorityInputCandidate) (entry : CertifiedGraphAuthorityInput)
    (certified : candidate.certify? = some entry) :
    entry.candidate = candidate ∧
      heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph = some entry.certified.input ∧
      entry.certified.input.certify? = some entry.certified ∧
      entry.certified.input.StructurallyWellFormed ∧
      entry.certified.input.molecule.atoms.length = candidate.graph.nodes.length ∧
      entry.certified.input.molecule.interactions.length = candidate.graph.bonds.length := by
  unfold AuthorityInputCandidate.certify? at certified
  change (heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph).bind
      (fun input => (input.certify?).bind
        (fun certifiedInput =>
          if atomCountExact : certifiedInput.input.molecule.atoms.length =
              candidate.graph.nodes.length then
            if interactionCountExact : certifiedInput.input.molecule.interactions.length =
                candidate.graph.bonds.length then
              some { candidate := candidate, certified := certifiedInput,
                     atomCountExact := atomCountExact,
                     interactionCountExact := interactionCountExact }
            else none
          else none)) = some entry at certified
  rw [Option.bind_eq_some_iff] at certified
  obtain ⟨input, hconverted, certified⟩ := certified
  rw [Option.bind_eq_some_iff] at certified
  obtain ⟨certifiedInput, hcertified, hrest⟩ := certified
  split at hrest
  · rename_i atomCountCheck
    split at hrest
    · rename_i interactionCountCheck
      rw [Option.some.injEq] at hrest
      cases hrest
      have certifyExact : input.certify? = some certifiedInput := hcertified
      unfold AuthoritativeChemicalInput.certify? at hcertified
      split at hcertified
      · rw [Option.some.injEq] at hcertified
        cases hcertified
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using hconverted
        · simpa using certifyExact
        · exact AuthoritativeChemicalInput.certify?_structurallyWellFormed
            input _ certifyExact
        · simpa using heavyAtomGraphToAuthoritativeChemicalInput?_atoms_length
            candidate.graph input hconverted
        · simpa using heavyAtomGraphToAuthoritativeChemicalInput?_interactionCount
            candidate.graph input hconverted
      · simp at hcertified
    · simp at hrest
  · simp at hrest

/-- Projection: the actual conversion witness of a successful candidate certification. -/
theorem AuthorityInputCandidate.certify?_graph_conversion
    (candidate : AuthorityInputCandidate) (entry : CertifiedGraphAuthorityInput)
    (certified : candidate.certify? = some entry) :
    heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph = some entry.certified.input :=
  (AuthorityInputCandidate.certify?_exact candidate entry certified).2.1

/-- Projection: the certified input is literally the certified entry of its own `certify?`. -/
theorem AuthorityInputCandidate.certify?_certified_input_certify
    (candidate : AuthorityInputCandidate) (entry : CertifiedGraphAuthorityInput)
    (certified : candidate.certify? = some entry) :
    entry.certified.input.certify? = some entry.certified :=
  (AuthorityInputCandidate.certify?_exact candidate entry certified).2.2.1

/-! ## `?`-free guard aliases -/

theorem conversion_fields_exact
    (graph : HeavyAtomGraph) (input : AuthoritativeChemicalInput)
    (converted : heavyAtomGraphToAuthoritativeChemicalInput? graph = some input) :
    (∃ atoms : List SemanticAtom,
        graph.nodes.mapM atomNodeToSemanticAtom? = some atoms ∧
          input.molecule.atoms = atoms) ∧
      (∃ interactions : List SemanticInteraction,
        graph.bonds.mapM (graphBondToSemanticInteraction? graph) = some interactions ∧
          input.molecule.interactions = interactions) ∧
      input.spatial? = none ∧
      input.diagram? = none :=
  heavyAtomGraphToAuthoritativeChemicalInput?_fields graph input converted

theorem bond_conversion_exact (graph : HeavyAtomGraph)
    (bond : GraphBond) (interaction : SemanticInteraction)
    (converted : graphBondToSemanticInteraction? graph bond = some interaction) :
    ∃ low high,
      heavyAtomNodeIndex? graph bond.low = some low ∧
        heavyAtomNodeIndex? graph bond.high = some high ∧
        interaction.participants = [low, high] ∧
        interaction.kind = .covalent (bondOrderToNat bond.order) :=
  graphBondToSemanticInteraction?_exact graph bond interaction converted

theorem certify_entry_exact
    (candidate : AuthorityInputCandidate) (entry : CertifiedGraphAuthorityInput)
    (certified : candidate.certify? = some entry) :
    entry.candidate = candidate ∧
      heavyAtomGraphToAuthoritativeChemicalInput? candidate.graph = some entry.certified.input ∧
      entry.certified.input.certify? = some entry.certified ∧
      entry.certified.input.StructurallyWellFormed ∧
      entry.certified.input.molecule.atoms.length = candidate.graph.nodes.length ∧
      entry.certified.input.molecule.interactions.length = candidate.graph.bonds.length :=
  AuthorityInputCandidate.certify?_exact candidate entry certified

end FigureAuthorityInput
end Retinoid1981
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.conversion_fields_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.bond_conversion_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.certify_entry_exact
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.atomNodeToSemanticAtom?_defaults
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.heavyAtomNodeIndex?_complete_of_nodup
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.heavyAtomGraphToAuthoritativeChemicalInput?_atomAt?_exact_of_lt
assert_kernel_only
  TetraStereo.OneCenter.Retinoid1981.FigureAuthorityInput.heavyAtomGraphToAuthoritativeChemicalInput?_interactionAt?_exact_of_lt
