import Mathlib.Data.List.Infix
import TetraStereo.OneCenter.ProductionCIPOrdinarySoundness
import TetraStereo.OneCenter.CanonicalRule3Hierarchy

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

/-!
# Reifying production canonical keys as declarative rooted digraphs

The production compiler stores sparse sphere layers.  This module turns their positional paths
back into a finite, parent-preserving `DeclarativeCIP.RootedDigraph`.  Prefix closure is taken
explicitly, so the construction is total even for a hand-built sparse key; successfully compiled
keys already contain those parent paths.

The second half of the module is the Rules-3--5 semantic bridge.  Rule 3 is carried as an
addressed, typed `Rule3Signature` (a `layers : AddressedHierarchy Rule3Geometry` structure): the
derived accessor `ProductionRules35Key.rule3` projects the compiled
`CanonicalRule3Key.observations` layer-by-layer and address-by-address through
`OfficialRule3Geometry.toDeclarative`.  The ordinary executable trace continues to use the actual
sparse compiled priority layers (`rule3Key.rule3`) and never a parallel flat signature.  The
shared bridge `ProductionRules35Key.rule3_outcome_iff_compiled` identifies the declarative
addressed comparison with the sparse runtime comparison; this module independently verifies the
underlying projection comparison (`compareRule3ObservationSignatures_eq_sparse`) from the derived
alignment proof stored in each production key and the primitive geometry-priority agreement.
-/

namespace RawMolecule.CanonicalBranchKey

/-- Full source-node occurrences retained by the production compiler.

Compiled keys use the recursive occurrence witness, whose parent/child structure is intrinsic.
The flat field remains a backwards-compatible fallback for externally constructed sparse keys. -/
def addressedSources (key : CanonicalBranchKey) : List CanonicalSourceEntry :=
  match key.sourceTree? with
  | some tree => tree.occurrences
  | none => key.sourceOccurrences

/-- Unified atom/provenance occurrences retained by the production compiler. -/
def addressedNodes (key : CanonicalBranchKey) : List CanonicalNodeEntry :=
  key.addressedSources.map fun entry =>
    (entry.1, (entry.2.atom, entry.2.provenance))

/-- Every atom-bearing occurrence retained by the production compiler. -/
def addressedAtoms (key : CanonicalBranchKey) : List CanonicalNatEntry :=
  key.addressedNodes.map fun entry => (entry.1, entry.2.1)

/-- Every provenance-bearing occurrence retained by the production compiler. -/
def addressedProvenance (key : CanonicalBranchKey) : List CanonicalProvenanceEntry :=
  key.addressedNodes.map fun entry => (entry.1, entry.2.2)

/-- Atom and provenance projections have exactly the same positional paths. -/
theorem addressedAtoms_paths_eq_addressedProvenance_paths (key : CanonicalBranchKey) :
    key.addressedAtoms.map Prod.fst = key.addressedProvenance.map Prod.fst := by
  simp [addressedAtoms, addressedProvenance]

/-- Finite prefix closure of every production positional path. -/
def hierarchyAddresses (key : CanonicalBranchKey) : List (List ℕ) :=
  [] :: key.addressedAtoms.flatMap fun entry => entry.1.inits

/-- Exact carrier characterization: converted nodes are the root and precisely the prefixes of
positions present in the unified production node table. -/
theorem mem_hierarchyAddresses_iff (key : CanonicalBranchKey) (address : List ℕ) :
    address ∈ key.hierarchyAddresses ↔
      address = [] ∨ ∃ entry ∈ key.addressedNodes, address <+: entry.1 := by
  simp [hierarchyAddresses, addressedAtoms, List.mem_inits]

@[simp] theorem nil_mem_hierarchyAddresses (key : CanonicalBranchKey) :
    [] ∈ key.hierarchyAddresses := by
  simp [hierarchyAddresses]

theorem dropLast_mem_hierarchyAddresses (key : CanonicalBranchKey)
    {address : List ℕ} (haddress : address ∈ key.hierarchyAddresses) :
    address.dropLast ∈ key.hierarchyAddresses := by
  simp only [hierarchyAddresses, List.mem_cons, List.mem_flatMap] at haddress ⊢
  rcases haddress with hnil | ⟨entry, hentry, hprefix⟩
  · subst address
    exact Or.inl rfl
  · refine Or.inr ⟨entry, hentry, ?_⟩
    rw [List.mem_inits] at hprefix ⊢
    exact address.dropLast_prefix.trans hprefix

/-- Nodes are canonical positional paths, not array indices or atom identities. -/
abbrev HierarchyNode (key : CanonicalBranchKey) :=
  { address : List ℕ // address ∈ key.hierarchyAddresses }

private noncomputable instance hierarchyNodeFintype (key : CanonicalBranchKey) :
    Fintype key.HierarchyNode := by
  classical
  exact Fintype.ofList key.hierarchyAddresses.attach (by intro node; simp)

/-- Full production source node at a positional path. -/
def sourceNodeAtAddress? (key : CanonicalBranchKey) (address : List ℕ) :
    Option CanonicalBranchNode :=
  match key.sourceTree? with
  | some tree => tree.sourceAt? address
  | none => (key.addressedSources.find? fun entry => entry.1 == address).map Prod.snd

/-- Unified atom/provenance witness at a positional path. -/
def nodeAtAddress? (key : CanonicalBranchKey) (address : List ℕ) :
    Option (ℕ × CanonicalNodeProvenance) :=
  (key.sourceNodeAtAddress? address).map fun node => (node.atom, node.provenance)

/-- Atom identity at a positional path, when the production table contains it. -/
def atomAtAddress? (key : CanonicalBranchKey) (address : List ℕ) : Option ℕ :=
  (key.nodeAtAddress? address).map Prod.fst

/-- Production provenance at a positional path. -/
def provenanceAtAddress? (key : CanonicalBranchKey) (address : List ℕ) :
    Option CanonicalNodeProvenance :=
  (key.nodeAtAddress? address).map Prod.snd

/-- Lookup cannot mix an atom from one occurrence with provenance from another occurrence. -/
theorem nodeAtAddress?_eq_some_iff (key : CanonicalBranchKey) (address : List ℕ)
    (atom : ℕ) (provenance : CanonicalNodeProvenance) :
    key.nodeAtAddress? address = some (atom, provenance) ↔
      key.atomAtAddress? address = some atom ∧
        key.provenanceAtAddress? address = some provenance := by
  unfold atomAtAddress? provenanceAtAddress?
  cases hlookup : key.nodeAtAddress? address with
  | none => simp
  | some value =>
      rcases value with ⟨foundAtom, foundProvenance⟩
      simp

@[simp] theorem canonicalRootKey_sourceNodeAtAddress_nil (mol : RawMolecule)
    (node : CanonicalBranchNode) (complete : Bool) :
    (mol.canonicalRootKey node complete).sourceNodeAtAddress? [] = some node := by
  rfl

@[simp] theorem canonicalRootKey_nodeAtAddress_nil (mol : RawMolecule)
    (node : CanonicalBranchNode) (complete : Bool) :
    (mol.canonicalRootKey node complete).nodeAtAddress? [] =
      some (node.atom, node.provenance) := by
  simp [nodeAtAddress?, canonicalRootKey_sourceNodeAtAddress_nil]

/-- Convert production provenance without losing duplicate-root distances. -/
def declarativeProvenance : CanonicalNodeProvenance → NodeProvenance
  | .realAtom => .realAtom
  | .multipleBondDuplicate distance => .multipleBondDuplicate distance
  | .ringDuplicate distance => .ringDuplicate distance
  | .phantom distance => .phantom distance

/-- Checked conversion of a parser atom index into the proof-facing finite atom type. -/
def atomFin? (mol : RawMolecule) (atom : ℕ) : Option (Fin mol.atomCount) :=
  if h : atom < mol.atomCount then some ⟨atom, h⟩ else none

/-- Semantic node label reconstructed from the production atom/provenance tables.

Prefix nodes absent from a malformed hand-built table become explicit phantoms.  Production keys
populate both tables at every represented node; later correspondence theorems expose that fact as
a checkable invariant. -/
def declarativeLabel (mol : RawMolecule) (key : CanonicalBranchKey)
    (node : key.HierarchyNode) : NodeLabel (Fin mol.atomCount) :=
  match key.sourceNodeAtAddress? node.1 with
  | some source =>
      match source.provenance with
      | .phantom distance => ⟨none, .phantom distance⟩
      | provenance => ⟨atomFin? mol source.atom, declarativeProvenance provenance⟩
  | none => ⟨none, .phantom node.1.length⟩

/-- Immediate parenthood is extension by one canonical sibling slot. -/
def HierarchyChild (key : CanonicalBranchKey)
    (parent node : key.HierarchyNode) : Prop :=
  ∃ slot, node.1 = parent.1 ++ [slot]

theorem hierarchyChild_parent_unique (key : CanonicalBranchKey)
    {first second node : key.HierarchyNode}
    (hfirst : key.HierarchyChild first node)
    (hsecond : key.HierarchyChild second node) :
    first = second := by
  rcases hfirst with ⟨firstSlot, hfirst⟩
  rcases hsecond with ⟨secondSlot, hsecond⟩
  apply Subtype.ext
  have hfirstDrop : node.1.dropLast = first.1 := by simp [hfirst]
  have hsecondDrop : node.1.dropLast = second.1 := by simp [hsecond]
  exact hfirstDrop.symm.trans hsecondDrop

theorem hierarchyRoot_has_no_parent (key : CanonicalBranchKey)
    (parent : key.HierarchyNode) :
    ¬key.HierarchyChild parent ⟨[], key.nil_mem_hierarchyAddresses⟩ := by
  rintro ⟨slot, hslot⟩
  have hlength := congrArg List.length hslot
  simp at hlength

theorem hierarchyReachable (key : CanonicalBranchKey)
    (address : List ℕ) (haddress : address ∈ key.hierarchyAddresses) :
    Relation.ReflTransGen key.HierarchyChild
      ⟨[], key.nil_mem_hierarchyAddresses⟩ ⟨address, haddress⟩ := by
  induction address using List.reverseRecOn with
  | nil => exact .refl
  | append_singleton address slot inductionHypothesis =>
      have hparent : address ∈ key.hierarchyAddresses := by
        have := key.dropLast_mem_hierarchyAddresses haddress
        simpa using this
      exact (inductionHypothesis hparent).tail ⟨slot, rfl⟩

/-- Total finite rooted-digraph conversion of a production canonical branch key. -/
def toDeclarativeDigraph (mol : RawMolecule) (key : CanonicalBranchKey) :
    RootedDigraph (Fin mol.atomCount) where
  Node := key.HierarchyNode
  nodeFintype := hierarchyNodeFintype key
  root := ⟨[], key.nil_mem_hierarchyAddresses⟩
  child := key.HierarchyChild
  label := key.declarativeLabel mol
  depth := fun node => node.1.length
  root_depth := rfl
  child_depth := by
    rintro parent node ⟨slot, hnode⟩
    rw [hnode]
    simp
  reachable := by
    intro node
    exact key.hierarchyReachable node.1 node.2

@[simp] theorem toDeclarativeDigraph_root_address (mol : RawMolecule)
    (key : CanonicalBranchKey) :
    (key.toDeclarativeDigraph mol).root.1 = [] :=
  rfl

/-- The canonical production paths form an admissible declarative addressing. -/
def declarativeAddressing (mol : RawMolecule) (key : CanonicalBranchKey) :
    (key.toDeclarativeDigraph mol).Addressing where
  address := fun node => node.1
  address_injective := Subtype.val_injective
  root_address := rfl
  child_iff := by
    intro parent node
    rfl

@[simp] theorem declarativeAddressing_address (mol : RawMolecule)
    (key : CanonicalBranchKey) (node : (key.toDeclarativeDigraph mol).Node) :
    (key.declarativeAddressing mol).address node = node.1 :=
  rfl

theorem toDeclarativeDigraph_finite (mol : RawMolecule) (key : CanonicalBranchKey) :
    Finite (key.toDeclarativeDigraph mol).Node := by
  change Finite key.HierarchyNode
  letI : Fintype key.HierarchyNode := hierarchyNodeFintype key
  infer_instance

theorem toDeclarativeDigraph_child_wellFounded (mol : RawMolecule)
    (key : CanonicalBranchKey) :
    WellFounded (key.toDeclarativeDigraph mol).child :=
  (key.toDeclarativeDigraph mol).child_wellFounded

end RawMolecule.CanonicalBranchKey

/-! ## Production observations on the converted hierarchy -/

namespace ProductionCIPHierarchy

def rule4aLayersToDeclarative
    (layers : List (List (List ℕ × OfficialStereogenicUnitKind))) :
    AddressedHierarchy StereogenicUnitKind :=
  layers.map fun layer => layer.map fun entry =>
    (entry.1, entry.2.toDeclarative)

/-! ### Derived addressed Rule-3 semantic projection

The compiled Rule-3 evidence is stored in `rule3Key.observations`, a sparse hierarchy of addressed
official geometry observations.  The declarative signature preserves every layer and every
positional address and only translates the primitive geometry class.  Nothing about the sparse
priority layers is cached here; the projection is a pure semantic translation.
-/

/-- Translate one compiled observation entry to the declarative addressed geometry entry. -/
def rule3EntryToDeclarative
    (entry : List ℕ × RawMolecule.CanonicalRule3Observation) :
    List ℕ × Rule3Geometry :=
  (entry.1, entry.2.geometry.toDeclarative)

/-- The compiled priority of one observation entry, in addressed form. -/
def rule3EntryPriority
    (entry : List ℕ × RawMolecule.CanonicalRule3Observation) :
    List ℕ × ℕ :=
  (entry.1, RawMolecule.CanonicalRule3Observation.priority entry.2)

/-- Translate one compiled observation layer to the declarative addressed geometry layer. -/
def rule3ObservationLayerToDeclarative
    (layer : List (List ℕ × RawMolecule.CanonicalRule3Observation)) :
    List (List ℕ × Rule3Geometry) :=
  layer.map rule3EntryToDeclarative

/-- The priority layer of one compiled observation layer, with addresses preserved. -/
def rule3ObservationLayerPriority
    (layer : List (List ℕ × RawMolecule.CanonicalRule3Observation)) :
    List (List ℕ × ℕ) :=
  layer.map rule3EntryPriority

/-- Translate a whole compiled observation hierarchy to the declarative addressed hierarchy. -/
def rule3ObservationLayersToDeclarative
    (layers : List (List (List ℕ × RawMolecule.CanonicalRule3Observation))) :
    AddressedHierarchy Rule3Geometry :=
  layers.map rule3ObservationLayerToDeclarative

/-- The priority hierarchy of a whole compiled observation hierarchy. -/
def rule3ObservationLayersPriority
    (layers : List (List (List ℕ × RawMolecule.CanonicalRule3Observation))) :
    List (List (List ℕ × ℕ)) :=
  layers.map rule3ObservationLayerPriority

/-- The priority projection of one observation layer is exactly the compiled sparse layer
projection used by `CanonicalRule3Key.Rule3Aligned`. -/
theorem rule3ObservationLayerPriority_eq_map
    (layer : List (List ℕ × RawMolecule.CanonicalRule3Observation)) :
    rule3ObservationLayerPriority layer =
      RawMolecule.mapObservationPriorityLayer layer :=
  rfl

/-- The priority projection of a whole observation hierarchy is exactly the compiled sparse
projection used by `CanonicalRule3Key.Rule3Aligned`. -/
theorem rule3ObservationLayersPriority_eq_map
    (layers : List (List (List ℕ × RawMolecule.CanonicalRule3Observation))) :
    rule3ObservationLayersPriority layers =
      RawMolecule.mapObservationPriorityLayers layers := by
  simp only [rule3ObservationLayersPriority, RawMolecule.mapObservationPriorityLayers]
  apply List.map_congr_left
  intro layer _
  exact rule3ObservationLayerPriority_eq_map layer

/-- Semantic Rules 3--5 evidence read from one opponent-independent production key.

Rules 3 and 4b are complete unary signatures and therefore live at the hierarchy root.  Rules 4a,
4c, and 5 retain their node-addressed sparse observations.  The Rule-3 field is the typed,
addressed declarative signature derived from the compiled observation evidence. -/
def evidence (compiled : ProductionRules35Key)
    {mol : RawMolecule} {hierarchy : RawMolecule.CanonicalBranchKey}
    (node : (hierarchy.toDeclarativeDigraph mol).Node) : StereochemicalObservation :=
  let root := node.1 = []
  { rule3 := if root then some compiled.rule3 else none
    rule4a := if root then some ⟨rule4aLayersToDeclarative compiled.rule4a⟩ else none
    rule4b := if root then some ⟨compiled.rule4b⟩ else none
    rule4c := if root then some ⟨compiled.rule4c⟩ else none
    rule5 := if root then some ⟨compiled.rule5⟩ else none }

/-- The observation at a semantic address under the canonical converted addressing. -/
def observationAtPosition (compiled : ProductionRules35Key)
    (mol : RawMolecule) (hierarchy : RawMolecule.CanonicalBranchKey)
    (position : List ℕ) : Option StereochemicalObservation :=
  if h : position ∈ hierarchy.hierarchyAddresses then
    some (evidence compiled (mol := mol) (hierarchy := hierarchy) ⟨position, h⟩)
  else none

theorem observationAt_iff_eq_observationAtPosition
    (compiled : ProductionRules35Key) (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey) (position : List ℕ)
    (observation : Option StereochemicalObservation) :
    RootedDigraph.Addressing.ObservationAt
        (hierarchy.toDeclarativeDigraph mol) (hierarchy.declarativeAddressing mol)
        (evidence compiled) position observation ↔
      observation = observationAtPosition compiled mol hierarchy position := by
  classical
  by_cases hposition : position ∈ hierarchy.hierarchyAddresses
  · constructor
    · intro h
      cases observation with
      | none =>
          exact False.elim (h ⟨position, hposition⟩ rfl)
      | some observation =>
          rcases h with ⟨node, hnode, hevidence⟩
          have hnodeEq : node = ⟨position, hposition⟩ := by
            apply Subtype.ext
            exact hnode
          subst node
          simp [observationAtPosition, hposition, hevidence]
    · intro h
      simp [observationAtPosition, hposition] at h
      subst observation
      exact ⟨⟨position, hposition⟩, rfl, rfl⟩
  · constructor
    · intro h
      cases observation with
      | none => simp [observationAtPosition, hposition]
      | some observation =>
          rcases h with ⟨node, hnode, _⟩
          exact False.elim (hposition (hnode ▸ node.2))
    · intro h
      simp [observationAtPosition, hposition] at h
      subst observation
      intro node hnode
      exact hposition (hnode ▸ node.2)

theorem stereochemicalOutcomeAt_iff_nodeOutcome
    (compiledLeft compiledRight : ProductionRules35Key)
    (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (rule : StereochemicalRule) (position : List ℕ) (outcome : Ordering) :
    StereochemicalOutcomeAt rule
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence compiledLeft)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence compiledRight) position outcome ↔
      StereochemicalNodeOutcome rule
        (observationAtPosition compiledLeft mol leftHierarchy position)
        (observationAtPosition compiledRight mol rightHierarchy position) outcome := by
  constructor
  · rintro ⟨leftObservation, rightObservation, hleft, hright, houtcome⟩
    have hleftEq := (observationAt_iff_eq_observationAtPosition
      compiledLeft mol leftHierarchy position leftObservation).1 hleft
    have hrightEq := (observationAt_iff_eq_observationAtPosition
      compiledRight mol rightHierarchy position rightObservation).1 hright
    simpa [hleftEq, hrightEq] using houtcome
  · intro houtcome
    exact ⟨observationAtPosition compiledLeft mol leftHierarchy position,
      observationAtPosition compiledRight mol rightHierarchy position,
      (observationAt_iff_eq_observationAtPosition _ _ _ _ _).2 rfl,
      (observationAt_iff_eq_observationAtPosition _ _ _ _ _).2 rfl,
      houtcome⟩

private theorem observationAt_bind_rootField
    {β : Type*} (compiled : ProductionRules35Key) (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey)
    (addressing : (hierarchy.toDeclarativeDigraph mol).Addressing)
    (field : StereochemicalObservation → Option β) (rootValue : β)
    (hroot : field (evidence compiled (hierarchy.toDeclarativeDigraph mol).root) = some rootValue)
    (hnonroot : ∀ node, node ≠ (hierarchy.toDeclarativeDigraph mol).root →
      field (evidence compiled node) = none)
    (position : List ℕ) (observation : Option StereochemicalObservation)
    (hobservation : RootedDigraph.Addressing.ObservationAt
      (hierarchy.toDeclarativeDigraph mol) addressing (evidence compiled)
      position observation) :
    observation.bind field = if position = [] then some rootValue else none := by
  by_cases hposition : position = []
  · subst position
    cases observation with
    | none =>
        exact False.elim (hobservation _ addressing.root_address)
    | some observation =>
        rcases hobservation with ⟨node, hnode, hevidence⟩
        have hnodeRoot : node = (hierarchy.toDeclarativeDigraph mol).root :=
          addressing.address_injective (hnode.trans addressing.root_address.symm)
        subst node
        simp [← hevidence, hroot]
  · cases observation with
    | none => simp [hposition]
    | some observation =>
        rcases hobservation with ⟨node, hnode, hevidence⟩
        have hnodeNotRoot : node ≠ (hierarchy.toDeclarativeDigraph mol).root := by
          intro hnodeRoot
          subst node
          exact hposition (hnode.symm.trans addressing.root_address)
        simp [← hevidence, hposition, hnonroot node hnodeNotRoot]

private theorem evidence_field_none_of_ne_root
    (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey)
    (node : (hierarchy.toDeclarativeDigraph mol).Node)
    (hnode : node ≠ (hierarchy.toDeclarativeDigraph mol).root) :
    node.1 ≠ [] := by
  intro hnil
  apply hnode
  apply Subtype.ext
  exact hnil

private theorem outcomeAt_iff_rootOnly
    {α : Type*} (relation : α → α → Ordering → Prop)
    (field : StereochemicalObservation → Option α) (rule : StereochemicalRule)
    (nodeOutcome : ∀ left right outcome,
      StereochemicalNodeOutcome rule left right outcome ↔
        OptionalOutcome relation (left.bind field) (right.bind field) outcome)
    (leftValue rightValue : α)
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (leftAddressing : (leftHierarchy.toDeclarativeDigraph mol).Addressing)
    (rightAddressing : (rightHierarchy.toDeclarativeDigraph mol).Addressing)
    (hleftRoot : field (evidence leftKey (leftHierarchy.toDeclarativeDigraph mol).root) =
      some leftValue)
    (hrightRoot : field (evidence rightKey (rightHierarchy.toDeclarativeDigraph mol).root) =
      some rightValue)
    (hleftOther : ∀ node, node ≠ (leftHierarchy.toDeclarativeDigraph mol).root →
      field (evidence leftKey node) = none)
    (hrightOther : ∀ node, node ≠ (rightHierarchy.toDeclarativeDigraph mol).root →
      field (evidence rightKey node) = none)
    (position : List ℕ) (outcome : Ordering) :
    StereochemicalOutcomeAt rule
        (leftHierarchy.toDeclarativeDigraph mol) leftAddressing (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) rightAddressing (evidence rightKey)
        position outcome ↔
      OptionalOutcome relation
        (if position = [] then some leftValue else none)
        (if position = [] then some rightValue else none) outcome := by
  constructor
  · rintro ⟨leftObservation, rightObservation, hleft, hright, houtcome⟩
    have hleftBind := observationAt_bind_rootField leftKey mol leftHierarchy leftAddressing
      field leftValue hleftRoot hleftOther position leftObservation hleft
    have hrightBind := observationAt_bind_rootField rightKey mol rightHierarchy rightAddressing
      field rightValue hrightRoot hrightOther position rightObservation hright
    rw [nodeOutcome] at houtcome
    simpa [hleftBind, hrightBind] using houtcome
  · intro houtcome
    rcases RootedDigraph.Addressing.observationAt_exists
      (leftHierarchy.toDeclarativeDigraph mol) leftAddressing (evidence leftKey) position with
      ⟨leftObservation, hleft⟩
    rcases RootedDigraph.Addressing.observationAt_exists
      (rightHierarchy.toDeclarativeDigraph mol) rightAddressing (evidence rightKey) position with
      ⟨rightObservation, hright⟩
    have hleftBind := observationAt_bind_rootField leftKey mol leftHierarchy leftAddressing
      field leftValue hleftRoot hleftOther position leftObservation hleft
    have hrightBind := observationAt_bind_rootField rightKey mol rightHierarchy rightAddressing
      field rightValue hrightRoot hrightOther position rightObservation hright
    refine ⟨leftObservation, rightObservation, hleft, hright, (nodeOutcome _ _ _).2 ?_⟩
    simpa [hleftBind, hrightBind] using houtcome

theorem observationAtPosition_bind_rule3
    (compiled : ProductionRules35Key) (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey) (position : List ℕ) :
    (observationAtPosition compiled mol hierarchy position).bind (·.rule3) =
      if position = [] then some compiled.rule3 else none := by
  classical
  by_cases hposition : position ∈ hierarchy.hierarchyAddresses <;>
    by_cases hroot : position = [] <;>
    simp [observationAtPosition, evidence, hposition, hroot]

theorem observationAtPosition_bind_rule4b
    (compiled : ProductionRules35Key) (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey) (position : List ℕ) :
    (observationAtPosition compiled mol hierarchy position).bind (·.rule4b) =
      if position = [] then some ⟨compiled.rule4b⟩ else none := by
  classical
  by_cases hposition : position ∈ hierarchy.hierarchyAddresses <;>
    by_cases hroot : position = [] <;>
    simp [observationAtPosition, evidence, hposition, hroot]

theorem observationAtPosition_bind_rule4a
    (compiled : ProductionRules35Key) (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey) (position : List ℕ) :
    (observationAtPosition compiled mol hierarchy position).bind (·.rule4a) =
      if position = [] then some ⟨rule4aLayersToDeclarative compiled.rule4a⟩ else none := by
  classical
  by_cases hposition : position ∈ hierarchy.hierarchyAddresses <;>
    by_cases hroot : position = [] <;>
    simp [observationAtPosition, evidence, hposition, hroot]

theorem observationAtPosition_bind_rule4c
    (compiled : ProductionRules35Key) (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey) (position : List ℕ) :
    (observationAtPosition compiled mol hierarchy position).bind (·.rule4c) =
      if position = [] then some ⟨compiled.rule4c⟩ else none := by
  classical
  by_cases hposition : position ∈ hierarchy.hierarchyAddresses <;>
    by_cases hroot : position = [] <;>
    simp [observationAtPosition, evidence, hposition, hroot]

theorem observationAtPosition_bind_rule5
    (compiled : ProductionRules35Key) (mol : RawMolecule)
    (hierarchy : RawMolecule.CanonicalBranchKey) (position : List ℕ) :
    (observationAtPosition compiled mol hierarchy position).bind (·.rule5) =
      if position = [] then some ⟨compiled.rule5⟩ else none := by
  classical
  by_cases hposition : position ∈ hierarchy.hierarchyAddresses <;>
    by_cases hroot : position = [] <;>
    simp [observationAtPosition, evidence, hposition, hroot]

private theorem listCompareLex_map {α β : Type*}
    (mapValue : α → β) (compareSource : α → α → Ordering)
    (compareTarget : β → β → Ordering)
    (hcompare : ∀ left right,
      compareTarget (mapValue left) (mapValue right) = compareSource left right) :
    ∀ left right,
      List.compareLex compareTarget (left.map mapValue) (right.map mapValue) =
        List.compareLex compareSource left right := by
  intro left
  induction left with
  | nil => intro right; cases right <;> rfl
  | cons head tail inductionHypothesis =>
      intro right
      cases right with
      | nil => rfl
      | cons other others =>
          simp only [List.map_cons, List.compareLex]
          rw [hcompare]
          cases compareSource head other <;> simp [inductionHypothesis]

/-! ### Primitive geometry-priority agreement and the sparse bridge -/

/-- The declarative geometry retains the official Rule-3 priority. -/
theorem rule3Geometry_priority_toDeclarative (geometry : OfficialRule3Geometry) :
    Rule3Geometry.priority geometry.toDeclarative = OfficialRule3Geometry.priority geometry := by
  cases geometry <;> rfl

/-- Addressed comparison of one declarative geometry entry agrees with sparse comparison of the
compiled observation priority entry at the same address. -/
theorem compareRule3Entry_toDeclarative
    (left right : List ℕ × RawMolecule.CanonicalRule3Observation) :
    compareAddressedEntry Rule3Geometry.priority
        (rule3EntryToDeclarative left) (rule3EntryToDeclarative right) =
      RawMolecule.compareSparseCanonicalEntry compare
        (rule3EntryPriority left) (rule3EntryPriority right) := by
  rcases left with ⟨leftPath, leftObservation⟩
  rcases right with ⟨rightPath, rightObservation⟩
  change compareAddressedEntry Rule3Geometry.priority
      (leftPath, leftObservation.geometry.toDeclarative)
      (rightPath, rightObservation.geometry.toDeclarative) =
    RawMolecule.compareSparseCanonicalEntry compare
      (leftPath, RawMolecule.CanonicalRule3Observation.priority leftObservation)
      (rightPath, RawMolecule.CanonicalRule3Observation.priority rightObservation)
  unfold compareAddressedEntry RawMolecule.compareSparseCanonicalEntry
    compareSemanticAddress RawMolecule.compareCanonicalPath Ordering.byKey
  have hkind :
      compare (Rule3Geometry.priority leftObservation.geometry.toDeclarative)
          (Rule3Geometry.priority rightObservation.geometry.toDeclarative) =
        compare (RawMolecule.CanonicalRule3Observation.priority leftObservation)
          (RawMolecule.CanonicalRule3Observation.priority rightObservation) := by
    simp only [rule3Geometry_priority_toDeclarative]
    rfl
  unfold compareLex
  cases hpath : List.compareLex compare rightPath leftPath <;> simp [hkind]

/-- Layerwise agreement of the declarative addressed geometry comparison and the sparse compiled
priority comparison. -/
theorem compareRule3Layer_toDeclarative
    (left right : List (List ℕ × RawMolecule.CanonicalRule3Observation)) :
    compareAddressedLayer Rule3Geometry.priority
        (rule3ObservationLayerToDeclarative left)
        (rule3ObservationLayerToDeclarative right) =
      RawMolecule.compareSparseCanonicalLayer compare
        (rule3ObservationLayerPriority left) (rule3ObservationLayerPriority right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons other others =>
          simp only [compareAddressedLayer, RawMolecule.compareSparseCanonicalLayer,
            rule3ObservationLayerToDeclarative, rule3ObservationLayerPriority]
            at inductionHypothesis
          simp only [rule3ObservationLayerToDeclarative, rule3ObservationLayerPriority,
            List.map_cons, compareAddressedLayer, RawMolecule.compareSparseCanonicalLayer,
            List.compareLex_cons_cons]
          rw [compareRule3Entry_toDeclarative head other, inductionHypothesis others]

/-- Sphere-major agreement of the declarative addressed geometry comparison and the sparse
compiled priority comparison. -/
theorem compareRule3Layers_toDeclarative
    (left right : List (List (List ℕ × RawMolecule.CanonicalRule3Observation))) :
    compareAddressedHierarchy Rule3Geometry.priority
        (rule3ObservationLayersToDeclarative left)
        (rule3ObservationLayersToDeclarative right) =
      RawMolecule.compareSparseCanonicalLayers compare
        (rule3ObservationLayersPriority left) (rule3ObservationLayersPriority right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons other others =>
          simp only [compareAddressedHierarchy, rule3ObservationLayersToDeclarative,
            rule3ObservationLayersPriority] at inductionHypothesis
          simp only [rule3ObservationLayersToDeclarative, rule3ObservationLayersPriority,
            List.map_cons, compareAddressedHierarchy, RawMolecule.compareSparseCanonicalLayers,
            List.compareLex_cons_cons]
          rw [compareRule3Layer_toDeclarative head other, inductionHypothesis others]
          rfl

/-- **Load-bearing bridge.**  The declarative addressed comparison of the raw compiled
observation hierarchy is exactly the ordinary sparse comparison of the compiled priority layers.

Only two facts are used: the primitive geometry-priority agreement and the derived alignment proof
`key.rule3Aligned` stored in each successfully produced key.  No flat-signature semantics and no
numeric output codec are involved.  (Owner A's derived accessor `key.rule3` is stated by the
shared contract to have exactly `rule3ObservationLayersToDeclarative key.rule3Key.observations`
as its `layers` field; this theorem is the independent verification of the comparison bridge.) -/
theorem compareRule3ObservationSignatures_eq_sparse (left right : ProductionRules35Key) :
    compareAddressedHierarchy Rule3Geometry.priority
        (rule3ObservationLayersToDeclarative left.rule3Key.observations)
        (rule3ObservationLayersToDeclarative right.rule3Key.observations) =
      RawMolecule.compareSparseCanonicalLayers compare
        left.rule3Key.rule3 right.rule3Key.rule3 := by
  rw [compareRule3Layers_toDeclarative]
  simp only [rule3ObservationLayersPriority_eq_map]
  have hleft : RawMolecule.mapObservationPriorityLayers left.rule3Key.observations =
      left.rule3Key.rule3 := left.rule3Aligned
  have hright : RawMolecule.mapObservationPriorityLayers right.rule3Key.observations =
      right.rule3Key.rule3 := right.rule3Aligned
  rw [hleft, hright]

private theorem compareRule4aEntry_toDeclarative
    (left right : List ℕ × OfficialStereogenicUnitKind) :
    compareAddressedEntry StereogenicUnitKind.priority
        (left.1, left.2.toDeclarative) (right.1, right.2.toDeclarative) =
      RawMolecule.compareSparseCanonicalEntry OfficialStereogenicUnitKind.compare left right := by
  rcases left with ⟨leftPath, leftKind⟩
  rcases right with ⟨rightPath, rightKind⟩
  unfold compareAddressedEntry RawMolecule.compareSparseCanonicalEntry
    compareSemanticAddress RawMolecule.compareCanonicalPath Ordering.byKey
  have hkind :
      compare (StereogenicUnitKind.priority leftKind.toDeclarative)
          (StereogenicUnitKind.priority rightKind.toDeclarative) =
        OfficialStereogenicUnitKind.compare leftKind rightKind := by
    cases leftKind <;> cases rightKind <;>
      simp [OfficialStereogenicUnitKind.compare, comparePriorityNat_eq_compare,
        OfficialStereogenicUnitKind.priority, OfficialStereogenicUnitKind.toDeclarative,
        StereogenicUnitKind.priority]
  unfold compareLex
  cases hpath : List.compareLex compare rightPath leftPath <;>
    simp [hkind]

theorem compareRule4aLayers_toDeclarative (left right :
    List (List (List ℕ × OfficialStereogenicUnitKind))) :
    compareAddressedHierarchy StereogenicUnitKind.priority
        (rule4aLayersToDeclarative left) (rule4aLayersToDeclarative right) =
      RawMolecule.compareSparseCanonicalLayers OfficialStereogenicUnitKind.compare left right := by
  unfold rule4aLayersToDeclarative compareAddressedHierarchy
    RawMolecule.compareSparseCanonicalLayers
  apply listCompareLex_map
  intro leftLayer rightLayer
  unfold compareAddressedLayer RawMolecule.compareSparseCanonicalLayer
  apply listCompareLex_map
  exact compareRule4aEntry_toDeclarative

theorem compareRule4cLayers_toDeclarative
    (left right : List (List (List ℕ × ℕ))) :
    compareAddressedHierarchy id left right =
      RawMolecule.compareSparseCanonicalLayers compare left right := by
  rfl

theorem compareRule5Layers_toDeclarative
    (left right : List (List (List ℕ × ℕ))) :
    compareAddressedHierarchy id left right =
      RawMolecule.compareSparseCanonicalLayers compare left right := by
  rfl

private theorem not_addressBefore_nil (address : List ℕ) :
    ¬HierarchyAddressBefore address [] := by
  cases address <;>
    simp [HierarchyAddressBefore, HierarchyAddressKey, List.cons_lt_cons_iff]

private theorem rootOnlyHierarchyOutcome_iff
    {α : Type*} (relation : α → α → Ordering → Prop)
    (relationFunctional : ∀ left right first second,
      relation left right first → relation left right second → first = second)
    (relationTotal : ∀ left right, ∃ outcome, relation left right outcome)
    (leftValue rightValue : α)
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (leftAddressing : (leftHierarchy.toDeclarativeDigraph mol).Addressing)
    (rightAddressing : (rightHierarchy.toDeclarativeDigraph mol).Addressing)
    (rule : StereochemicalRule)
    (localOutcome : ∀ position outcome,
      StereochemicalOutcomeAt rule
          (leftHierarchy.toDeclarativeDigraph mol) leftAddressing
          (evidence leftKey)
          (rightHierarchy.toDeclarativeDigraph mol) rightAddressing
          (evidence rightKey) position outcome ↔
        OptionalOutcome relation
          (if position = [] then some leftValue else none)
          (if position = [] then some rightValue else none) outcome)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule
        (leftHierarchy.toDeclarativeDigraph mol) leftAddressing
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) rightAddressing
        (evidence rightKey) outcome ↔
      relation leftValue rightValue outcome := by
  rcases relationTotal leftValue rightValue with ⟨decision, hdecision⟩
  have hcanonical :
      StereochemicalHierarchyOutcome rule
        (leftHierarchy.toDeclarativeDigraph mol) leftAddressing
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) rightAddressing
        (evidence rightKey) decision := by
    cases decision with
    | lt =>
        refine ⟨[], (localOutcome [] Ordering.lt).2 (OptionalOutcome.both hdecision), ?_⟩
        intro earlier hearlier
        exact False.elim (not_addressBefore_nil earlier hearlier)
    | eq =>
        intro position
        by_cases hroot : position = []
        · subst position
          exact (localOutcome [] Ordering.eq).2 (OptionalOutcome.both hdecision)
        · exact (localOutcome position Ordering.eq).2 (by
            simp only [hroot, ↓reduceIte]
            exact OptionalOutcome.neither)
    | gt =>
        refine ⟨[], (localOutcome [] Ordering.gt).2 (OptionalOutcome.both hdecision), ?_⟩
        intro earlier hearlier
        exact False.elim (not_addressBefore_nil earlier hearlier)
  constructor
  · intro h
    have heq := stereochemicalHierarchyOutcome_functional rule
      (leftHierarchy.toDeclarativeDigraph mol) leftAddressing
      (evidence leftKey)
      (rightHierarchy.toDeclarativeDigraph mol) rightAddressing
      (evidence rightKey) h hcanonical
    subst outcome
    exact hdecision
  · intro h
    have heq := relationFunctional leftValue rightValue outcome decision h hdecision
    subst outcome
    exact hcanonical

/-- The converted hierarchy's declarative Rule-3 judgment is exactly comparison of the complete
opponent-independent production signatures, using the actual sparse compiled priority layers.

The declarative side compares the typed addressed geometry signature at the root; the executable
side compares `rule3Key.rule3`.  The two coincide by the shared
`ProductionRules35Key.rule3_outcome_iff_compiled` bridge (whose content is independently verified
here as `compareRule3ObservationSignatures_eq_sparse`). -/
theorem rule3HierarchyOutcome_iff
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome StereochemicalRule.rule3DoubleBondGeometry
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence rightKey) outcome ↔
      RawMolecule.compareSparseCanonicalLayers compare
        leftKey.rule3Key.rule3 rightKey.rule3Key.rule3 = outcome := by
  have localOutcome : ∀ position decision,
      StereochemicalOutcomeAt StereochemicalRule.rule3DoubleBondGeometry
          (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
          (evidence leftKey)
          (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
          (evidence rightKey) position decision ↔
        OptionalOutcome Rule3Signature.Outcome
          (if position = [] then some leftKey.rule3 else none)
          (if position = [] then some rightKey.rule3 else none) decision := by
    intro position decision
    rw [stereochemicalOutcomeAt_iff_nodeOutcome]
    simp only [StereochemicalNodeOutcome, observationAtPosition_bind_rule3]
  have h := rootOnlyHierarchyOutcome_iff Rule3Signature.Outcome
    (fun left right first second => Rule3Signature.outcome_functional left right)
    Rule3Signature.outcome_total leftKey.rule3 rightKey.rule3 leftKey rightKey mol
    leftHierarchy rightHierarchy (leftHierarchy.declarativeAddressing mol)
    (rightHierarchy.declarativeAddressing mol) StereochemicalRule.rule3DoubleBondGeometry
    localOutcome outcome
  exact h.trans
    (ProductionRules35Key.rule3_outcome_iff_compiled leftKey rightKey outcome)

/-- The converted hierarchy's declarative Rule-4b judgment is exactly comparison of the complete
opponent-independent production readings. -/
theorem rule4bHierarchyOutcome_iff
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome StereochemicalRule.rule4bLikeUnlikeDescriptorPairs
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence rightKey) outcome ↔
      compare leftKey.rule4b rightKey.rule4b = outcome := by
  let decision := compare leftKey.rule4b rightKey.rule4b
  have hcanonical :
      StereochemicalHierarchyOutcome StereochemicalRule.rule4bLikeUnlikeDescriptorPairs
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence rightKey) decision := by
    cases hdecision : decision with
    | lt =>
        refine ⟨[], ?_, ?_⟩
        · rw [stereochemicalOutcomeAt_iff_nodeOutcome]
          simp only [StereochemicalNodeOutcome, observationAtPosition_bind_rule4b,
            ↓reduceIte]
          exact OptionalOutcome.both hdecision
        · intro earlier hearlier
          exact False.elim (not_addressBefore_nil earlier hearlier)
    | eq =>
        intro position
        rw [stereochemicalOutcomeAt_iff_nodeOutcome]
        simp only [StereochemicalNodeOutcome, observationAtPosition_bind_rule4b]
        by_cases hroot : position = []
        · simp only [hroot, ↓reduceIte]
          exact OptionalOutcome.both hdecision
        · simp only [hroot, ↓reduceIte]
          exact OptionalOutcome.neither
    | gt =>
        refine ⟨[], ?_, ?_⟩
        · rw [stereochemicalOutcomeAt_iff_nodeOutcome]
          simp only [StereochemicalNodeOutcome, observationAtPosition_bind_rule4b,
            ↓reduceIte]
          exact OptionalOutcome.both hdecision
        · intro earlier hearlier
          exact False.elim (not_addressBefore_nil earlier hearlier)
  constructor
  · intro h
    have heq := stereochemicalHierarchyOutcome_functional
      StereochemicalRule.rule4bLikeUnlikeDescriptorPairs
      (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
      (evidence leftKey)
      (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
      (evidence rightKey) h hcanonical
    exact heq.symm
  · intro h
    rw [← h]
    exact hcanonical

theorem rule4aHierarchyOutcome_iff
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome StereochemicalRule.rule4aStereogenicUnitKind
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence rightKey) outcome ↔
      RawMolecule.compareSparseCanonicalLayers OfficialStereogenicUnitKind.compare
        leftKey.rule4a rightKey.rule4a = outcome := by
  let leftSignature : Rule4aSignature := ⟨rule4aLayersToDeclarative leftKey.rule4a⟩
  let rightSignature : Rule4aSignature := ⟨rule4aLayersToDeclarative rightKey.rule4a⟩
  have localOutcome : ∀ position decision,
      StereochemicalOutcomeAt StereochemicalRule.rule4aStereogenicUnitKind
          (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
          (evidence leftKey)
          (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
          (evidence rightKey) position decision ↔
        OptionalOutcome Rule4aSignature.Outcome
          (if position = [] then some leftSignature else none)
          (if position = [] then some rightSignature else none) decision := by
    intro position decision
    rw [stereochemicalOutcomeAt_iff_nodeOutcome]
    simp only [StereochemicalNodeOutcome, observationAtPosition_bind_rule4a]
    rfl
  have h := rootOnlyHierarchyOutcome_iff Rule4aSignature.Outcome
    (fun left right first second => Rule4aSignature.outcome_functional left right)
    Rule4aSignature.outcome_total leftSignature rightSignature leftKey rightKey mol
    leftHierarchy rightHierarchy (leftHierarchy.declarativeAddressing mol)
    (rightHierarchy.declarativeAddressing mol) StereochemicalRule.rule4aStereogenicUnitKind
    localOutcome outcome
  simpa [leftSignature, rightSignature, Rule4aSignature.Outcome,
    compareRule4aLayers_toDeclarative] using h

theorem rule4cHierarchyOutcome_iff
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome StereochemicalRule.rule4cPseudoasymmetricDescriptor
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence rightKey) outcome ↔
      RawMolecule.compareSparseCanonicalLayers compare leftKey.rule4c rightKey.rule4c = outcome := by
  let leftSignature : Rule4cSignature := ⟨leftKey.rule4c⟩
  let rightSignature : Rule4cSignature := ⟨rightKey.rule4c⟩
  have localOutcome : ∀ position decision,
      StereochemicalOutcomeAt StereochemicalRule.rule4cPseudoasymmetricDescriptor
          (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
          (evidence leftKey)
          (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
          (evidence rightKey) position decision ↔
        OptionalOutcome Rule4cSignature.Outcome
          (if position = [] then some leftSignature else none)
          (if position = [] then some rightSignature else none) decision := by
    intro position decision
    rw [stereochemicalOutcomeAt_iff_nodeOutcome]
    simp only [StereochemicalNodeOutcome, observationAtPosition_bind_rule4c]
    rfl
  have h := rootOnlyHierarchyOutcome_iff Rule4cSignature.Outcome
    (fun left right first second => Rule4cSignature.outcome_functional left right)
    Rule4cSignature.outcome_total leftSignature rightSignature leftKey rightKey mol
    leftHierarchy rightHierarchy (leftHierarchy.declarativeAddressing mol)
    (rightHierarchy.declarativeAddressing mol) StereochemicalRule.rule4cPseudoasymmetricDescriptor
    localOutcome outcome
  simpa [leftSignature, rightSignature, Rule4cSignature.Outcome,
    compareRule4cLayers_toDeclarative] using h

theorem rule5HierarchyOutcome_iff
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (outcome : Ordering) :
    StereochemicalHierarchyOutcome StereochemicalRule.rule5EnantiomorphicDescriptor
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence rightKey) outcome ↔
      RawMolecule.compareSparseCanonicalLayers compare leftKey.rule5 rightKey.rule5 = outcome := by
  let leftSignature : Rule5Signature := ⟨leftKey.rule5⟩
  let rightSignature : Rule5Signature := ⟨rightKey.rule5⟩
  have localOutcome : ∀ position decision,
      StereochemicalOutcomeAt StereochemicalRule.rule5EnantiomorphicDescriptor
          (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
          (evidence leftKey)
          (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
          (evidence rightKey) position decision ↔
        OptionalOutcome Rule5Signature.Outcome
          (if position = [] then some leftSignature else none)
          (if position = [] then some rightSignature else none) decision := by
    intro position decision
    rw [stereochemicalOutcomeAt_iff_nodeOutcome]
    simp only [StereochemicalNodeOutcome, observationAtPosition_bind_rule5]
    rfl
  have h := rootOnlyHierarchyOutcome_iff Rule5Signature.Outcome
    (fun left right first second => Rule5Signature.outcome_functional left right)
    Rule5Signature.outcome_total leftSignature rightSignature leftKey rightKey mol
    leftHierarchy rightHierarchy (leftHierarchy.declarativeAddressing mol)
    (rightHierarchy.declarativeAddressing mol) StereochemicalRule.rule5EnantiomorphicDescriptor
    localOutcome outcome
  simpa [leftSignature, rightSignature, Rule5Signature.Outcome,
    compareRule5Layers_toDeclarative] using h

/-- Rule-local executable outcome on the five-field production key.

The Rule-3 branch is the ordinary sparse comparison of the compiled priority layers stored in
`rule3Key`; it is not a re-derivation from the semantic projection. -/
def productionRuleOutcome (left right : ProductionRules35Key) :
    StereochemicalRule → Ordering
  | .rule3DoubleBondGeometry =>
      RawMolecule.compareSparseCanonicalLayers compare
        left.rule3Key.rule3 right.rule3Key.rule3
  | .rule4aStereogenicUnitKind =>
      RawMolecule.compareSparseCanonicalLayers OfficialStereogenicUnitKind.compare
        left.rule4a right.rule4a
  | .rule4bLikeUnlikeDescriptorPairs => compare left.rule4b right.rule4b
  | .rule4cPseudoasymmetricDescriptor =>
      RawMolecule.compareSparseCanonicalLayers compare left.rule4c right.rule4c
  | .rule5EnantiomorphicDescriptor =>
      RawMolecule.compareSparseCanonicalLayers compare left.rule5 right.rule5

/-- The live five-entry trace contains exactly the rule-local outcomes used by the declarative
bridge, in official Rules 3, 4a, 4b, 4c, 5 order.

The first entry is definitionally the sparse compiled Rule-3 comparison, matching the migrated
`ProductionRules35Key.compareTrace`. -/
theorem compareTrace_eq_productionRuleOutcomes (left right : ProductionRules35Key) :
    left.compareTrace right =
      [ { rule := CIPRuleFamily.doubleBondGeometry
          outcome := productionRuleOutcome left right .rule3DoubleBondGeometry }
      , { rule := CIPRuleFamily.stereogenicUnitKind
          outcome := productionRuleOutcome left right .rule4aStereogenicUnitKind }
      , { rule := CIPRuleFamily.likeUnlikeDescriptorPair
          outcome := productionRuleOutcome left right .rule4bLikeUnlikeDescriptorPairs }
      , { rule := CIPRuleFamily.pseudoasymmetricDescriptor
          outcome := productionRuleOutcome left right .rule4cPseudoasymmetricDescriptor }
      , { rule := CIPRuleFamily.pseudoasymmetricTiebreak
          outcome := productionRuleOutcome left right .rule5EnantiomorphicDescriptor }
      ] := by
  rfl

/-- One theorem covers every Rules 3--5 slot: production key comparison holds exactly when the
independent declarative judgment holds on the converted finite rooted digraphs. -/
theorem hierarchyOutcome_iff_ruleOutcome
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (rule : StereochemicalRule) (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule
        (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
        (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
        (evidence rightKey) outcome ↔
      productionRuleOutcome leftKey rightKey rule = outcome := by
  cases rule
  · exact rule3HierarchyOutcome_iff leftKey rightKey mol leftHierarchy rightHierarchy outcome
  · exact rule4aHierarchyOutcome_iff leftKey rightKey mol leftHierarchy rightHierarchy outcome
  · exact rule4bHierarchyOutcome_iff leftKey rightKey mol leftHierarchy rightHierarchy outcome
  · exact rule4cHierarchyOutcome_iff leftKey rightKey mol leftHierarchy rightHierarchy outcome
  · exact rule5HierarchyOutcome_iff leftKey rightKey mol leftHierarchy rightHierarchy outcome

/-- Addressing-independent form of the bridge.  The semantic signatures live at the graph root,
which every admissible addressing must map to `[]`; therefore the result holds for arbitrary
addressings of both converted representations, not only for the compiler's canonical paths. -/
theorem hierarchyOutcome_allAddressings_iff_ruleOutcome
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (leftAddressing : (leftHierarchy.toDeclarativeDigraph mol).Addressing)
    (rightAddressing : (rightHierarchy.toDeclarativeDigraph mol).Addressing)
    (rule : StereochemicalRule) (outcome : Ordering) :
    StereochemicalHierarchyOutcome rule
        (leftHierarchy.toDeclarativeDigraph mol) leftAddressing (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) rightAddressing (evidence rightKey) outcome ↔
      productionRuleOutcome leftKey rightKey rule = outcome := by
  cases rule with
  | rule3DoubleBondGeometry =>
      have hleftRoot :
          (evidence leftKey (leftHierarchy.toDeclarativeDigraph mol).root).rule3 =
            some leftKey.rule3 := by simp [evidence]
      have hrightRoot :
          (evidence rightKey (rightHierarchy.toDeclarativeDigraph mol).root).rule3 =
            some rightKey.rule3 := by simp [evidence]
      have hleftOther : ∀ node, node ≠ (leftHierarchy.toDeclarativeDigraph mol).root →
          (evidence leftKey node).rule3 = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol leftHierarchy node hnode
        simp [evidence, haddress]
      have hrightOther : ∀ node, node ≠ (rightHierarchy.toDeclarativeDigraph mol).root →
          (evidence rightKey node).rule3 = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol rightHierarchy node hnode
        simp [evidence, haddress]
      have localOutcome := outcomeAt_iff_rootOnly Rule3Signature.Outcome (·.rule3)
        StereochemicalRule.rule3DoubleBondGeometry (by intro left right decision; rfl)
        leftKey.rule3 rightKey.rule3 leftKey rightKey mol leftHierarchy rightHierarchy
        leftAddressing rightAddressing hleftRoot hrightRoot hleftOther hrightOther
      have h := rootOnlyHierarchyOutcome_iff Rule3Signature.Outcome
        (fun left right first second => Rule3Signature.outcome_functional left right)
        Rule3Signature.outcome_total leftKey.rule3 rightKey.rule3 leftKey rightKey mol
        leftHierarchy rightHierarchy leftAddressing rightAddressing
        StereochemicalRule.rule3DoubleBondGeometry localOutcome outcome
      simpa only [productionRuleOutcome] using
        (h.trans (ProductionRules35Key.rule3_outcome_iff_compiled leftKey rightKey outcome))
  | rule4aStereogenicUnitKind =>
      let leftSignature : Rule4aSignature := ⟨rule4aLayersToDeclarative leftKey.rule4a⟩
      let rightSignature : Rule4aSignature := ⟨rule4aLayersToDeclarative rightKey.rule4a⟩
      have hleftRoot :
          (evidence leftKey (leftHierarchy.toDeclarativeDigraph mol).root).rule4a =
            some leftSignature := by simp [evidence, leftSignature]
      have hrightRoot :
          (evidence rightKey (rightHierarchy.toDeclarativeDigraph mol).root).rule4a =
            some rightSignature := by simp [evidence, rightSignature]
      have hleftOther : ∀ node, node ≠ (leftHierarchy.toDeclarativeDigraph mol).root →
          (evidence leftKey node).rule4a = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol leftHierarchy node hnode
        simp [evidence, haddress]
      have hrightOther : ∀ node, node ≠ (rightHierarchy.toDeclarativeDigraph mol).root →
          (evidence rightKey node).rule4a = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol rightHierarchy node hnode
        simp [evidence, haddress]
      have localOutcome := outcomeAt_iff_rootOnly Rule4aSignature.Outcome (·.rule4a)
        StereochemicalRule.rule4aStereogenicUnitKind (by intro left right decision; rfl)
        leftSignature rightSignature leftKey rightKey mol leftHierarchy rightHierarchy
        leftAddressing rightAddressing hleftRoot hrightRoot hleftOther hrightOther
      have h := rootOnlyHierarchyOutcome_iff Rule4aSignature.Outcome
        (fun left right first second => Rule4aSignature.outcome_functional left right)
        Rule4aSignature.outcome_total leftSignature rightSignature leftKey rightKey mol
        leftHierarchy rightHierarchy leftAddressing rightAddressing
        StereochemicalRule.rule4aStereogenicUnitKind localOutcome outcome
      simpa [productionRuleOutcome, Rule4aSignature.Outcome, leftSignature, rightSignature,
        compareRule4aLayers_toDeclarative] using h
  | rule4bLikeUnlikeDescriptorPairs =>
      let leftSignature : Rule4bSignature := ⟨leftKey.rule4b⟩
      let rightSignature : Rule4bSignature := ⟨rightKey.rule4b⟩
      have hleftRoot :
          (evidence leftKey (leftHierarchy.toDeclarativeDigraph mol).root).rule4b =
            some leftSignature := by simp [evidence, leftSignature]
      have hrightRoot :
          (evidence rightKey (rightHierarchy.toDeclarativeDigraph mol).root).rule4b =
            some rightSignature := by simp [evidence, rightSignature]
      have hleftOther : ∀ node, node ≠ (leftHierarchy.toDeclarativeDigraph mol).root →
          (evidence leftKey node).rule4b = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol leftHierarchy node hnode
        simp [evidence, haddress]
      have hrightOther : ∀ node, node ≠ (rightHierarchy.toDeclarativeDigraph mol).root →
          (evidence rightKey node).rule4b = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol rightHierarchy node hnode
        simp [evidence, haddress]
      have localOutcome := outcomeAt_iff_rootOnly Rule4bSignature.Outcome (·.rule4b)
        StereochemicalRule.rule4bLikeUnlikeDescriptorPairs (by intro left right decision; rfl)
        leftSignature rightSignature leftKey rightKey mol leftHierarchy rightHierarchy
        leftAddressing rightAddressing hleftRoot hrightRoot hleftOther hrightOther
      have h := rootOnlyHierarchyOutcome_iff Rule4bSignature.Outcome
        (fun left right first second => Rule4bSignature.outcome_functional left right)
        Rule4bSignature.outcome_total leftSignature rightSignature leftKey rightKey mol
        leftHierarchy rightHierarchy leftAddressing rightAddressing
        StereochemicalRule.rule4bLikeUnlikeDescriptorPairs localOutcome outcome
      simpa [productionRuleOutcome, Rule4bSignature.Outcome, leftSignature, rightSignature] using h
  | rule4cPseudoasymmetricDescriptor =>
      let leftSignature : Rule4cSignature := ⟨leftKey.rule4c⟩
      let rightSignature : Rule4cSignature := ⟨rightKey.rule4c⟩
      have hleftRoot :
          (evidence leftKey (leftHierarchy.toDeclarativeDigraph mol).root).rule4c =
            some leftSignature := by simp [evidence, leftSignature]
      have hrightRoot :
          (evidence rightKey (rightHierarchy.toDeclarativeDigraph mol).root).rule4c =
            some rightSignature := by simp [evidence, rightSignature]
      have hleftOther : ∀ node, node ≠ (leftHierarchy.toDeclarativeDigraph mol).root →
          (evidence leftKey node).rule4c = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol leftHierarchy node hnode
        simp [evidence, haddress]
      have hrightOther : ∀ node, node ≠ (rightHierarchy.toDeclarativeDigraph mol).root →
          (evidence rightKey node).rule4c = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol rightHierarchy node hnode
        simp [evidence, haddress]
      have localOutcome := outcomeAt_iff_rootOnly Rule4cSignature.Outcome (·.rule4c)
        StereochemicalRule.rule4cPseudoasymmetricDescriptor (by intro left right decision; rfl)
        leftSignature rightSignature leftKey rightKey mol leftHierarchy rightHierarchy
        leftAddressing rightAddressing hleftRoot hrightRoot hleftOther hrightOther
      have h := rootOnlyHierarchyOutcome_iff Rule4cSignature.Outcome
        (fun left right first second => Rule4cSignature.outcome_functional left right)
        Rule4cSignature.outcome_total leftSignature rightSignature leftKey rightKey mol
        leftHierarchy rightHierarchy leftAddressing rightAddressing
        StereochemicalRule.rule4cPseudoasymmetricDescriptor localOutcome outcome
      simpa [productionRuleOutcome, Rule4cSignature.Outcome, leftSignature, rightSignature,
        compareRule4cLayers_toDeclarative] using h
  | rule5EnantiomorphicDescriptor =>
      let leftSignature : Rule5Signature := ⟨leftKey.rule5⟩
      let rightSignature : Rule5Signature := ⟨rightKey.rule5⟩
      have hleftRoot :
          (evidence leftKey (leftHierarchy.toDeclarativeDigraph mol).root).rule5 =
            some leftSignature := by simp [evidence, leftSignature]
      have hrightRoot :
          (evidence rightKey (rightHierarchy.toDeclarativeDigraph mol).root).rule5 =
            some rightSignature := by simp [evidence, rightSignature]
      have hleftOther : ∀ node, node ≠ (leftHierarchy.toDeclarativeDigraph mol).root →
          (evidence leftKey node).rule5 = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol leftHierarchy node hnode
        simp [evidence, haddress]
      have hrightOther : ∀ node, node ≠ (rightHierarchy.toDeclarativeDigraph mol).root →
          (evidence rightKey node).rule5 = none := by
        intro node hnode
        have haddress := evidence_field_none_of_ne_root mol rightHierarchy node hnode
        simp [evidence, haddress]
      have localOutcome := outcomeAt_iff_rootOnly Rule5Signature.Outcome (·.rule5)
        StereochemicalRule.rule5EnantiomorphicDescriptor (by intro left right decision; rfl)
        leftSignature rightSignature leftKey rightKey mol leftHierarchy rightHierarchy
        leftAddressing rightAddressing hleftRoot hrightRoot hleftOther hrightOther
      have h := rootOnlyHierarchyOutcome_iff Rule5Signature.Outcome
        (fun left right first second => Rule5Signature.outcome_functional left right)
        Rule5Signature.outcome_total leftSignature rightSignature leftKey rightKey mol
        leftHierarchy rightHierarchy leftAddressing rightAddressing
        StereochemicalRule.rule5EnantiomorphicDescriptor localOutcome outcome
      simpa [productionRuleOutcome, Rule5Signature.Outcome, leftSignature, rightSignature,
        compareRule5Layers_toDeclarative] using h

/-- Canonical outcome specialized to converted production hierarchies.

This is the same non-vacuous universal quantification used by
`StereochemicalProblemData.CanonicalOutcome`, stated without pretending that the conversion has
already supplied the independent constitutional `ExactExpansion` proof required to build an
entire problem instance. -/
def ConvertedCanonicalOutcome
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (rule : StereochemicalRule) (outcome : Ordering) : Prop :=
  Nonempty (leftHierarchy.toDeclarativeDigraph mol).Addressing ∧
    Nonempty (rightHierarchy.toDeclarativeDigraph mol).Addressing ∧
    ∀ leftAddressing rightAddressing,
      StereochemicalHierarchyOutcome rule
        (leftHierarchy.toDeclarativeDigraph mol) leftAddressing (evidence leftKey)
        (rightHierarchy.toDeclarativeDigraph mol) rightAddressing (evidence rightKey) outcome

/-- The production decision is sound and complete for the non-vacuous, addressing-independent
canonical outcome of the converted hierarchies. -/
theorem convertedCanonicalOutcome_iff_ruleOutcome
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey)
    (rule : StereochemicalRule) (outcome : Ordering) :
    ConvertedCanonicalOutcome leftKey rightKey mol leftHierarchy rightHierarchy rule outcome ↔
      productionRuleOutcome leftKey rightKey rule = outcome := by
  constructor
  · rintro ⟨_, _, hall⟩
    exact (hierarchyOutcome_allAddressings_iff_ruleOutcome leftKey rightKey mol
      leftHierarchy rightHierarchy (leftHierarchy.declarativeAddressing mol)
      (rightHierarchy.declarativeAddressing mol) rule outcome).1
      (hall (leftHierarchy.declarativeAddressing mol)
        (rightHierarchy.declarativeAddressing mol))
  · intro houtcome
    refine ⟨⟨leftHierarchy.declarativeAddressing mol⟩,
      ⟨rightHierarchy.declarativeAddressing mol⟩, ?_⟩
    intro leftAddressing rightAddressing
    exact (hierarchyOutcome_allAddressings_iff_ruleOutcome leftKey rightKey mol
      leftHierarchy rightHierarchy leftAddressing rightAddressing rule outcome).2 houtcome

/-- A successfully compiled unary Rules 3--5 key always comes with the exact authoritative
production hierarchy from which its Rule-4a observation was read. -/
theorem productionRules35Key?_hasHierarchy
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center ligand : ℕ) (compiled : ProductionRules35Key)
    (hcompiled : productionRules35Key? result mol state center ligand = some compiled) :
    ∃ hierarchy, branchDescriptorCanonicalKey? mol center ligand = some hierarchy := by
  cases hhierarchy : branchDescriptorCanonicalKey? mol center ligand with
  | none =>
      simp [productionRules35Key?, branchRule4aSparseLayers, hhierarchy] at hcompiled
  | some hierarchy =>
      exact ⟨hierarchy, rfl⟩

/-- All five declarative rule judgments certified by comparing two production keys on their exact
converted canonical hierarchies. -/
structure Rules35HierarchyJudgments
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey) : Prop where
  rule3 : StereochemicalHierarchyOutcome .rule3DoubleBondGeometry
    (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
    (evidence leftKey)
    (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
    (evidence rightKey) (productionRuleOutcome leftKey rightKey .rule3DoubleBondGeometry)
  rule4a : StereochemicalHierarchyOutcome .rule4aStereogenicUnitKind
    (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
    (evidence leftKey)
    (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
    (evidence rightKey) (productionRuleOutcome leftKey rightKey .rule4aStereogenicUnitKind)
  rule4b : StereochemicalHierarchyOutcome .rule4bLikeUnlikeDescriptorPairs
    (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
    (evidence leftKey)
    (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
    (evidence rightKey) (productionRuleOutcome leftKey rightKey .rule4bLikeUnlikeDescriptorPairs)
  rule4c : StereochemicalHierarchyOutcome .rule4cPseudoasymmetricDescriptor
    (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
    (evidence leftKey)
    (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
    (evidence rightKey) (productionRuleOutcome leftKey rightKey .rule4cPseudoasymmetricDescriptor)
  rule5 : StereochemicalHierarchyOutcome .rule5EnantiomorphicDescriptor
    (leftHierarchy.toDeclarativeDigraph mol) (leftHierarchy.declarativeAddressing mol)
    (evidence leftKey)
    (rightHierarchy.toDeclarativeDigraph mol) (rightHierarchy.declarativeAddressing mol)
    (evidence rightKey) (productionRuleOutcome leftKey rightKey .rule5EnantiomorphicDescriptor)

theorem rules35HierarchyJudgments
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey) :
    Rules35HierarchyJudgments leftKey rightKey mol leftHierarchy rightHierarchy := by
  constructor <;>
    apply (hierarchyOutcome_iff_ruleOutcome leftKey rightKey mol
      leftHierarchy rightHierarchy _ _).2 <;> rfl

/-- The stronger, representation-independent certificate for all five Rules 3--5 fields. -/
structure Rules35CanonicalOutcomes
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey) : Prop where
  rule3 : ConvertedCanonicalOutcome leftKey rightKey mol leftHierarchy rightHierarchy
    .rule3DoubleBondGeometry (productionRuleOutcome leftKey rightKey .rule3DoubleBondGeometry)
  rule4a : ConvertedCanonicalOutcome leftKey rightKey mol leftHierarchy rightHierarchy
    .rule4aStereogenicUnitKind (productionRuleOutcome leftKey rightKey .rule4aStereogenicUnitKind)
  rule4b : ConvertedCanonicalOutcome leftKey rightKey mol leftHierarchy rightHierarchy
    .rule4bLikeUnlikeDescriptorPairs
      (productionRuleOutcome leftKey rightKey .rule4bLikeUnlikeDescriptorPairs)
  rule4c : ConvertedCanonicalOutcome leftKey rightKey mol leftHierarchy rightHierarchy
    .rule4cPseudoasymmetricDescriptor
      (productionRuleOutcome leftKey rightKey .rule4cPseudoasymmetricDescriptor)
  rule5 : ConvertedCanonicalOutcome leftKey rightKey mol leftHierarchy rightHierarchy
    .rule5EnantiomorphicDescriptor
      (productionRuleOutcome leftKey rightKey .rule5EnantiomorphicDescriptor)

theorem rules35CanonicalOutcomes
    (leftKey rightKey : ProductionRules35Key) (mol : RawMolecule)
    (leftHierarchy rightHierarchy : RawMolecule.CanonicalBranchKey) :
    Rules35CanonicalOutcomes leftKey rightKey mol leftHierarchy rightHierarchy := by
  constructor <;>
    apply (convertedCanonicalOutcome_iff_ruleOutcome leftKey rightKey mol
      leftHierarchy rightHierarchy _ _).2 <;> rfl

/-- End-to-end successful-compilation bridge: the live production keys determine exact production
hierarchies, and every emitted Rules 3--5 decision is a declarative judgment on their converted
finite rooted digraphs. -/
theorem productionRules35Keys_have_declarativeJudgments
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ)
    (leftKey rightKey : ProductionRules35Key)
    (hleft : productionRules35Key? result mol state center left = some leftKey)
    (hright : productionRules35Key? result mol state center right = some rightKey) :
    ∃ leftHierarchy rightHierarchy,
      branchDescriptorCanonicalKey? mol center left = some leftHierarchy ∧
      branchDescriptorCanonicalKey? mol center right = some rightHierarchy ∧
      Rules35HierarchyJudgments leftKey rightKey mol leftHierarchy rightHierarchy := by
  rcases productionRules35Key?_hasHierarchy result mol state center left leftKey hleft with
    ⟨leftHierarchy, hleftHierarchy⟩
  rcases productionRules35Key?_hasHierarchy result mol state center right rightKey hright with
    ⟨rightHierarchy, hrightHierarchy⟩
  exact ⟨leftHierarchy, rightHierarchy, hleftHierarchy, hrightHierarchy,
    rules35HierarchyJudgments leftKey rightKey mol leftHierarchy rightHierarchy⟩

/-- End-to-end live-executable certificate.  Successful production compilation yields the exact
authoritative hierarchies, the exact emitted five-rule trace, and universal declarative outcomes
for every admissible addressing of both converted finite rooted digraphs. -/
theorem compareRawOfficialSequences_has_convertedCanonicalOutcomes
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (center left right : ℕ)
    (leftKey rightKey : ProductionRules35Key)
    (hleft : productionRules35Key? result mol state center left = some leftKey)
    (hright : productionRules35Key? result mol state center right = some rightKey) :
    ∃ leftHierarchy rightHierarchy,
      branchDescriptorCanonicalKey? mol center left = some leftHierarchy ∧
      branchDescriptorCanonicalKey? mol center right = some rightHierarchy ∧
      compareRawOfficialSequences result mol state center left right =
        some (leftKey.compareTrace rightKey) ∧
      Rules35CanonicalOutcomes leftKey rightKey mol leftHierarchy rightHierarchy := by
  rcases productionRules35Keys_have_declarativeJudgments result mol state center left right
      leftKey rightKey hleft hright with
    ⟨leftHierarchy, rightHierarchy, hleftHierarchy, hrightHierarchy, _⟩
  exact ⟨leftHierarchy, rightHierarchy, hleftHierarchy, hrightHierarchy,
    compareRawOfficialSequences_of_keys result mol state center left right
      leftKey rightKey hleft hright,
    rules35CanonicalOutcomes leftKey rightKey mol leftHierarchy rightHierarchy⟩

end ProductionCIPHierarchy

end
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.ProductionCIPHierarchy.rule3HierarchyOutcome_iff

assert_kernel_only TetraStereo.OneCenter.ProductionCIPHierarchy.compareRawOfficialSequences_has_convertedCanonicalOutcomes
