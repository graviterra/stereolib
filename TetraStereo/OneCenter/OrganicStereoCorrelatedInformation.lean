import TetraStereo.OneCenter.GraphicalRepresentationST3to6
import TetraStereo.OneCenter.OrganicStereoRealConfiguration

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open IUPACDrawing2006.ST6

/-!
# Correlated joint stereochemical information over an arbitrary physical state type

This module is a representation layer for *correlated* stereochemical information.  The central
object is `CorrelatedInformation State`, where `State` is an arbitrary type of complete physical
states.  A value stores

* the existing IUPAC drawing knowledge tag `ConfigurationKnowledge` (all eight tags of
  `ST6.allKnowledgeStates`);
* a configuration-scope summary `List DiagramConfigurationScope`, including all
  `relative`/`racemic` group identifiers;
* `possible : Set State`, the set of **full joint** physical states consistent with the evidence;
  and
* `diagram? : Option DiagramConfiguration`, the original diagram when the scope summary is attached
  to its bond/atom-configuration statements.  The bare scope list does not by itself retain that
  statement attachment.

`possible` is deliberately a set of whole states, not a product of independently chosen per-centre
possibilities.  The concrete `TwoCoordinateCorrelation` section below proves that projections onto
individual coordinates cannot in general recover the joint set, even when both marginal projection
sets are identical.  General correlated information therefore remains representable, while any
independent-coordinate summary is strictly weaker.

The module provides singleton information, universal (`whollyUnspecified`) information, and
restriction by an explicit physical constraint, together with exact tag/scope preservation,
membership, commutation, idempotence, transport along an equivalence of state types, and
entailment preservation.

## Representation boundaries

* Knowledge tags and scope lists are retained metadata.  Nothing here derives racemicness,
  absolute descriptors, or any stereochemical fact from a tag; no theorem relates
  `knowledge = .racemic` or `knowledge = .unknownAbsoluteSingleStereoisomer` to a particular
  `possible` set.  A tag can only be justified by evidence outside this representation layer.
  The eight `ST6.ConfigurationKnowledge` tags classify drawing-knowledge states; they are not a
  chemical truth oracle and are not proved complete for chemistry.
* A bare `List DiagramConfigurationScope` retains scope values and their group identifiers, but it
  does **not** retain which bond or atom configuration each scope annotates.  The attachment is
  retained separately by `diagram? : Option DiagramConfiguration`; `RetainsDiagram` states that the
  scope summary is exactly the diagram's statement scopes, and `ofDiagram`/`ofSource` are the
  attachment-preserving constructors.  `ofPossible` sets `diagram? = none` and therefore makes no
  attachment claim.
* An `unknown` tag is not proved to be permanent: extra actual evidence is represented by
  narrowing `possible` (via `restrict`), while the tag itself is never silently rewritten.
* An empty `possible` set records inconsistent evidence, not vacuous chemical knowledge.
  `Consistent` is nonemptiness; `entailsFalse_iff_empty` states that the false proposition is
  entailed exactly when the evidence is inconsistent, and `CertifiedEntails` requires nonemptiness
  before a physical fact is claimed.
* There are no weights, populations, energies, or dynamics in this module.
-/

/-! ## Original diagram statements and their scopes -/

namespace DiagramConfiguration

/-- The configuration scopes annotated by the original diagram statements, one entry per
configuration-bearing bond or atom configuration, in source order.  This list is a *summary*: it
preserves scope values and their group identifiers and their multiplicity, but by itself it does
not record which statement each entry annotates.  The enclosing `DiagramConfiguration`, retained in
`CorrelatedInformation.diagram?`, is what preserves the statement attachment. -/
def scopeList (diagram : DiagramConfiguration) : List DiagramConfigurationScope :=
  diagram.bonds.map DiagramBond.scope ++
    diagram.atomConfigurations.map DiagramAtomConfiguration.scope

/-- Membership in the summary is exactly membership in some retained bond or atom-configuration
statement's scope.  This is the statement-attachment statement for a retained diagram. -/
@[simp] theorem mem_scopeList_iff (diagram : DiagramConfiguration)
    (scope : DiagramConfigurationScope) :
    scope ∈ diagram.scopeList ↔
      (∃ bond ∈ diagram.bonds, bond.scope = scope) ∨
      (∃ configuration ∈ diagram.atomConfigurations, configuration.scope = scope) := by
  simp [scopeList]

end DiagramConfiguration

/-! ## The joint-information carrier -/

/-- Correlated stereochemical information over complete physical states of type `State`.

`possible` is the set of whole joint states allowed by the evidence.  It is not stored as, and must
not be read as, a product of per-centre possibilities.

`scopes` is a scope summary.  The original diagram, and therefore the attachment of each scope to a
particular bond or atom-configuration statement, is retained separately in `diagram?` when
available.  Use `RetainsDiagram` to assert that the summary is exactly the retained diagram's
statement scopes. -/
structure CorrelatedInformation (State : Type*) where
  /-- The retained IUPAC configuration-knowledge tag. -/
  knowledge : ConfigurationKnowledge
  /-- The retained configuration-scope summary, including `relative`/`racemic` group identifiers.
  This list alone does not retain statement attachment. -/
  scopes : List DiagramConfigurationScope
  /-- The full joint set of physical states consistent with the evidence. -/
  possible : Set State
  /-- The original graphical diagram whose statements annotate the scopes, when this information is
  attached to one.  `none` records that no statement attachment is claimed. -/
  diagram? : Option DiagramConfiguration := none

namespace CorrelatedInformation

variable {State : Type*}

/-! ## Constructors -/

/-- General constructor from an explicitly supplied joint possible-state set.  No consistency
requirement is imposed, so that inconsistent evidence remains representable and distinguishable
from missing information. -/
def ofPossible (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (possible : Set State) :
    CorrelatedInformation State :=
  { knowledge := knowledge
    scopes := scopes
    possible := possible
    diagram? := none }

/-- Information attached to an original graphical diagram.  The scope summary is derived exactly
from the diagram's configuration-bearing statements, and the original diagram is retained
unchanged, so the statement attachment is not lost. -/
def ofDiagram (knowledge : ConfigurationKnowledge) (diagram : DiagramConfiguration)
    (possible : Set State) : CorrelatedInformation State :=
  { knowledge := knowledge
    scopes := diagram.scopeList
    possible := possible
    diagram? := some diagram }

/-- The scope summary is exactly the statement-scope list of the retained original diagram, when a
diagram is retained.  When `diagram? = none`, no attachment is claimed. -/
def RetainsDiagram (info : CorrelatedInformation State) : Prop :=
  match info.diagram? with
  | some diagram => info.scopes = diagram.scopeList
  | none => True

/-- Information whose joint possible set is exactly one physical state. -/
def singleton (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    CorrelatedInformation State :=
  ofPossible knowledge scopes {state}

/-- Information whose joint possible set is every state of the carrier type.  The tag is retained
unchanged; this constructor records universal possibility, not a claim that every state is
chemically admissible. -/
def universal (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) : CorrelatedInformation State :=
  ofPossible knowledge scopes Set.univ

/-- Wholly unspecified information: the explicit `whollyUnspecified` tag with universal joint
possibility and the supplied scopes. -/
def whollyUnspecified (scopes : List DiagramConfigurationScope) :
    CorrelatedInformation State :=
  universal ConfigurationKnowledge.whollyUnspecified scopes

/-- Restriction by an explicit physical constraint.  The evidence is intersected with `constraint`;
no state outside the constraint remains possible. -/
def restrict (info : CorrelatedInformation State) (constraint : Set State) :
    CorrelatedInformation State :=
  { info with possible := info.possible ∩ constraint }

/-! ## Transport along an equivalence of state types -/

/-- Transport joint information along an equivalence of physical-state types.  Knowledge tags and
scopes are unchanged; the joint possible set is moved by the equivalence. -/
def transport {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) : CorrelatedInformation Other :=
  { knowledge := info.knowledge
    scopes := info.scopes
    possible := equivalent '' info.possible
    diagram? := info.diagram? }

/-! ## Entailment and consistency -/

/-- A piece of information entails `property` when every jointly possible state satisfies it. -/
def Entails (info : CorrelatedInformation State) (property : State → Prop) : Prop :=
  ∀ state : State, state ∈ info.possible → property state

/-- Consistency of evidence is nonemptiness of the joint possible set.  This is a separate
question from the knowledge tag and from entailment. -/
def Consistent (info : CorrelatedInformation State) : Prop :=
  info.possible.Nonempty

/-- A certified physical claim: the evidence is consistent and entails the claimed property.
Requiring `Consistent` prevents vacuous entailment from an empty possible set being presented as
credible knowledge. -/
def CertifiedEntails (info : CorrelatedInformation State) (property : State → Prop) : Prop :=
  info.Consistent ∧ info.Entails property

/-! ## Extensionality and constructor projections -/

@[ext] theorem ext {first second : CorrelatedInformation State}
    (knowledge : first.knowledge = second.knowledge)
    (scopes : first.scopes = second.scopes)
    (possible : first.possible = second.possible)
    (diagram : first.diagram? = second.diagram?) : first = second := by
  cases first with
  | mk firstKnowledge firstScopes firstPossible firstDiagram =>
      cases second with
      | mk secondKnowledge secondScopes secondPossible secondDiagram =>
          simp_all

@[simp] theorem ofPossible_knowledge (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (possible : Set State) :
    (ofPossible knowledge scopes possible).knowledge = knowledge := rfl

@[simp] theorem ofPossible_scopes (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (possible : Set State) :
    (ofPossible knowledge scopes possible).scopes = scopes := rfl

@[simp] theorem ofPossible_possible (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (possible : Set State) :
    (ofPossible knowledge scopes possible).possible = possible := rfl

@[simp] theorem ofPossible_diagram? (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (possible : Set State) :
    (ofPossible knowledge scopes possible).diagram? = none := rfl

@[simp] theorem ofDiagram_knowledge (knowledge : ConfigurationKnowledge)
    (diagram : DiagramConfiguration) (possible : Set State) :
    (ofDiagram knowledge diagram possible).knowledge = knowledge := rfl

@[simp] theorem ofDiagram_scopes (knowledge : ConfigurationKnowledge)
    (diagram : DiagramConfiguration) (possible : Set State) :
    (ofDiagram knowledge diagram possible).scopes = diagram.scopeList := rfl

@[simp] theorem ofDiagram_possible (knowledge : ConfigurationKnowledge)
    (diagram : DiagramConfiguration) (possible : Set State) :
    (ofDiagram knowledge diagram possible).possible = possible := rfl

@[simp] theorem ofDiagram_diagram? (knowledge : ConfigurationKnowledge)
    (diagram : DiagramConfiguration) (possible : Set State) :
    (ofDiagram knowledge diagram possible).diagram? = some diagram := rfl

/-- The diagram-attached constructor retains exactly the supplied original diagram and its derived
statement scopes. -/
theorem ofDiagram_recovers (knowledge : ConfigurationKnowledge)
    (diagram : DiagramConfiguration) (possible : Set State) :
    (ofDiagram knowledge diagram possible).knowledge = knowledge ∧
      (ofDiagram knowledge diagram possible).diagram? = some diagram ∧
      (ofDiagram knowledge diagram possible).scopes = diagram.scopeList :=
  ⟨rfl, rfl, rfl⟩

/-- An attached diagram satisfies the attachment invariant by construction. -/
theorem ofDiagram_retainsDiagram (knowledge : ConfigurationKnowledge)
    (diagram : DiagramConfiguration) (possible : Set State) :
    (ofDiagram knowledge diagram possible).RetainsDiagram :=
  rfl

/-- Every scope in the summary of a diagram-attached carrier annotates an original bond or
atom-configuration statement of the retained diagram. -/
theorem ofDiagram_scope_attached (knowledge : ConfigurationKnowledge)
    (diagram : DiagramConfiguration) (possible : Set State)
    {scope : DiagramConfigurationScope}
    (member : scope ∈ (ofDiagram knowledge diagram possible).scopes) :
    (∃ bond ∈ diagram.bonds, bond.scope = scope) ∨
      (∃ configuration ∈ diagram.atomConfigurations,
        configuration.scope = scope) := by
  have inList : scope ∈ diagram.scopeList := by simpa [ofDiagram] using member
  exact (DiagramConfiguration.mem_scopeList_iff diagram scope).mp inList

@[simp] theorem singleton_knowledge (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    (singleton knowledge scopes state).knowledge = knowledge := rfl

@[simp] theorem singleton_scopes (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    (singleton knowledge scopes state).scopes = scopes := rfl

@[simp] theorem singleton_possible (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    (singleton knowledge scopes state).possible = {state} := rfl

@[simp] theorem mem_singleton_iff (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state target : State) :
    target ∈ (singleton knowledge scopes state).possible ↔ target = state :=
  Set.mem_singleton_iff

@[simp] theorem universal_knowledge (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) :
    (universal knowledge scopes : CorrelatedInformation State).knowledge = knowledge := rfl

@[simp] theorem universal_scopes (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) :
    (universal knowledge scopes : CorrelatedInformation State).scopes = scopes := rfl

@[simp] theorem universal_possible (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) :
    (universal knowledge scopes : CorrelatedInformation State).possible = Set.univ := rfl

@[simp] theorem mem_universal_iff (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    state ∈ (universal knowledge scopes : CorrelatedInformation State).possible ↔ True :=
  Iff.rfl

@[simp] theorem whollyUnspecified_knowledge (scopes : List DiagramConfigurationScope) :
    (whollyUnspecified (State := State) scopes).knowledge =
      ConfigurationKnowledge.whollyUnspecified := rfl

@[simp] theorem whollyUnspecified_scopes (scopes : List DiagramConfigurationScope) :
    (whollyUnspecified (State := State) scopes).scopes = scopes := rfl

@[simp] theorem whollyUnspecified_possible (scopes : List DiagramConfigurationScope) :
    (whollyUnspecified (State := State) scopes).possible = Set.univ := rfl

@[simp] theorem singleton_diagram? (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    (singleton knowledge scopes state).diagram? = none := rfl

@[simp] theorem universal_diagram? (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) :
    (universal knowledge scopes : CorrelatedInformation State).diagram? = none := rfl

@[simp] theorem whollyUnspecified_diagram? (scopes : List DiagramConfigurationScope) :
    (whollyUnspecified (State := State) scopes).diagram? = none := rfl

/-! ## Exact recovery of every tag and every scope list -/

/-- Every one of the eight `ConfigurationKnowledge` tags occurs in `allKnowledgeStates`. -/
theorem knowledge_mem_allKnowledgeStates (knowledge : ConfigurationKnowledge) :
    knowledge ∈ allKnowledgeStates := by
  cases knowledge <;> simp [allKnowledgeStates]

/-- Every retained knowledge tag is one of the eight declared tags.  Combined with
`knowledge_mem_allKnowledgeStates`, this is exact recovery of the tag alphabet. -/
theorem knowledge_classified (info : CorrelatedInformation State) :
    ∃ knowledge : ConfigurationKnowledge,
      knowledge ∈ allKnowledgeStates ∧ info.knowledge = knowledge :=
  ⟨info.knowledge, knowledge_mem_allKnowledgeStates info.knowledge, rfl⟩

/-- The singleton constructor recovers exactly the supplied tag and scope list.  In particular all
`relative`/`racemic` group identifiers in the scopes are preserved unchanged. -/
theorem singleton_recovers_knowledge_scopes (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    (singleton knowledge scopes state).knowledge = knowledge ∧
      (singleton knowledge scopes state).scopes = scopes :=
  ⟨rfl, rfl⟩

/-- The universal constructor recovers exactly the supplied tag and scope list. -/
theorem universal_recovers_knowledge_scopes (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) :
    (universal knowledge scopes : CorrelatedInformation State).knowledge = knowledge ∧
      (universal knowledge scopes : CorrelatedInformation State).scopes = scopes :=
  ⟨rfl, rfl⟩

/-- The group identifier carried by a configuration scope, if any.  `absolute` and `unknown`
carry no group identifier. -/
def scopeGroup? : DiagramConfigurationScope → Option ℕ
  | .absolute => none
  | .relative group => some group
  | .racemic group => some group
  | .unknown => none

@[simp] theorem scopeGroup?_relative (group : ℕ) :
    scopeGroup? (.relative group) = some group := rfl

@[simp] theorem scopeGroup?_racemic (group : ℕ) :
    scopeGroup? (.racemic group) = some group := rfl

@[simp] theorem scopeGroup?_absolute : scopeGroup? (.absolute : DiagramConfigurationScope) = none :=
  rfl

@[simp] theorem scopeGroup?_unknown : scopeGroup? (.unknown : DiagramConfigurationScope) = none :=
  rfl

/-! ## Restriction: membership, preservation, commutation, idempotence -/

@[simp] theorem restrict_knowledge (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).knowledge = info.knowledge := rfl

@[simp] theorem restrict_scopes (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).scopes = info.scopes := rfl

@[simp] theorem restrict_possible (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).possible = info.possible ∩ constraint := rfl

@[simp] theorem restrict_diagram? (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).diagram? = info.diagram? := rfl

/-- Restriction preserves the original diagram attachment exactly. -/
theorem restrict_retainsDiagram (info : CorrelatedInformation State)
    (constraint : Set State) (retains : info.RetainsDiagram) :
    (info.restrict constraint).RetainsDiagram := by
  simpa [RetainsDiagram, restrict] using retains

/-- Membership after restriction is exactly the conjunction of prior membership and satisfaction
of the explicit physical constraint. -/
@[simp] theorem mem_restrict_iff (info : CorrelatedInformation State)
    (constraint : Set State) (state : State) :
    state ∈ (info.restrict constraint).possible ↔
      state ∈ info.possible ∧ state ∈ constraint :=
  Set.mem_inter_iff state info.possible constraint

/-- Restriction preserves the knowledge tag exactly. -/
theorem restrict_preserves_knowledge (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).knowledge = info.knowledge := rfl

/-- Restriction preserves the whole scope list exactly, hence every relative/racemic group
identifier. -/
theorem restrict_preserves_scopes (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).scopes = info.scopes := rfl

/-- Restriction preserves all group identifiers appearing in the scopes. -/
theorem restrict_preserves_scopeGroups (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).scopes.map scopeGroup? =
      info.scopes.map scopeGroup? := rfl

/-- Restriction preserves knowledge, scope summary, and original-diagram attachment together. -/
theorem restrict_recovers_metadata (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).knowledge = info.knowledge ∧
      (info.restrict constraint).scopes = info.scopes ∧
      (info.restrict constraint).diagram? = info.diagram? :=
  ⟨rfl, rfl, rfl⟩

/-- Restriction never adds possible states. -/
theorem restrict_possible_subset (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).possible ⊆ info.possible :=
  fun _ member => member.1

/-- Restricting by two constraints consecutively is restriction by their intersection. -/
theorem restrict_restrict_eq (info : CorrelatedInformation State)
    (first second : Set State) :
    (info.restrict first).restrict second = info.restrict (first ∩ second) := by
  apply ext
  · rfl
  · rfl
  · ext state
    simp [restrict, Set.inter_assoc]
  · rfl

/-- Restrictions commute. -/
theorem restrict_restrict_comm (info : CorrelatedInformation State)
    (first second : Set State) :
    (info.restrict first).restrict second =
      (info.restrict second).restrict first := by
  rw [restrict_restrict_eq, restrict_restrict_eq, Set.inter_comm]

/-- Restriction is idempotent. -/
theorem restrict_idempotent (info : CorrelatedInformation State)
    (constraint : Set State) :
    (info.restrict constraint).restrict constraint = info.restrict constraint := by
  apply ext
  · rfl
  · rfl
  · ext state
    simp [restrict]
  · rfl

/-- Restriction by the universal constraint changes nothing. -/
theorem restrict_univ (info : CorrelatedInformation State) :
    info.restrict Set.univ = info := by
  apply ext
  · rfl
  · rfl
  · ext state
    simp [restrict]
  · rfl

/-! ## Entailment and restriction -/

/-- Entailment transfers to any restriction of the evidence. -/
theorem entails_restrict {info : CorrelatedInformation State} {property : State → Prop}
    (entails : info.Entails property) (constraint : Set State) :
    (info.restrict constraint).Entails property :=
  fun state member => entails state member.1

/-- Entailment after restriction is exactly universal satisfaction on the intersected set. -/
theorem entails_restrict_iff (info : CorrelatedInformation State)
    (constraint : Set State) (property : State → Prop) :
    (info.restrict constraint).Entails property ↔
      ∀ state : State, state ∈ info.possible ∩ constraint → property state :=
  Iff.rfl

/-- Exact entailment from a singleton. -/
@[simp] theorem singleton_entails_iff (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) (property : State → Prop) :
    (singleton knowledge scopes state).Entails property ↔ property state := by
  constructor
  · intro entails
    exact entails state (by simp)
  · intro satisfied target member
    have targetEq : target = state := by simpa using member
    rw [targetEq]
    exact satisfied

@[simp] theorem universal_entails_iff (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (property : State → Prop) :
    (universal knowledge scopes : CorrelatedInformation State).Entails property ↔
      ∀ state : State, property state := by
  constructor
  · intro entails state
    exact entails state (by simp)
  · intro satisfies state _
    exact satisfies state

/-! ## Consistency and the non-vacuous-certification boundary -/

@[simp] theorem consistent_iff (info : CorrelatedInformation State) :
    info.Consistent ↔ info.possible.Nonempty := Iff.rfl

@[simp] theorem singleton_consistent (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) (state : State) :
    (singleton knowledge scopes state).Consistent :=
  ⟨state, by simp⟩

/-- Universal information is consistent exactly when the state type is inhabited.  No topology,
measure, or physical admissibility is asserted. -/
theorem universal_consistent [Nonempty State] (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope) :
    (universal knowledge scopes : CorrelatedInformation State).Consistent := by
  obtain ⟨state⟩ := (inferInstance : Nonempty State)
  exact ⟨state, by simp⟩

theorem whollyUnspecified_consistent [Nonempty State]
    (scopes : List DiagramConfigurationScope) :
    (whollyUnspecified (State := State) scopes).Consistent :=
  universal_consistent (State := State) ConfigurationKnowledge.whollyUnspecified scopes

/-- The false proposition is entailed exactly when the joint possible set is empty.  In
particular, vacuous entailment is a symptom of inconsistent evidence, not of knowledge. -/
theorem entailsFalse_iff_empty (info : CorrelatedInformation State) :
    info.Entails (fun _ : State => False) ↔ info.possible = ∅ := by
  constructor
  · intro entails
    exact Set.eq_empty_iff_forall_notMem.mpr
      (fun state member => entails state member)
  · intro empty state member
    rw [empty] at member
    simp at member

/-- Consistency is exactly the negation of vacuous entailment of false. -/
theorem consistent_iff_not_entailsFalse (info : CorrelatedInformation State) :
    info.Consistent ↔ ¬ info.Entails (fun _ : State => False) := by
  rw [entailsFalse_iff_empty]
  constructor
  · rintro ⟨state, member⟩ empty
    rw [empty] at member
    simp at member
  · intro notEntails
    by_contra notConsistent
    apply notEntails
    exact Set.eq_empty_iff_forall_notMem.mpr
      (fun state member => notConsistent ⟨state, member⟩)

/-- Inconsistent evidence has an empty joint possible set. -/
theorem possible_eq_empty_of_not_consistent (info : CorrelatedInformation State)
    (notConsistent : ¬ info.Consistent) :
    info.possible = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr
    (fun state member => notConsistent ⟨state, member⟩)

/-- Conversely, an empty joint possible set is inconsistent evidence. -/
theorem not_consistent_of_possible_eq_empty (info : CorrelatedInformation State)
    (empty : info.possible = ∅) :
    ¬ info.Consistent := by
  rw [consistent_iff, empty]
  rintro ⟨state, member⟩
  simp at member

/-- A certified physical claim cannot be the vacuous entailment of false. -/
theorem not_certifiedEntails_false (info : CorrelatedInformation State) :
    ¬ info.CertifiedEntails (fun _ : State => False) := by
  rintro ⟨consistent, entails⟩
  exact (consistent_iff_not_entailsFalse info).mp consistent entails

/-- A certified physical claim yields consistency. -/
theorem certifiedEntails_consistent {info : CorrelatedInformation State}
    {property : State → Prop} (certified : info.CertifiedEntails property) :
    info.Consistent :=
  certified.1

/-- A certified physical claim yields entailment. -/
theorem certifiedEntails_entails {info : CorrelatedInformation State}
    {property : State → Prop} (certified : info.CertifiedEntails property) :
    info.Entails property :=
  certified.2

/-- Restriction preserves a certified physical claim provided the restricted evidence remains
nonempty.  The nonemptiness hypothesis is essential: an inconsistent restriction must not certify
physical facts vacuously. -/
theorem certifiedEntails_restrict {info : CorrelatedInformation State}
    {property : State → Prop} {constraint : Set State}
    (certified : info.CertifiedEntails property)
    (nonempty : (info.possible ∩ constraint).Nonempty) :
    (info.restrict constraint).CertifiedEntails property :=
  ⟨nonempty, entails_restrict certified.2 constraint⟩

/-! ## Transport: tags, scopes, membership in both directions, and inverses -/

@[simp] theorem transport_knowledge {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) :
    (info.transport equivalent).knowledge = info.knowledge := rfl

@[simp] theorem transport_scopes {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) :
    (info.transport equivalent).scopes = info.scopes := rfl

@[simp] theorem transport_possible {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) :
    (info.transport equivalent).possible = equivalent '' info.possible := rfl

@[simp] theorem transport_diagram? {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) :
    (info.transport equivalent).diagram? = info.diagram? := rfl

/-- Transport preserves the original diagram attachment exactly. -/
theorem transport_retainsDiagram {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) (retains : info.RetainsDiagram) :
    (info.transport equivalent).RetainsDiagram := by
  simpa [RetainsDiagram, transport] using retains

/-- Transport preserves knowledge, scope summary, group identifiers, and original-diagram
attachment together. -/
theorem transport_recovers_metadata {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) :
    (info.transport equivalent).knowledge = info.knowledge ∧
      (info.transport equivalent).scopes = info.scopes ∧
      (info.transport equivalent).scopes.map scopeGroup? =
        info.scopes.map scopeGroup? ∧
      (info.transport equivalent).diagram? = info.diagram? :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Membership after transport, in the forward direction: a transported state is possible exactly
when its inverse image was possible. -/
theorem mem_transport_iff {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) (state : Other) :
    state ∈ (info.transport equivalent).possible ↔
      equivalent.symm state ∈ info.possible := by
  constructor
  · rintro ⟨source, sourceMember, mapped⟩
    rw [← mapped, Equiv.symm_apply_apply]
    exact sourceMember
  · intro inverseMember
    exact ⟨equivalent.symm state, inverseMember, equivalent.apply_symm_apply state⟩

/-- Membership of an image state in the transported joint set, in both directions. -/
theorem transport_mem_iff_source {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) (state : State) :
    equivalent state ∈ (info.transport equivalent).possible ↔
      state ∈ info.possible := by
  rw [mem_transport_iff, Equiv.symm_apply_apply]

/-- Transport by an equivalence and then by its inverse recovers the original information,
including the exact joint possible set. -/
theorem transport_symm_transport {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) :
    (info.transport equivalent).transport equivalent.symm = info := by
  apply ext
  · rfl
  · rfl
  · ext state
    constructor
    · rintro ⟨other, ⟨source, sourceMember, mapped⟩, back⟩
      rw [← back, ← mapped, Equiv.symm_apply_apply]
      exact sourceMember
    · intro member
      exact ⟨equivalent state, ⟨state, member, rfl⟩, by simp⟩
  · rfl

/-- Transport by the inverse equivalence and then by the equivalence recovers the original
information. -/
theorem transport_transport_symm {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation Other) :
    (info.transport equivalent.symm).transport equivalent = info := by
  apply ext
  · rfl
  · rfl
  · ext state
    constructor
    · rintro ⟨source, ⟨other, otherMember, back⟩, mapped⟩
      rw [← mapped, ← back, Equiv.apply_symm_apply]
      exact otherMember
    · intro member
      exact ⟨equivalent.symm state, ⟨state, member, rfl⟩, by simp⟩
  · rfl

/-- Entailment is preserved by transport in the forward direction. -/
theorem entails_transport {Other : Type*} (equivalent : State ≃ Other)
    (info : CorrelatedInformation State) (property : Other → Prop)
    (entails : info.Entails fun state => property (equivalent state)) :
    (info.transport equivalent).Entails property := by
  intro state member
  rw [mem_transport_iff] at member
  simpa using entails (equivalent.symm state) member

end CorrelatedInformation

/-! ## A concrete two-coordinate counterexample

The state type is `Bool × Bool`.  The diagonal joint set `{(false,false),(true,true)}` and the
anti-diagonal joint set `{(false,true),(true,false)}` have identical projections onto each
coordinate, hence identical independent marginal sets and identical product reconstructions.
They are nevertheless different joint sets.  Consequently no function of the two projections can
recover an arbitrary joint possible set.  The two joint sets are fully representable as
`CorrelatedInformation` values, so correlation is retained in this representation.
-/

namespace TwoCoordinateCorrelation

/-- The correlated diagonal joint set. -/
def diagonal : Set (Bool × Bool) :=
  {point | point.1 = point.2}

/-- The anti-correlated joint set. -/
def antiDiagonal : Set (Bool × Bool) :=
  {point | point.1 ≠ point.2}

/-- Projection of a joint set onto the first coordinate. -/
def firstProjection (possible : Set (Bool × Bool)) : Set Bool :=
  Prod.fst '' possible

/-- Projection of a joint set onto the second coordinate. -/
def secondProjection (possible : Set (Bool × Bool)) : Set Bool :=
  Prod.snd '' possible

/-- The product reconstruction induced by the two independent coordinate projections.  This is the
strongest information recoverable from the marginals alone. -/
def productOfProjections (possible : Set (Bool × Bool)) : Set (Bool × Bool) :=
  {point | point.1 ∈ firstProjection possible ∧ point.2 ∈ secondProjection possible}

@[simp] theorem mem_firstProjection_iff (possible : Set (Bool × Bool)) (value : Bool) :
    value ∈ firstProjection possible ↔ ∃ point ∈ possible, point.1 = value :=
  Iff.rfl

@[simp] theorem mem_secondProjection_iff (possible : Set (Bool × Bool)) (value : Bool) :
    value ∈ secondProjection possible ↔ ∃ point ∈ possible, point.2 = value :=
  Iff.rfl

@[simp] theorem mem_diagonal_iff (point : Bool × Bool) :
    point ∈ diagonal ↔ point.1 = point.2 :=
  Iff.rfl

@[simp] theorem mem_antiDiagonal_iff (point : Bool × Bool) :
    point ∈ antiDiagonal ↔ point.1 ≠ point.2 :=
  Iff.rfl

/-- Both coordinate projections of the diagonal joint set are the full two-element set. -/
@[simp] theorem firstProjection_diagonal : firstProjection diagonal = Set.univ := by
  ext value
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨(value, value), by simp [diagonal], rfl⟩

@[simp] theorem secondProjection_diagonal : secondProjection diagonal = Set.univ := by
  ext value
  constructor
  · intro _
    trivial
  · intro _
    exact ⟨(value, value), by simp [diagonal], rfl⟩

/-- Both coordinate projections of the anti-diagonal joint set are also the full two-element set. -/
@[simp] theorem firstProjection_antiDiagonal : firstProjection antiDiagonal = Set.univ := by
  ext value
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨(value, !value), ?_, rfl⟩
    cases value <;> simp [antiDiagonal]

@[simp] theorem secondProjection_antiDiagonal : secondProjection antiDiagonal = Set.univ := by
  ext value
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨(!value, value), ?_, rfl⟩
    cases value <;> simp [antiDiagonal]

/-- The two marginal projection sets are identical for the diagonal and anti-diagonal joints. -/
theorem marginal_projections_identical :
    firstProjection diagonal = firstProjection antiDiagonal ∧
      secondProjection diagonal = secondProjection antiDiagonal :=
  ⟨by simp, by simp⟩

/-- The product reconstruction from the marginals is the same for both joint sets. -/
@[simp] theorem productOfProjections_diagonal :
    productOfProjections diagonal = Set.univ := by
  ext point
  simp [productOfProjections]

@[simp] theorem productOfProjections_antiDiagonal :
    productOfProjections antiDiagonal = Set.univ := by
  ext point
  simp [productOfProjections]

theorem productOfProjections_equal :
    productOfProjections diagonal = productOfProjections antiDiagonal := by
  rw [productOfProjections_diagonal, productOfProjections_antiDiagonal]

/-- The two joint sets are genuinely different: the pair `(false, true)` is anti-diagonal but not
diagonal. -/
theorem diagonal_ne_antiDiagonal : diagonal ≠ antiDiagonal := by
  intro equal
  have member : (false, true) ∈ diagonal := by
    rw [equal]
    simp [antiDiagonal]
  simp [diagonal] at member

/-- The diagonal joint set is not the product of its own coordinate marginals. -/
theorem diagonal_not_productOfProjections :
    diagonal ≠ productOfProjections diagonal := by
  intro equal
  have member : (false, true) ∈ productOfProjections diagonal := by
    rw [productOfProjections_diagonal]
    exact Set.mem_univ _
  rw [← equal] at member
  simp [diagonal] at member

/-- The anti-diagonal joint set is not the product of its own coordinate marginals. -/
theorem antiDiagonal_not_productOfProjections :
    antiDiagonal ≠ productOfProjections antiDiagonal := by
  intro equal
  have member : (false, false) ∈ productOfProjections antiDiagonal := by
    rw [productOfProjections_antiDiagonal]
    exact Set.mem_univ _
  rw [← equal] at member
  simp [antiDiagonal] at member

/-- Summary of the loss: identical marginals and identical product reconstructions, but different
joint possible sets, neither of which equals its product reconstruction. -/
theorem projections_lose_correlation :
    firstProjection diagonal = firstProjection antiDiagonal ∧
      secondProjection diagonal = secondProjection antiDiagonal ∧
      productOfProjections diagonal = productOfProjections antiDiagonal ∧
      diagonal ≠ antiDiagonal ∧
      diagonal ≠ productOfProjections diagonal :=
  ⟨marginal_projections_identical.1, marginal_projections_identical.2,
    productOfProjections_equal, diagonal_ne_antiDiagonal,
    diagonal_not_productOfProjections⟩

/-- No function of the two coordinate projections can recover every joint possible set: the
diagonal and anti-diagonal joints have equal projections but are distinct. -/
theorem no_reconstruction_from_projections :
    ¬ ∃ reconstruct : Set Bool → Set Bool → Set (Bool × Bool),
        ∀ possible : Set (Bool × Bool),
          reconstruct (firstProjection possible) (secondProjection possible) = possible := by
  rintro ⟨reconstruct, recovers⟩
  have sameInputs :
      reconstruct (firstProjection diagonal) (secondProjection diagonal) =
        reconstruct (firstProjection antiDiagonal) (secondProjection antiDiagonal) := by
    rw [firstProjection_diagonal, firstProjection_antiDiagonal,
      secondProjection_diagonal, secondProjection_antiDiagonal]
  have diagonalRecovered := recovers diagonal
  have antiDiagonalRecovered := recovers antiDiagonal
  rw [diagonalRecovered, antiDiagonalRecovered] at sameInputs
  exact diagonal_ne_antiDiagonal sameInputs

/-- The correlated diagonal joint possible set represented as stereochemical information.  The
knowledge tag is retained metadata only; no theorem here derives it from `possible`. -/
def diagonalInformation : CorrelatedInformation (Bool × Bool) :=
  CorrelatedInformation.ofPossible ConfigurationKnowledge.experimentallyUnknown [] diagonal

/-- The anti-correlated joint possible set represented at the same knowledge tag. -/
def antiDiagonalInformation : CorrelatedInformation (Bool × Bool) :=
  CorrelatedInformation.ofPossible ConfigurationKnowledge.experimentallyUnknown [] antiDiagonal

/-- The joint representation retains both correlation and the distinction that the independent
coordinate projections lose. -/
theorem joint_information_retains_correlation :
    diagonalInformation.possible ≠ antiDiagonalInformation.possible ∧
      productOfProjections diagonalInformation.possible =
        productOfProjections antiDiagonalInformation.possible := by
  constructor
  · simpa [diagonalInformation, antiDiagonalInformation] using diagonal_ne_antiDiagonal
  · simp [diagonalInformation, antiDiagonalInformation]

/-- The diagonal information entails the correlation between its two coordinates. -/
theorem diagonalInformation_entails_correlation :
    diagonalInformation.Entails (fun point : Bool × Bool => point.1 = point.2) := by
  intro point member
  simpa [diagonalInformation] using member

/-- The anti-diagonal information entails anti-correlation. -/
theorem antiDiagonalInformation_entails_anticorrelation :
    antiDiagonalInformation.Entails (fun point : Bool × Bool => point.1 ≠ point.2) := by
  intro point member
  simpa [antiDiagonalInformation] using member

/-- An explicit physical constraint: the first coordinate is `true`. -/
def firstCoordinateTrue : Set (Bool × Bool) :=
  {point | point.1 = true}

/-- Restricting the diagonal information to `firstCoordinateTrue` leaves exactly the state
`(true, true)`. -/
theorem restrict_diagonal_firstCoordinateTrue :
    (diagonalInformation.restrict firstCoordinateTrue).possible =
      ({(true, true)} : Set (Bool × Bool)) := by
  ext point
  constructor
  · rintro ⟨correlated, firstTrue⟩
    have coordinateEq : point.1 = point.2 := by simpa [diagonal] using correlated
    have firstValue : point.1 = true := by simpa [firstCoordinateTrue] using firstTrue
    have secondValue : point.2 = true := by
      rw [← coordinateEq]
      exact firstValue
    have pointEq : point = (true, true) := by
      cases point with
      | mk first second => simp_all
    rw [pointEq]
    simp
  · intro member
    have pointEq : point = (true, true) := by simpa using member
    rw [pointEq]
    exact ⟨by simp [diagonalInformation, diagonal], by simp [firstCoordinateTrue]⟩

/-- Restriction preserves the tag and the (empty) scope list of the counterexample. -/
theorem restrict_diagonal_metadata :
    (diagonalInformation.restrict firstCoordinateTrue).knowledge =
        ConfigurationKnowledge.experimentallyUnknown ∧
      (diagonalInformation.restrict firstCoordinateTrue).scopes = [] :=
  ⟨rfl, rfl⟩

end TwoCoordinateCorrelation

/-! ## Source-bound alias

This is the requested reuse hook for the real-conformation representation: the arbitrary state
type is instantiated by the existing `SourceConformation` of a certified source.  No geometry,
descriptor, or conformance claim is added here; the alias merely specializes the carrier. -/

/-- Correlated stereochemical information over the real source-indexed conformations of a
certified chemical input. -/
abbrev SourceCorrelatedInformation (source : CertifiedAuthoritativeChemicalInput) : Type :=
  CorrelatedInformation (SourceConformation source)

/-- The original diagram retained by a certified source.  This is the source's own channel, not a
reconstruction. -/
def sourceDiagram? (source : CertifiedAuthoritativeChemicalInput) :
    Option DiagramConfiguration :=
  source.input.diagram?

/-- The scope summary attached to the source's original diagram, if any.  It is derived from the
diagram's statement list (bonds and atom configurations); it is not synthesized from a bare scope
list. -/
def sourceScopeList (source : CertifiedAuthoritativeChemicalInput) :
    List DiagramConfigurationScope :=
  match sourceDiagram? source with
  | some diagram => diagram.scopeList
  | none => []

/-- Source-bound joint information whose scope summary and retained diagram come from the original
certified source.  The original `DiagramConfiguration` (when present) is retained exactly, so the
attachment of each scope to a source bond or atom-configuration statement is preserved. -/
def ofSource (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    SourceCorrelatedInformation source :=
  { knowledge := knowledge
    scopes := sourceScopeList source
    possible := possible
    diagram? := sourceDiagram? source }

@[simp] theorem sourceDiagram?_eq (source : CertifiedAuthoritativeChemicalInput) :
    sourceDiagram? source = source.input.diagram? := rfl

@[simp] theorem ofSource_diagram? (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    (ofSource source knowledge possible).diagram? = source.input.diagram? := rfl

@[simp] theorem ofSource_scopes (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    (ofSource source knowledge possible).scopes = sourceScopeList source := rfl

@[simp] theorem ofSource_knowledge (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    (ofSource source knowledge possible).knowledge = knowledge := rfl

@[simp] theorem ofSource_possible (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    (ofSource source knowledge possible).possible = possible := rfl

/-- Exact recovery of the supplied knowledge tag, the source's original diagram, and the derived
source scope summary. -/
theorem ofSource_recovers (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    (ofSource source knowledge possible).knowledge = knowledge ∧
      (ofSource source knowledge possible).diagram? = source.input.diagram? ∧
      (ofSource source knowledge possible).scopes = sourceScopeList source :=
  ⟨rfl, rfl, rfl⟩

/-- The original source diagram is retained exactly: the carrier does not replace, reinterpret, or
drop it. -/
theorem ofSource_retains_source_diagram (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    (ofSource source knowledge possible).diagram? = source.input.diagram? := rfl

/-- Source-bound information constructed by `ofSource` satisfies the diagram-attachment
invariant. -/
theorem ofSource_retainsDiagram (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source)) :
    (ofSource source knowledge possible).RetainsDiagram := by
  cases observed : source.input.diagram? with
  | none =>
      simp [CorrelatedInformation.RetainsDiagram, ofSource, sourceDiagram?, observed]
  | some diagram =>
      simp [CorrelatedInformation.RetainsDiagram, ofSource, sourceDiagram?, sourceScopeList,
        observed]

/-- Every scope in a source-attached summary annotates a bond or atom-configuration statement of the
original source diagram that is retained in `diagram?`. -/
theorem ofSource_scope_attached (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (possible : Set (SourceConformation source))
    {scope : DiagramConfigurationScope}
    (member : scope ∈ (ofSource source knowledge possible).scopes) :
    ∃ diagram : DiagramConfiguration,
      source.input.diagram? = some diagram ∧
        ((∃ bond ∈ diagram.bonds, bond.scope = scope) ∨
          (∃ configuration ∈ diagram.atomConfigurations,
            configuration.scope = scope)) := by
  cases observed : source.input.diagram? with
  | none =>
      simp [ofSource, sourceScopeList, sourceDiagram?, observed] at member
  | some diagram =>
      refine ⟨diagram, rfl, ?_⟩
      have inList : scope ∈ diagram.scopeList := by
        simpa [ofSource, sourceScopeList, sourceDiagram?, observed] using member
      exact (DiagramConfiguration.mem_scopeList_iff diagram scope).mp inList

/-- A singleton source-indexed conformation is consistent joint information. -/
theorem source_singleton_consistent (source : CertifiedAuthoritativeChemicalInput)
    (knowledge : ConfigurationKnowledge)
    (scopes : List DiagramConfigurationScope)
    (conformation : SourceConformation source) :
    (CorrelatedInformation.singleton knowledge scopes conformation :
      SourceCorrelatedInformation source).Consistent :=
  CorrelatedInformation.singleton_consistent knowledge scopes conformation

/-- Restriction of source-indexed information by a geometric or other physical constraint retains
the source-level knowledge tag exactly. -/
theorem source_restrict_knowledge (source : CertifiedAuthoritativeChemicalInput)
    (info : SourceCorrelatedInformation source) (constraint : Set (SourceConformation source)) :
    (info.restrict constraint).knowledge = info.knowledge := rfl

end OneCenter
end TetraStereo
