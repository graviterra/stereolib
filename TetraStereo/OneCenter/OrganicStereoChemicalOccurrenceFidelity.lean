import TetraStereo.OneCenter.OrganicStereoLipidAnnotationIngress
import TetraStereo.OneCenter.OrganicStereoSourceBoundResidueAssembly
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Chemically typed occurrence evidence above raw source metadata

The existing lipid / glycolipid records

* `LipidAnnotationIngress.SphingoidDoubleBondBinding`, and
* `GlycolipidCitationAdapter.Binding`

are *lossless* representations of supplied source metadata.  Their participant fields prove
endpoint incidence only: both resolved atoms occur in the participant list of a recorded source
interaction.  They deliberately say nothing about the interaction kind or bond order, and they do
not certify E/Z geometry, anomeric configuration, CIP description or chemical class.  Reading a
chemical-fidelity certificate out of them would be unsound.

This module adds the missing **typed** layer strictly above those records:

* `SemanticInteraction.TypedChemicalOccurrence` is the shared predicate: the participant list is
  exactly the ordered pair of endpoints **and** the kind is exactly
  `SemanticInteractionKind.covalent order`.  Both components are exact equations on the existing
  semantic interaction; there is no opaque "is chemically correct" proposition.
* `FiniteAtomInteractionHypergraph.SourceBinaryCovalentEdge` is the same evidence at the
  independent source-graph level, and
  `FiniteAtomInteractionHypergraph.encodeInteraction_typedChemicalOccurrence` proves that the
  exact existing source encoding (`encodeInteraction`) transports it to the index representation.
* `SphingoidDoubleBondSourceEvidence` builds an actual `SphingoidDoubleBondBinding` from a real
  source hyperedge whose two labels and covalent kind are supplied by the source graph, and
  derives a typed order-2 witness through that binding.
* The `TypedChemical` predicates for sphingoid double bonds and glycolipid citations expose the
  exact endpoint support and covalent order while using the records' own resolved atoms.  In
  particular the glycosidic predicate imposes **no** universal carbon/oxygen endpoint convention:
  the source citation's donor/acceptor atoms are used verbatim.
* A concrete hydrogen-bond fixture proves the separation is real: the raw endpoint-incidence
  content holds, while the typed predicate is false for every bond order.

Scope boundaries, stated as theorems rather than assumptions:

* Bond order does not determine E/Z: a typed sphingoid occurrence survives replacing `.E` by
  `.Z` (`SphingoidDoubleBondBinding.typedChemical_does_not_determine_EZ`).
* A glycosidic typed occurrence does not determine the supplied anomer
  (`GlycolipidCitationAdapter.Binding.typedChemical_does_not_determine_anomer`).

The genuine follow-up bridge is therefore geometric/priority evidence, not another bond-order
check: `SourceConfigurationChannels` names the actual spatial and diagram channels that such a
bridge must consume, and the report records the remaining obligation explicitly.
-/

/-! ## Shared exact endpoint support and covalent-order evidence -/

namespace SemanticInteraction

/-- Exact ordered binary endpoint support: the interaction's participant list is exactly the two
named atoms in the given order.  This is a structural equation on the existing interaction and
states nothing about the interaction kind. -/
def ExactBinaryEndpointSupport (interaction : SemanticInteraction)
    (first second : Nat) : Prop :=
  interaction.participants = [first, second]

/-- The interaction is exactly a `covalent` interaction of the given bond order. -/
def CovalentOrder (interaction : SemanticInteraction) (order : Nat) : Prop :=
  interaction.kind = SemanticInteractionKind.covalent order

/-- Shared chemically typed binary covalent occurrence.

Both fields are exact equations on the existing `SemanticInteraction`.  This is the common
evidence object for sphingoid double bonds and glycosidic links; it is deliberately not an
opaque correctness flag and it records no E/Z or anomeric configuration. -/
structure TypedChemicalOccurrence (interaction : SemanticInteraction)
    (first second order : Nat) : Prop where
  /-- The participants are exactly the ordered endpoint pair. -/
  endpoint_exact : interaction.participants = [first, second]
  /-- The interaction kind is exactly `covalent order`. -/
  covalent_exact : interaction.kind = SemanticInteractionKind.covalent order

/-- Raw endpoint incidence: both named atoms occur in the participant list.  This is precisely the
content supplied by the existing `source_participant` / `target_participant` fields.  It says
nothing about interaction kind, bond order or configuration. -/
def RawEndpointIncidence (interaction : SemanticInteraction)
    (first second : Nat) : Prop :=
  first ∈ interaction.participants ∧ second ∈ interaction.participants

/-- Exact endpoint support implies raw endpoint incidence. -/
theorem ExactBinaryEndpointSupport.rawEndpointIncidence
    {interaction : SemanticInteraction} {first second : Nat}
    (support : interaction.ExactBinaryEndpointSupport first second) :
    interaction.RawEndpointIncidence first second := by
  unfold ExactBinaryEndpointSupport at support
  unfold RawEndpointIncidence
  rw [support]
  exact ⟨by simp, by simp⟩

/-- A typed occurrence has exact endpoint support. -/
theorem TypedChemicalOccurrence.exactEndpointSupport
    {interaction : SemanticInteraction} {first second order : Nat}
    (typed : interaction.TypedChemicalOccurrence first second order) :
    interaction.ExactBinaryEndpointSupport first second :=
  typed.endpoint_exact

/-- A typed occurrence has raw endpoint incidence.  The converse fails in general; the
hydrogen-bond fixture below is a concrete counterexample. -/
theorem TypedChemicalOccurrence.rawEndpointIncidence
    {interaction : SemanticInteraction} {first second order : Nat}
    (typed : interaction.TypedChemicalOccurrence first second order) :
    interaction.RawEndpointIncidence first second :=
  ExactBinaryEndpointSupport.rawEndpointIncidence typed.endpoint_exact

/-- A typed occurrence records the stated covalent order. -/
theorem TypedChemicalOccurrence.covalentOrder
    {interaction : SemanticInteraction} {first second order : Nat}
    (typed : interaction.TypedChemicalOccurrence first second order) :
    interaction.CovalentOrder order :=
  typed.covalent_exact

end SemanticInteraction

/-! ## Transport through the exact existing source encoding -/

namespace FiniteAtomInteractionHypergraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Exact binary covalent source-edge data.  The source hyperedge's participant list is exactly
the two labels and its kind is exactly the actual covalent order. -/
def SourceBinaryCovalentEdge (edge : List V × SemanticInteractionKind)
    (first second : V) (order : Nat) : Prop :=
  edge.1 = [first, second] ∧ edge.2 = SemanticInteractionKind.covalent order

/-- The existing source encoding copies participant identities in order. -/
@[simp] theorem encodeInteraction_participants (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) :
    (encodeInteraction enumeration edge).participants =
      edge.1.map (fun atom => (enumeration atom).val) := rfl

/-- The existing source encoding copies the interaction kind verbatim. -/
@[simp] theorem encodeInteraction_kind (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) :
    (encodeInteraction enumeration edge).kind = edge.2 := rfl

/-- Transport of typed binary covalent evidence through the exact existing source encoding
`FiniteAtomInteractionHypergraph.encodeInteraction`: exact ordered endpoints become the
enumeration indices of the two labels, and the source kind is preserved literally. -/
theorem encodeInteraction_typedChemicalOccurrence
    (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) (first second : V) (order : Nat)
    (source : SourceBinaryCovalentEdge edge first second order) :
    SemanticInteraction.TypedChemicalOccurrence (encodeInteraction enumeration edge)
      (enumeration first).val (enumeration second).val order := by
  obtain ⟨endpointEq, kindEq⟩ := source
  constructor
  · simp [encodeInteraction, endpointEq]
  · simp [encodeInteraction, kindEq]

end FiniteAtomInteractionHypergraph

/-! ## Residue-ledger helpers for concrete source fixtures -/

namespace OrganicStereoChemicalOccurrenceFidelity

/-- A residue fragment with exactly two resolvable locants.  Locants are natural-number tokens;
every other token is unresolved.  The support is the two named atoms, so resolved incidence stays
inside the support by construction. -/
def twoLocantFragment {atomCount : Nat} (first second : Fin atomCount)
    (firstLocant secondLocant : Nat) : ResidueFragment Nat atomCount where
  support := {first, second}
  incidence locant :=
    if locant = firstLocant then some first
    else if locant = secondLocant then some second
    else none
  incidence_mem_support := by
    intro locant atom found
    by_cases firstCase : locant = firstLocant
    · rw [if_pos firstCase] at found
      simp only [Option.some.injEq] at found
      subst atom
      simp
    · rw [if_neg firstCase] at found
      by_cases secondCase : locant = secondLocant
      · rw [if_pos secondCase] at found
        simp only [Option.some.injEq] at found
        subst atom
        simp
      · rw [if_neg secondCase] at found
        cases found

/-- The first locant of a two-locant fragment resolves to the first atom. -/
theorem twoLocantFragment_incidence_first {atomCount : Nat} (first second : Fin atomCount)
    (firstLocant secondLocant : Nat) :
    (twoLocantFragment first second firstLocant secondLocant).incidence firstLocant =
      some first := by
  simp [twoLocantFragment]

/-- The second locant resolves to the second atom when the two locants are distinct. -/
theorem twoLocantFragment_incidence_second {atomCount : Nat} (first second : Fin atomCount)
    (firstLocant secondLocant : Nat) (distinct : firstLocant ≠ secondLocant) :
    (twoLocantFragment first second firstLocant secondLocant).incidence secondLocant =
      some second := by
  have notFirst : secondLocant ≠ firstLocant := fun equal => distinct equal.symm
  simp [twoLocantFragment, notFirst]

/-- A one-residue incidence ledger with an empty directed-link list.  Link endpoint obligations
are vacuous because there are no links. -/
def singleResidueLedger {input : CertifiedAuthoritativeChemicalInput}
    (fragment : ResidueFragment Nat input.input.molecule.atomCount) :
    ResidueIncidenceLedger Nat input where
  residueCount := 1
  residue := fun _ => fragment
  links := []
  link_source_mem := by
    intro link member
    exact absurd member (by simp)
  link_target_mem := by
    intro link member
    exact absurd member (by simp)

/-- The atom equivalence induced by the common source enumeration, typed directly at the certified
encoding's atom count.  It is the existing `encodedAtomEquiv`; no second enumeration is chosen. -/
abbrev encodedSourceAtomEquiv {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    V ≃ Fin (source.certifiedEncoding enumeration).input.molecule.atomCount :=
  OrganicStereoIndependentElectronicEncoding.encodedAtomEquiv source enumeration

/-- The encoded atom index has the same numeral as the source enumeration index. -/
@[simp] theorem encodedSourceAtomEquiv_val {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (atom : V) :
    (encodedSourceAtomEquiv source enumeration atom).val = (enumeration atom).val := rfl

/-- The encoded interaction index of a source interaction index, transported across the exact
interaction-length identity of the certified encoding. -/
def encodedInteractionIndex {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin source.interactions.length) :
    Fin (source.certifiedEncoding enumeration).input.molecule.interactions.length :=
  ⟨index.val, by
    simp [certifiedEncoding_interactions_length source enumeration, index.isLt]⟩

/-- The actual interaction at an encoded index is exactly the encoding of the source interaction
at the same index. -/
theorem certifiedEncoding_get_encoded {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin source.interactions.length) :
    (source.certifiedEncoding enumeration).input.molecule.interactions.get
        (encodedInteractionIndex source enumeration index) =
      FiniteAtomInteractionHypergraph.encodeInteraction enumeration
        (source.interactions.get index) := by
  have transported := certifiedEncoding_interactions_get source enumeration
    (encodedInteractionIndex source enumeration index)
  have indexEq : residueSourceInteractionIndex source enumeration
      (encodedInteractionIndex source enumeration index) = index :=
    Fin.ext rfl
  rw [indexEq] at transported
  exact transported

/-- Distinct source labels have distinct encoded atoms. -/
theorem encodedSourceAtomEquiv_ne {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {first second : V} (distinct : first ≠ second) :
    encodedSourceAtomEquiv source enumeration first ≠
      encodedSourceAtomEquiv source enumeration second := by
  intro equal
  exact distinct ((encodedSourceAtomEquiv source enumeration).injective equal)

end OrganicStereoChemicalOccurrenceFidelity

/-! ## Typed chemical evidence for the existing sphingoid binding -/

namespace LipidAnnotationIngress.SphingoidDoubleBondBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}
variable {residue : Fin ledger.residueCount}

/-- The binding's recorded interaction is an actual binary covalent occurrence of the stated order
between its own two resolved atoms.

This is strictly more than the binding's endpoint-incidence fields: it equates the participant
list with the ordered endpoint pair and equates the interaction kind with `covalent order`.  It
still records no E/Z configuration; `descriptor` is deliberately not consulted. -/
def TypedChemical (binding : SphingoidDoubleBondBinding input ledger residue)
    (order : Nat) : Prop :=
  SemanticInteraction.TypedChemicalOccurrence
    (input.input.molecule.interactions.get binding.interaction)
    binding.sourceAtom.val binding.targetAtom.val order

/-- Raw endpoint incidence supplied by the binding.  This is exactly its participant fields. -/
theorem rawEndpointIncidence (binding : SphingoidDoubleBondBinding input ledger residue) :
    SemanticInteraction.RawEndpointIncidence
      (input.input.molecule.interactions.get binding.interaction)
      binding.sourceAtom.val binding.targetAtom.val :=
  ⟨binding.source_participant, binding.target_participant⟩

/-- The typed predicate is exactly ordered endpoint support plus the covalent order. -/
theorem typedChemical_iff (binding : SphingoidDoubleBondBinding input ledger residue)
    (order : Nat) :
    binding.TypedChemical order ↔
      (input.input.molecule.interactions.get binding.interaction).participants =
          [binding.sourceAtom.val, binding.targetAtom.val] ∧
        (input.input.molecule.interactions.get binding.interaction).kind =
          SemanticInteractionKind.covalent order := by
  constructor
  · intro typed
    unfold LipidAnnotationIngress.SphingoidDoubleBondBinding.TypedChemical at typed
    exact ⟨typed.endpoint_exact, typed.covalent_exact⟩
  · intro parts
    exact ⟨parts.1, parts.2⟩

/-- Replace only the supplied E/Z descriptor.  Every endpoint, interaction and incidence field is
unchanged. -/
def withDescriptor (binding : SphingoidDoubleBondBinding input ledger residue)
    (descriptor : Glycolipid1997.EZ) :
    SphingoidDoubleBondBinding input ledger residue where
  sourceLocant := binding.sourceLocant
  targetLocant := binding.targetLocant
  descriptor := descriptor
  sourceAtom := binding.sourceAtom
  targetAtom := binding.targetAtom
  interaction := binding.interaction
  source_eq := binding.source_eq
  target_eq := binding.target_eq
  source_participant := binding.source_participant
  target_participant := binding.target_participant
  ordered := binding.ordered
  distinct_atoms := binding.distinct_atoms

/-- The typed chemical occurrence is independent of the supplied E/Z descriptor. -/
theorem typedChemical_withDescriptor_iff
    (binding : SphingoidDoubleBondBinding input ledger residue)
    (descriptor : Glycolipid1997.EZ) (order : Nat) :
    (binding.withDescriptor descriptor).TypedChemical order ↔ binding.TypedChemical order := by
  constructor <;> intro typed <;> exact typed

/-- **Negative chemical-fidelity result.**  A typed order-2 (or any-order) sphingoid double-bond
occurrence is compatible with both supplied E/Z labels.  Bond order alone therefore cannot certify
E/Z geometry; that requires a separate geometry/priority bridge. -/
theorem typedChemical_does_not_determine_EZ
    (binding : SphingoidDoubleBondBinding input ledger residue) (order : Nat)
    (typed : binding.TypedChemical order) :
    (binding.withDescriptor .E).TypedChemical order ∧
      (binding.withDescriptor .Z).TypedChemical order :=
  ⟨(binding.typedChemical_withDescriptor_iff .E order).mpr typed,
    (binding.typedChemical_withDescriptor_iff .Z order).mpr typed⟩

end LipidAnnotationIngress.SphingoidDoubleBondBinding

/-! ## Typed chemical evidence for the existing glycolipid citation binding -/

namespace GlycolipidCitationAdapter.Binding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- The bound glycosidic relation is an actual binary covalent occurrence of the supplied order
between the citation's own resolved donor and acceptor atoms.

There is deliberately no element test: in particular no universal carbon/oxygen endpoint pair is
imposed.  A glycosidic relation may identify donor and acceptor atoms across an intervening oxygen,
and non-oxygen glycosidic link types exist; the actual supplied atom/link convention is used. -/
def TypedChemical (binding : Binding input ledger) (order : Nat) : Prop :=
  SemanticInteraction.TypedChemicalOccurrence
    (input.input.molecule.interactions.get binding.interaction)
    binding.sourceAtom.val binding.targetAtom.val order

/-- Raw endpoint incidence supplied by the citation binding. -/
theorem rawEndpointIncidence (binding : Binding input ledger) :
    SemanticInteraction.RawEndpointIncidence
      (input.input.molecule.interactions.get binding.interaction)
      binding.sourceAtom.val binding.targetAtom.val :=
  ⟨binding.source_participant, binding.target_participant⟩

/-- The typed predicate is exactly ordered endpoint support plus the covalent order.  The statement
mentions no element, so it cannot smuggle in a universal C-O endpoint convention. -/
theorem typedChemical_iff (binding : Binding input ledger) (order : Nat) :
    binding.TypedChemical order ↔
      (input.input.molecule.interactions.get binding.interaction).participants =
          [binding.sourceAtom.val, binding.targetAtom.val] ∧
        (input.input.molecule.interactions.get binding.interaction).kind =
          SemanticInteractionKind.covalent order := by
  constructor
  · intro typed
    unfold GlycolipidCitationAdapter.Binding.TypedChemical at typed
    exact ⟨typed.endpoint_exact, typed.covalent_exact⟩
  · intro parts
    exact ⟨parts.1, parts.2⟩

/-- Replace only the supplied anomer metadata.  Every endpoint, interaction and incidence field is
unchanged. -/
def withAnomer (binding : Binding input ledger) (anomer : Glycolipid1997.Anomer) :
    Binding input ledger where
  citation := { binding.citation with anomer := anomer }
  sourceResidue := binding.sourceResidue
  targetResidue := binding.targetResidue
  interaction := binding.interaction
  sourceAtom := binding.sourceAtom
  targetAtom := binding.targetAtom
  source_eq := binding.source_eq
  target_eq := binding.target_eq
  source_participant := binding.source_participant
  target_participant := binding.target_participant

/-- The typed chemical occurrence is independent of the supplied anomer metadata. -/
theorem typedChemical_withAnomer_iff (binding : Binding input ledger)
    (anomer : Glycolipid1997.Anomer) (order : Nat) :
    (binding.withAnomer anomer).TypedChemical order ↔ binding.TypedChemical order := by
  constructor <;> intro typed <;> exact typed

/-- **Negative chemical-fidelity result.**  A typed glycosidic occurrence is compatible with both
supplied anomer labels.  Bond order alone therefore cannot certify an alpha/beta assignment; that
requires the separate anomeric-geometry/priority bridge. -/
theorem typedChemical_does_not_determine_anomer (binding : Binding input ledger)
    (order : Nat) (typed : binding.TypedChemical order) :
    (binding.withAnomer .alpha).TypedChemical order ∧
      (binding.withAnomer .beta).TypedChemical order :=
  ⟨(binding.typedChemical_withAnomer_iff .alpha order).mpr typed,
    (binding.typedChemical_withAnomer_iff .beta order).mpr typed⟩

end GlycolipidCitationAdapter.Binding

/-! ## Source-backed sphingoid double-bond evidence

The structure below is the producer side.  It does not take a typed predicate as a hypothesis:
it records the real source hyperedge (its ordered labels and its actual covalent kind), the
ledger resolutions, and then *constructs* the existing binding and derives the typed occurrence
through the exact source encoding. -/

namespace OrganicStereoChemicalOccurrenceFidelity

/-- Real source bond data for one sphingoid double bond.

`source.interactions.get edgeIndex` is the actual source hyperedge; `edge_support` and `edge_kind`
state that it is exactly the two supplied labels with the actual covalent order.  All remaining
fields are the same caller obligations as in `SphingoidDoubleBondBinding`. -/
structure SphingoidDoubleBondSourceEvidence
    {V : Type*} [DecidableEq V] [Fintype V]
    (source : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (ledger : ResidueIncidenceLedger Nat (source.certifiedEncoding enumeration))
    (residue : Fin ledger.residueCount) where
  /-- Index of the actual source hyperedge. -/
  edgeIndex : Fin source.interactions.length
  /-- First ordered source label. -/
  first : V
  /-- Second ordered source label. -/
  second : V
  /-- Actual covalent bond order of the source hyperedge. -/
  order : Nat
  /-- Supplied source locant of the first endpoint. -/
  sourceLocant : Nat
  /-- Supplied source locant of the second endpoint. -/
  targetLocant : Nat
  /-- Supplied E/Z annotation, retained verbatim and never derived from `order`. -/
  descriptor : Glycolipid1997.EZ
  /-- The source hyperedge has exactly the two ordered labels as participants. -/
  edge_support : (source.interactions.get edgeIndex).1 = [first, second]
  /-- The source hyperedge kind is exactly the actual covalent order. -/
  edge_kind : (source.interactions.get edgeIndex).2 =
    SemanticInteractionKind.covalent order
  /-- The first locant resolves to the encoded first label. -/
  source_eq : (ledger.residue residue).incidence sourceLocant =
    some (encodedSourceAtomEquiv source enumeration first)
  /-- The second locant resolves to the encoded second label. -/
  target_eq : (ledger.residue residue).incidence targetLocant =
    some (encodedSourceAtomEquiv source enumeration second)
  /-- The ordered locant obligation. -/
  ordered : sourceLocant < targetLocant
  /-- The two encoded endpoint atoms are distinct. -/
  distinct_atoms : encodedSourceAtomEquiv source enumeration first ≠
    encodedSourceAtomEquiv source enumeration second

namespace SphingoidDoubleBondSourceEvidence

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {source : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}
variable {ledger : ResidueIncidenceLedger Nat (source.certifiedEncoding enumeration)}
variable {residue : Fin ledger.residueCount}

/-- Construct the actual existing sphingoid binding from real source bond data.  The binding's
interaction is the encoded source hyperedge; both atoms are the encoded source labels. -/
def binding (evidence : SphingoidDoubleBondSourceEvidence source enumeration ledger residue) :
    LipidAnnotationIngress.SphingoidDoubleBondBinding
      (source.certifiedEncoding enumeration) ledger residue where
  sourceLocant := evidence.sourceLocant
  targetLocant := evidence.targetLocant
  descriptor := evidence.descriptor
  sourceAtom := encodedSourceAtomEquiv source enumeration evidence.first
  targetAtom := encodedSourceAtomEquiv source enumeration evidence.second
  interaction := encodedInteractionIndex source enumeration evidence.edgeIndex
  source_eq := evidence.source_eq
  target_eq := evidence.target_eq
  source_participant := by
    have hget := certifiedEncoding_get_encoded source enumeration evidence.edgeIndex
    rw [hget, FiniteAtomInteractionHypergraph.encodeInteraction_participants,
      evidence.edge_support]
    change (encodedSourceAtomEquiv source enumeration evidence.first).val ∈
      (enumeration evidence.first).val :: (enumeration evidence.second).val :: []
    exact List.Mem.head _
  target_participant := by
    have hget := certifiedEncoding_get_encoded source enumeration evidence.edgeIndex
    rw [hget, FiniteAtomInteractionHypergraph.encodeInteraction_participants,
      evidence.edge_support]
    change (encodedSourceAtomEquiv source enumeration evidence.second).val ∈
      (enumeration evidence.first).val :: (enumeration evidence.second).val :: []
    exact List.Mem.tail _ (List.Mem.head _)
  ordered := evidence.ordered
  distinct_atoms := evidence.distinct_atoms

@[simp] theorem binding_interaction (evidence :
    SphingoidDoubleBondSourceEvidence source enumeration ledger residue) :
    evidence.binding.interaction =
      encodedInteractionIndex source enumeration evidence.edgeIndex := rfl

@[simp] theorem binding_sourceAtom (evidence :
    SphingoidDoubleBondSourceEvidence source enumeration ledger residue) :
    evidence.binding.sourceAtom =
      encodedSourceAtomEquiv source enumeration evidence.first := rfl

@[simp] theorem binding_targetAtom (evidence :
    SphingoidDoubleBondSourceEvidence source enumeration ledger residue) :
    evidence.binding.targetAtom =
      encodedSourceAtomEquiv source enumeration evidence.second := rfl

/-- The constructed binding carries the typed chemical occurrence at the actual source order. -/
theorem typedChemical (evidence :
    SphingoidDoubleBondSourceEvidence source enumeration ledger residue) :
    evidence.binding.TypedChemical evidence.order := by
  unfold LipidAnnotationIngress.SphingoidDoubleBondBinding.TypedChemical
  have hget := certifiedEncoding_get_encoded source enumeration evidence.edgeIndex
  constructor
  · rw [binding_interaction, binding_sourceAtom, binding_targetAtom, hget,
      FiniteAtomInteractionHypergraph.encodeInteraction_participants,
      evidence.edge_support]
    rfl
  · rw [binding_interaction, hget,
      FiniteAtomInteractionHypergraph.encodeInteraction_kind]
    exact evidence.edge_kind

/-- The constructed binding's actual interaction kind equals the source order. -/
theorem interaction_kind_eq (evidence :
    SphingoidDoubleBondSourceEvidence source enumeration ledger residue) :
    ((source.certifiedEncoding enumeration).input.molecule.interactions.get
        evidence.binding.interaction).kind =
      SemanticInteractionKind.covalent evidence.order := by
  have typed := evidence.typedChemical
  unfold LipidAnnotationIngress.SphingoidDoubleBondBinding.TypedChemical at typed
  exact typed.covalent_exact

/-- Specialization to an order-two source bond. -/
theorem order_two_of_order_eq (evidence :
    SphingoidDoubleBondSourceEvidence source enumeration ledger residue)
    (orderEq : evidence.order = 2) :
    evidence.binding.TypedChemical 2 := by
  rw [← orderEq]
  exact evidence.typedChemical

/-- The sphingoid double-bond order-2 witness derived from real source bond data. -/
theorem interaction_kind_two (evidence :
    SphingoidDoubleBondSourceEvidence source enumeration ledger residue)
    (orderEq : evidence.order = 2) :
    ((source.certifiedEncoding enumeration).input.molecule.interactions.get
        evidence.binding.interaction).kind =
      SemanticInteractionKind.covalent 2 := by
  have kindEq := evidence.interaction_kind_eq
  rw [orderEq] at kindEq
  exact kindEq

end SphingoidDoubleBondSourceEvidence

/-! ## Concrete source-backed sphingoid double bond -/

/-- A carbon atom record used by the concrete fixtures. -/
def carbonAtom : SemanticAtom :=
  { element := ⟨6, by decide, by decide⟩ }

/-- A real two-atom source hypergraph whose only interaction is a covalent double bond between the
two atom labels. -/
def twoAtomSourceGraph : FiniteAtomInteractionHypergraph (Fin 2) where
  atomData := fun _ => carbonAtom
  interactions := [([(0 : Fin 2), (1 : Fin 2)], SemanticInteractionKind.covalent 2)]
  arity_ge_two := by
    intro edge member
    simp only [List.mem_singleton] at member
    subst edge
    decide
  participants_nodup := by
    intro edge member
    simp only [List.mem_singleton] at member
    subst edge
    decide

/-- The common enumeration of the two source labels. -/
def twoAtomEnumeration : Fin 2 ≃ Fin (Fintype.card (Fin 2)) :=
  OrganicStereoIndependentElectronicEncoding.finCastEquiv (Fintype.card_fin 2).symm

/-- Encoded first source atom. -/
def twoAtomEncodedZero :
    Fin (twoAtomSourceGraph.certifiedEncoding twoAtomEnumeration).input.molecule.atomCount :=
  encodedSourceAtomEquiv twoAtomSourceGraph twoAtomEnumeration (0 : Fin 2)

/-- Encoded second source atom. -/
def twoAtomEncodedOne :
    Fin (twoAtomSourceGraph.certifiedEncoding twoAtomEnumeration).input.molecule.atomCount :=
  encodedSourceAtomEquiv twoAtomSourceGraph twoAtomEnumeration (1 : Fin 2)

/-- A one-residue fragment resolving locants 3 and 4 to the two encoded atoms. -/
def twoAtomSphingoidFragment :
    ResidueFragment Nat
      (twoAtomSourceGraph.certifiedEncoding twoAtomEnumeration).input.molecule.atomCount :=
  twoLocantFragment twoAtomEncodedZero twoAtomEncodedOne 3 4

/-- The one-residue ledger for the concrete source. -/
def twoAtomSphingoidLedger :
    ResidueIncidenceLedger Nat
      (twoAtomSourceGraph.certifiedEncoding twoAtomEnumeration) :=
  singleResidueLedger twoAtomSphingoidFragment

/-- The concrete source-backed sphingoid double-bond evidence: actual edge index `0`, ordered
labels `0,1`, covalent order `2`, supplied locants `3,4` and a supplied `.E` annotation. -/
def sphingoidDoubleBondWitness :
    SphingoidDoubleBondSourceEvidence twoAtomSourceGraph twoAtomEnumeration
      twoAtomSphingoidLedger ⟨0, by decide⟩ where
  edgeIndex := ⟨0, by decide⟩
  first := (0 : Fin 2)
  second := (1 : Fin 2)
  order := 2
  sourceLocant := 3
  targetLocant := 4
  descriptor := .E
  edge_support := rfl
  edge_kind := rfl
  source_eq := twoLocantFragment_incidence_first
    twoAtomEncodedZero twoAtomEncodedOne 3 4
  target_eq := twoLocantFragment_incidence_second
    twoAtomEncodedZero twoAtomEncodedOne 3 4 (by decide)
  ordered := by decide
  distinct_atoms := encodedSourceAtomEquiv_ne twoAtomSourceGraph twoAtomEnumeration
    (by decide : (0 : Fin 2) ≠ 1)

/-- The constructed binding satisfies the typed chemical predicate at order two. -/
theorem sphingoidDoubleBond_typedChemical_two :
    sphingoidDoubleBondWitness.binding.TypedChemical 2 :=
  sphingoidDoubleBondWitness.order_two_of_order_eq rfl

/-- The actual semantic interaction carried by the constructed sphingoid binding is a covalent
order-2 occurrence of its two resolved source atoms. -/
theorem sphingoidDoubleBond_order_two_witness :
    ((twoAtomSourceGraph.certifiedEncoding twoAtomEnumeration).input.molecule.interactions.get
        sphingoidDoubleBondWitness.binding.interaction).kind =
      SemanticInteractionKind.covalent 2 :=
  sphingoidDoubleBondWitness.interaction_kind_two rfl

/-! ## Hydrogen-bond fixture: raw incidence versus typed chemistry -/

/-- A two-atom molecule whose only interaction is a hydrogen bond.  Both atoms are carbon records;
the point of the fixture is the interaction kind, not the element choice. -/
def hydrogenBondInteraction : SemanticInteraction :=
  { participants := [0, 1], kind := SemanticInteractionKind.hydrogenBond }

/-- The fixture molecule: two atoms, one hydrogen-bond interaction. -/
def hydrogenBondMolecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom]
    interactions := [hydrogenBondInteraction] }

/-- The fixture molecule is structurally well formed: the hydrogen-bond interaction has two
distinct in-range participants. -/
theorem hydrogenBondMolecule_structurallyWellFormed :
    hydrogenBondMolecule.StructurallyWellFormed := by
  unfold SemanticMolecule.StructurallyWellFormed
  decide

/-- The certified fixture input.  Structural well-formedness is the only certificate; no chemical
admissibility or configuration is claimed. -/
def hydrogenBondCertified : CertifiedAuthoritativeChemicalInput where
  input := { molecule := hydrogenBondMolecule }
  structurallyWellFormed :=
    ⟨hydrogenBondMolecule_structurallyWellFormed, trivial, trivial⟩

/-- Source atom `0` of the fixture. -/
def hydrogenBondAtomZero :
    Fin hydrogenBondCertified.input.molecule.atomCount := ⟨0, by decide⟩

/-- Source atom `1` of the fixture. -/
def hydrogenBondAtomOne :
    Fin hydrogenBondCertified.input.molecule.atomCount := ⟨1, by decide⟩

/-- A one-residue fragment resolving locants 3 and 4 to the fixture atoms. -/
def hydrogenBondFragment :
    ResidueFragment Nat hydrogenBondCertified.input.molecule.atomCount :=
  twoLocantFragment hydrogenBondAtomZero hydrogenBondAtomOne 3 4

/-- The fixture ledger. -/
def hydrogenBondLedger : ResidueIncidenceLedger Nat hydrogenBondCertified :=
  singleResidueLedger hydrogenBondFragment

/-- The existing sphingoid double-bond binding constructed on the hydrogen-bond fixture.  Every
field is satisfied: this is exactly the raw metadata content, and it is genuinely lossless for
what it records. -/
def hydrogenBondBinding :
    LipidAnnotationIngress.SphingoidDoubleBondBinding hydrogenBondCertified hydrogenBondLedger
      ⟨0, by decide⟩ where
  sourceLocant := 3
  targetLocant := 4
  descriptor := .E
  sourceAtom := hydrogenBondAtomZero
  targetAtom := hydrogenBondAtomOne
  interaction := ⟨0, by decide⟩
  source_eq := twoLocantFragment_incidence_first
    hydrogenBondAtomZero hydrogenBondAtomOne 3 4
  target_eq := twoLocantFragment_incidence_second
    hydrogenBondAtomZero hydrogenBondAtomOne 3 4 (by decide)
  source_participant := by
    change hydrogenBondAtomZero.val ∈ hydrogenBondInteraction.participants
    decide
  target_participant := by
    change hydrogenBondAtomOne.val ∈ hydrogenBondInteraction.participants
    decide
  ordered := by decide
  distinct_atoms := by decide

/-- The fixture binding's interaction is the hydrogen-bond interaction. -/
theorem hydrogenBondBinding_interaction_get :
    hydrogenBondCertified.input.molecule.interactions.get hydrogenBondBinding.interaction =
      hydrogenBondInteraction := rfl

/-- The fixture binding's actual interaction kind is `hydrogenBond`. -/
theorem hydrogenBondBinding_kind :
    (hydrogenBondCertified.input.molecule.interactions.get
        hydrogenBondBinding.interaction).kind =
      SemanticInteractionKind.hydrogenBond := rfl

/-- **Raw incidence admits the hydrogen-bond fixture.**  The existing binding's participant
membership content holds for the hydrogen-bond interaction. -/
theorem hydrogenBondFixture_rawEndpointIncidence :
    SemanticInteraction.RawEndpointIncidence
      (hydrogenBondCertified.input.molecule.interactions.get hydrogenBondBinding.interaction)
      hydrogenBondBinding.sourceAtom.val hydrogenBondBinding.targetAtom.val :=
  hydrogenBondBinding.rawEndpointIncidence

/-- **The typed chemical predicate rejects the hydrogen-bond fixture at every bond order.**  Raw
endpoint incidence therefore does not imply typed chemical occurrence. -/
theorem hydrogenBondFixture_not_typedChemical_anyOrder (order : Nat) :
    ¬ hydrogenBondBinding.TypedChemical order := by
  intro typed
  unfold LipidAnnotationIngress.SphingoidDoubleBondBinding.TypedChemical at typed
  have kindEq : SemanticInteractionKind.hydrogenBond =
      SemanticInteractionKind.covalent order := by
    rw [← hydrogenBondBinding_kind]
    exact typed.covalent_exact
  cases kindEq

/-- The typed predicate rejects the hydrogen-bond fixture in particular at order two. -/
theorem hydrogenBondFixture_not_typedChemical :
    ¬ hydrogenBondBinding.TypedChemical 2 :=
  hydrogenBondFixture_not_typedChemical_anyOrder 2

/-- The shared typed predicate also rejects the fixture interaction directly. -/
theorem hydrogenBondInteraction_not_typedChemical_anyOrder (order : Nat) :
    ¬ hydrogenBondInteraction.TypedChemicalOccurrence 0 1 order := by
  intro typed
  have kindEq : SemanticInteractionKind.hydrogenBond =
      SemanticInteractionKind.covalent order := typed.covalent_exact
  cases kindEq

/-- Raw endpoint incidence holds for the fixture interaction directly. -/
theorem hydrogenBondInteraction_rawEndpointIncidence :
    hydrogenBondInteraction.RawEndpointIncidence 0 1 := by
  unfold SemanticInteraction.RawEndpointIncidence hydrogenBondInteraction
  exact ⟨by simp, by simp⟩

/-- The separation in one statement: raw incidence holds and the typed order-2 predicate fails. -/
theorem hydrogenBondFixture_raw_but_not_typed :
    hydrogenBondInteraction.RawEndpointIncidence 0 1 ∧
      ¬ hydrogenBondInteraction.TypedChemicalOccurrence 0 1 2 :=
  ⟨hydrogenBondInteraction_rawEndpointIncidence,
    hydrogenBondInteraction_not_typedChemical_anyOrder 2⟩

/-! ## Genuine follow-up bridge for E/Z and anomeric labels -/

/-- The actual source configuration channels a genuine E/Z or anomeric bridge must consume.
This record is lossless and deliberately not a certificate: it names the spatial and diagram
channels that a geometric/priority analysis has to interpret.  Bond order alone cannot supply
them. -/
structure SourceConfigurationChannels (input : CertifiedAuthoritativeChemicalInput) where
  /-- The supplied exact-coordinate channel, if any. -/
  spatial? : Option SpatialConfiguration
  /-- The channel is exactly the input's channel. -/
  spatial_exact : spatial? = input.input.spatial?
  /-- The supplied diagram channel, if any. -/
  diagram? : Option DiagramConfiguration
  /-- The channel is exactly the input's channel. -/
  diagram_exact : diagram? = input.input.diagram?

/-- The configuration channels of any certified input, recovered without loss. -/
def sourceConfigurationChannels (input : CertifiedAuthoritativeChemicalInput) :
    SourceConfigurationChannels input :=
  ⟨input.input.spatial?, rfl, input.input.diagram?, rfl⟩

end OrganicStereoChemicalOccurrenceFidelity

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive results -/

assert_kernel_only
  TetraStereo.OneCenter.SemanticInteraction.TypedChemicalOccurrence.rawEndpointIncidence
assert_kernel_only
  TetraStereo.OneCenter.FiniteAtomInteractionHypergraph.encodeInteraction_typedChemicalOccurrence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.SphingoidDoubleBondSourceEvidence.binding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.SphingoidDoubleBondSourceEvidence.typedChemical
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.SphingoidDoubleBondSourceEvidence.interaction_kind_two
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.sphingoidDoubleBond_typedChemical_two
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.sphingoidDoubleBond_order_two_witness
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.hydrogenBondFixture_rawEndpointIncidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.hydrogenBondFixture_not_typedChemical
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.hydrogenBondFixture_raw_but_not_typed
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SphingoidDoubleBondBinding.typedChemical_does_not_determine_EZ
assert_kernel_only
  TetraStereo.OneCenter.GlycolipidCitationAdapter.Binding.typedChemical_does_not_determine_anomer
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoChemicalOccurrenceFidelity.sourceConfigurationChannels
