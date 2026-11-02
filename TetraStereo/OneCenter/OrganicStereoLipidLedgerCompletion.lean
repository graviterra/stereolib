import TetraStereo.OneCenter.OrganicStereoLipidAnnotationIngress
import TetraStereo.OneCenter.OrganicStereoResidueLinkAnnotations

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Completed lipid source-data support and one-residue glycerol ingress

This module closes two concrete gaps in `OrganicStereoLipidAnnotationIngress`.

## 1. Support from the actual ledger incidence

The earlier `sourceData_supported` lemmas asked the caller for atom-membership premises.  Here the
same support conclusions are derived from the real `ResidueIncidenceLedger`:

* each glycerol `sn` atom comes from its recorded `incidence` equation and
  `ResidueFragment.incidence_mem_support`;
* C-2, C-3, the optional C-4 and both endpoints of every ordered sphingoid double bond come from
  the same incidence equations.

The support is stated both as the transported actual residue support
`(ledger.residue r).support.map e.symm.toEmbedding` and as the support of the already existing
`encodeFragment` constructor, using **the same** atom enumeration `e : V ≃ SourceAtom input`.  These
are exactly the premises consumed by the shared `encodeWithSourceData` constructor.

## 2. A glycerol ingress living at one actual residue

The raw `GlycerolIngress` is deliberately left unconstrained: it is a raw codec and may contain
Fischer/CIP bindings whose recorded residues differ.  The new `GlycerolIngressAt` is a coherent
aggregate **indexed by one actual residue**.  Coherence is a structural field in the source
premise, never an assumption hidden in an output statement:

* `glycerol : SnGlycerolBinding` is tied to the index by `glycerol_residue`;
* the scope-level `KnowledgeState` therefore belongs to `glycerol.residue`;
* `fischer?` keeps absence (`none`) and order, and any present binding is tied to the index by
  `fischer_residue`;
* every ordered CIP reading keeps its own recorded `residue` field and is tied to the index by
  `cip_residue`.

`ofRaw` is the only bridge from the raw ingress and takes those coherence proofs explicitly;
`toRaw` forgets the coherence proofs and preserves every arbitrary source binding.

## Constructed channel and readback

`encodeIngress` and `encodeSphingoidBinding` call the existing repository
`encodeWithSourceData`: the fragment supports, locant bindings, links and hierarchy are exactly the
shared encodings, and the ordered source data are appended by the existing
`FragmentAnnotation.withSourceData`.  Readback results use only the constructed annotation's
`sourceData` list on the left-hand side.  When appending to an existing annotation with prior
source data, the suffix/offset readback selects only the newly emitted data; the prior prefix is
preserved and is not re-read as a new payload.

## Boundary on double bonds

`SphingoidDoubleBondBinding` certifies actual source-interaction incidence only: its `Fin` index
selects a real `SemanticInteraction`, and both resolved atoms occur as participants of it.  It says
nothing about interaction kind (in particular not `covalent 2`), bond order or arity.  This module
does not narrow raw annotation input and does not claim a covalent double bond.
-/

namespace TetraStereo.OneCenter

namespace LipidLedgerCompletion

open LipidAnnotationIngress

/-! ## Transported actual residue support -/

/-- Transport one atom of the actual ledger residue support through the caller's atom
enumeration.  This is the elementary bridge from incidence to the support consumer. -/
theorem mem_support_map_symm {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Locant input}
    (e : V ≃ SourceAtom input) (residue : Fin ledger.residueCount)
    (atom : SourceAtom input) (member : atom ∈ (ledger.residue residue).support) :
    e.symm atom ∈ (ledger.residue residue).support.map e.symm.toEmbedding :=
  Finset.mem_map.mpr ⟨atom, member, rfl⟩

/-! ## Glycerol: incidence-derived support -/

theorem snGlycerol_atOne_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SnGlycerolBinding input ledger) :
    binding.atOne ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support 1 binding.atOne binding.atOne_eq

theorem snGlycerol_atTwo_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SnGlycerolBinding input ledger) :
    binding.atTwo ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support 2 binding.atTwo binding.atTwo_eq

theorem snGlycerol_atThree_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SnGlycerolBinding input ledger) :
    binding.atThree ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support 3 binding.atThree binding.atThree_eq

/-- The emitted glycerol datum is supported by the actual residue support transported through
`e`, with **no** caller-supplied membership premise. -/
theorem snGlycerol_sourceData_supported_of_ledger {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SnGlycerolBinding input ledger)
    {V : Type*} (e : V ≃ SourceAtom input) :
    SourceDataSupported ((ledger.residue binding.residue).support.map e.symm.toEmbedding)
      (binding.sourceData e) := by
  apply SourceDataSupported.singleton
  intro atom atomMem
  simp only [FragmentSourceDatum.atomReferences_lipidGlycerol, List.mem_cons,
    List.not_mem_nil, or_false] at atomMem
  rcases atomMem with rfl | rfl | rfl
  · exact mem_support_map_symm e binding.residue binding.atOne
      (snGlycerol_atOne_mem_support binding)
  · exact mem_support_map_symm e binding.residue binding.atTwo
      (snGlycerol_atTwo_mem_support binding)
  · exact mem_support_map_symm e binding.residue binding.atThree
      (snGlycerol_atThree_mem_support binding)

/-- The same support conclusion stated against the actual `encodeFragment` image of the residue,
using the same enumeration `e`. -/
theorem snGlycerol_sourceData_supported_encodeFragment
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SnGlycerolBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : List Nat) :
    SourceDataSupported
      (encodeFragment codec e (ledger.residue binding.residue) cover).support
      (binding.sourceData e) := by
  simpa only [encodeFragment_support] using
    snGlycerol_sourceData_supported_of_ledger (ledger := ledger) binding e

/-! ## Sphingoid: incidence-derived support for every configured centre and bond -/

/-- C-2 resolves through the actual residue incidence. -/
theorem sphingoid_c2_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger) :
    binding.c2Atom ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support 2 binding.c2Atom binding.c2_eq

/-- C-3 resolves through the actual residue incidence. -/
theorem sphingoid_c3_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger) :
    binding.c3Atom ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support 3 binding.c3Atom binding.c3_eq

/-- A claimed C-4 centre resolves through the actual residue incidence.  When C-4 is absent no
atom is asserted. -/
theorem sphingoid_c4_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    (atom : SourceAtom input) (descriptor : Glycolipid1997.RS)
    (present : binding.c4? = some (atom, descriptor)) :
    atom ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support 4 atom
    (binding.c4_eq atom descriptor present)

/-- The source endpoint of a bound double bond resolves through the actual residue incidence. -/
theorem sphingoid_bondSource_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    (bond : SphingoidDoubleBondBinding input ledger binding.residue)
    (_member : bond ∈ binding.doubleBonds) :
    bond.sourceAtom ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support bond.sourceLocant bond.sourceAtom
    bond.source_eq

/-- The target endpoint of a bound double bond resolves through the actual residue incidence. -/
theorem sphingoid_bondTarget_mem_support {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    (bond : SphingoidDoubleBondBinding input ledger binding.residue)
    (_member : bond ∈ binding.doubleBonds) :
    bond.targetAtom ∈ (ledger.residue binding.residue).support :=
  (ledger.residue binding.residue).incidence_mem_support bond.targetLocant bond.targetAtom
    bond.target_eq

/-- Emitted sphingoid data is supported by the actual residue support transported through `e`.
All four membership obligations (C-2, C-3, optional C-4, every double-bond endpoint) are derived
from ledger incidence. -/
theorem sphingoid_sourceData_supported_of_ledger
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (e : V ≃ SourceAtom input) :
    SourceDataSupported ((ledger.residue binding.residue).support.map e.symm.toEmbedding)
      (binding.sourceData e) := by
  apply SphingoidBinding.sourceData_supported (binding := binding) (e := e)
  · exact mem_support_map_symm e binding.residue binding.c2Atom
      (sphingoid_c2_mem_support binding)
  · exact mem_support_map_symm e binding.residue binding.c3Atom
      (sphingoid_c3_mem_support binding)
  · intro atom descriptor present
    exact mem_support_map_symm e binding.residue atom
      (sphingoid_c4_mem_support binding atom descriptor present)
  · intro bond member
    exact ⟨mem_support_map_symm e binding.residue bond.sourceAtom
        (sphingoid_bondSource_mem_support binding bond member),
      mem_support_map_symm e binding.residue bond.targetAtom
        (sphingoid_bondTarget_mem_support binding bond member)⟩

/-- The same sphingoid support conclusion stated against the actual `encodeFragment` image of the
residue, using the same enumeration `e`. -/
theorem sphingoid_sourceData_supported_encodeFragment
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : List Nat) :
    SourceDataSupported
      (encodeFragment codec e (ledger.residue binding.residue) cover).support
      (binding.sourceData e) := by
  simpa only [encodeFragment_support] using
    sphingoid_sourceData_supported_of_ledger (ledger := ledger) binding e

/-- Boundary statement: a double-bond binding certifies actual interaction incidence only.  It
does not constrain the source interaction kind, bond order or arity. -/
theorem sphingoidDoubleBond_actual_interaction_incidence
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    {residue : Fin ledger.residueCount}
    (binding : SphingoidDoubleBondBinding input ledger residue) :
    listGet? input.input.molecule.interactions binding.interaction.val =
        some (input.input.molecule.interactions.get binding.interaction) ∧
      binding.sourceAtom.val ∈
        (input.input.molecule.interactions.get binding.interaction).participants ∧
      binding.targetAtom.val ∈
        (input.input.molecule.interactions.get binding.interaction).participants :=
  ⟨listGet?_eq_some_get input.input.molecule.interactions binding.interaction,
    binding.source_participant, binding.target_participant⟩

/-! ## Coherent one-residue glycerol ingress -/

/-- A glycerol source record whose substitution, scope-level knowledge, optional Fischer
projection and ordered CIP readings all belong to **one** actual ledger residue.

The residue tie is a structural field of the source premise for every component; it is not an
assumption made in any output statement.  `fischer? = none` is preserved as absence.  CIP readings
are kept in order, with multiplicity, and each reading keeps its own recorded `residue`. -/
structure GlycerolIngressAt (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) (residue : Fin ledger.residueCount) where
  /-- The `sn` substitution with its three actual anchors. -/
  glycerol : SnGlycerolBinding input ledger
  /-- The substitution lives at the aggregate residue. -/
  glycerol_residue : glycerol.residue = residue
  /-- Scope-level partial-knowledge claim; its scope is `glycerol.residue`, i.e. `residue`. -/
  knowledge : Lipid1976.KnowledgeState
  /-- Optional reference Fischer projection; `none` records absence. -/
  fischer? : Option (FischerBinding input ledger)
  /-- Any present Fischer projection lives at the aggregate residue. -/
  fischer_residue : ∀ (fischer : FischerBinding input ledger),
    fischer? = some fischer → fischer.residue = residue
  /-- Ordered CIP readings, duplicates and order retained. -/
  cipReadings : List (GlycerolCIPBinding input ledger)
  /-- Every ordered CIP reading keeps its own recorded residue, tied to the aggregate residue. -/
  cip_residue : ∀ (reading : GlycerolCIPBinding input ledger),
    reading ∈ cipReadings → reading.residue = residue

namespace GlycerolIngressAt

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}
variable {residue : Fin ledger.residueCount}

/-- Forget the coherence proofs: the underlying raw `GlycerolIngress`, with every arbitrary source
binding preserved verbatim. -/
def toRaw (ingress : GlycerolIngressAt input ledger residue) : GlycerolIngress input ledger where
  glycerol := ingress.glycerol
  knowledge := ingress.knowledge
  fischer? := ingress.fischer?
  cipReadings := ingress.cipReadings

/-- Build the coherent aggregate from a raw ingress.  The three residue equalities are explicit
coherence premises supplied by the caller from the actual bindings. -/
def ofRaw (ingress : GlycerolIngress input ledger) (residue : Fin ledger.residueCount)
    (glycerol_residue : ingress.glycerol.residue = residue)
    (fischer_residue : ∀ (fischer : FischerBinding input ledger),
      ingress.fischer? = some fischer → fischer.residue = residue)
    (cip_residue : ∀ (reading : GlycerolCIPBinding input ledger),
      reading ∈ ingress.cipReadings → reading.residue = residue) :
    GlycerolIngressAt input ledger residue where
  glycerol := ingress.glycerol
  glycerol_residue := glycerol_residue
  knowledge := ingress.knowledge
  fischer? := ingress.fischer?
  fischer_residue := fischer_residue
  cipReadings := ingress.cipReadings
  cip_residue := cip_residue

@[simp] theorem toRaw_ofRaw (ingress : GlycerolIngress input ledger)
    (residue : Fin ledger.residueCount)
    (glycerol_residue : ingress.glycerol.residue = residue)
    (fischer_residue : ∀ (fischer : FischerBinding input ledger),
      ingress.fischer? = some fischer → fischer.residue = residue)
    (cip_residue : ∀ (reading : GlycerolCIPBinding input ledger),
      reading ∈ ingress.cipReadings → reading.residue = residue) :
    (ofRaw ingress residue glycerol_residue fischer_residue cip_residue).toRaw = ingress := rfl

/-- Coherence is retained as an explicit source fact: the substitution's actual residue is the
aggregate index. -/
theorem glycerol_scope (ingress : GlycerolIngressAt input ledger residue) :
    ingress.glycerol.residue = residue :=
  ingress.glycerol_residue

/-- Scope-level knowledge belongs to `glycerol.residue`, hence to the aggregate index. -/
theorem knowledge_scope (ingress : GlycerolIngressAt input ledger residue) :
    residue = ingress.glycerol.residue :=
  ingress.glycerol_residue.symm

/-- A present Fischer projection is tied to the aggregate actual residue. -/
theorem fischer_scope (ingress : GlycerolIngressAt input ledger residue)
    (fischer : FischerBinding input ledger)
    (present : ingress.fischer? = some fischer) :
    fischer.residue = residue :=
  ingress.fischer_residue fischer present

/-- An ordered CIP reading retains its own actual residue, tied to the aggregate index. -/
theorem cipReading_scope (ingress : GlycerolIngressAt input ledger residue)
    (reading : GlycerolCIPBinding input ledger)
    (member : reading ∈ ingress.cipReadings) :
    reading.residue = residue :=
  ingress.cip_residue reading member

/-- The complete list of CIP residues is the constant list of the aggregate residue, so order and
multiplicity are retained without collapsing any reading's own residue field. -/
theorem cipReadings_residue_map_aux (readings : List (GlycerolCIPBinding input ledger))
    (at_residue : ∀ (reading : GlycerolCIPBinding input ledger),
      reading ∈ readings → reading.residue = residue) :
    readings.map (fun reading => reading.residue) =
      List.replicate readings.length residue := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, List.length_cons,
        show head.residue = residue from
          at_residue head (List.mem_cons_self (l := tail))]
      rw [ih (fun reading member =>
        at_residue reading (List.mem_cons_of_mem head member))]
      rfl

theorem cipReadings_residue_map (ingress : GlycerolIngressAt input ledger residue) :
    ingress.cipReadings.map (fun reading => reading.residue) =
      List.replicate ingress.cipReadings.length residue :=
  cipReadings_residue_map_aux ingress.cipReadings ingress.cip_residue

/-- Fischer source data selected by an optional binding.  Matching happens on the option alone, so
the aggregate's coherence proof cannot enter the elimination. -/
def fischerData (choice : Option (FischerBinding input ledger)) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  match choice with
  | none => []
  | some fischer => fischer.sourceData e

/-- Ordered Fischer payloads selected by an optional binding, with the same absence/order
behaviour. -/
def fischerPayloadData (choice : Option (FischerBinding input ledger)) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FischerPayload V) :=
  match choice with
  | none => []
  | some fischer => [⟨e.symm fischer.atom, fischer.projection⟩]

/-- Auxiliary source data: knowledge, the optional Fischer projection (appended only when
present, in that order) and the ordered CIP readings. -/
def auxiliaryData (ingress : GlycerolIngressAt input ledger residue) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.lipidKnowledge ingress.knowledge]
    ++ fischerData ingress.fischer? e
    ++ ingress.cipReadings.flatMap (fun reading => reading.sourceData e)

/-- Full emitted source data: substitution first, then the auxiliary data. -/
def sourceData (ingress : GlycerolIngressAt input ledger residue) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  ingress.glycerol.sourceData e ++ ingress.auxiliaryData e

/-- The coherent aggregate emits exactly the raw ingress's data; coherence adds no output field
and removes nothing. -/
@[simp] theorem sourceData_eq_raw (ingress : GlycerolIngressAt input ledger residue) {V : Type*}
    (e : V ≃ SourceAtom input) :
    ingress.sourceData e = ingress.toRaw.sourceData e := rfl

/-- Exact output-only recovery of the supplied substitution. -/
theorem recoveredSubstitution?_exact (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    (firstGlycerolPayload? (ingress.sourceData e)).map
        (fun payload => payload.substitution) =
      some ingress.glycerol.substitution := by
  rw [GlycerolIngressAt.sourceData_eq_raw]
  exact GlycerolIngress.recoveredSubstitution?_exact ingress.toRaw e

/-- Exact output-only recovery of the scope-level knowledge claim. -/
theorem recoveredKnowledge?_exact (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    (knowledgePayloads (ingress.auxiliaryData e)).head? = some ingress.knowledge := by
  rw [show ingress.auxiliaryData e = ingress.toRaw.auxiliaryData e from rfl]
  exact GlycerolIngress.recoveredKnowledge?_exact ingress.toRaw e

/-- Exact output-only recovery of the optional Fischer projection.  When the source has no
projection the recovered list is empty; when it has one, exactly that ordered singleton is
recovered. -/
theorem recoveredFischer?_exact (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    fischerPayloads (ingress.auxiliaryData e) =
      fischerPayloadData ingress.fischer? e := by
  rw [show ingress.auxiliaryData e = ingress.toRaw.auxiliaryData e from rfl]
  exact GlycerolIngress.recoveredFischer?_exact ingress.toRaw e

/-- Absence is preserved: an absent optional projection contributes no datum. -/
theorem recoveredFischer?_none (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) (absent : ingress.fischer? = none) :
    fischerPayloads (ingress.auxiliaryData e) = [] := by
  rw [ingress.recoveredFischer?_exact e, absent]
  rfl

/-- Presence and order are preserved: a present optional projection contributes exactly its
ordered singleton. -/
theorem recoveredFischer?_some (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) (fischer : FischerBinding input ledger)
    (present : ingress.fischer? = some fischer) :
    fischerPayloads (ingress.auxiliaryData e) =
      [⟨e.symm fischer.atom, fischer.projection⟩] := by
  rw [ingress.recoveredFischer?_exact e, present]
  rfl

/-- Exact output-only recovery of the ordered CIP readings, including duplicates and order. -/
theorem recoveredCIPReadings_exact (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    cipPayloads (ingress.auxiliaryData e) =
      ingress.cipReadings.map (fun reading => ⟨e.symm reading.atom, reading.reading⟩) := by
  rw [show ingress.auxiliaryData e = ingress.toRaw.auxiliaryData e from rfl]
  exact GlycerolIngress.recoveredCIPReadings_exact ingress.toRaw e

/-- The number of recovered CIP readings is exactly the supplied number. -/
theorem recoveredCIPReadings_length (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    (cipPayloads (ingress.auxiliaryData e)).length = ingress.cipReadings.length := by
  rw [ingress.recoveredCIPReadings_exact e]
  simp

/-- Knowledge recovery from the full emitted list (the substitution datum contributes no
knowledge payload). -/
theorem sourceData_recoveredKnowledge? (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    (knowledgePayloads (ingress.sourceData e)).head? = some ingress.knowledge := by
  unfold GlycerolIngressAt.sourceData
  rw [knowledgePayloads_append]
  rw [show knowledgePayloads (ingress.glycerol.sourceData e) = [] from rfl]
  rw [List.nil_append]
  exact ingress.recoveredKnowledge?_exact e

/-- Fischer recovery from the full emitted list. -/
theorem sourceData_recoveredFischer (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    fischerPayloads (ingress.sourceData e) =
      fischerPayloadData ingress.fischer? e := by
  unfold GlycerolIngressAt.sourceData
  rw [fischerPayloads_append]
  rw [show fischerPayloads (ingress.glycerol.sourceData e) = [] from rfl]
  rw [List.nil_append]
  exact ingress.recoveredFischer?_exact e

/-- CIP-reading recovery from the full emitted list. -/
theorem sourceData_recoveredCIPReadings (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    cipPayloads (ingress.sourceData e) =
      ingress.cipReadings.map (fun reading => ⟨e.symm reading.atom, reading.reading⟩) := by
  unfold GlycerolIngressAt.sourceData
  rw [cipPayloads_append]
  rw [show cipPayloads (ingress.glycerol.sourceData e) = [] from rfl]
  rw [List.nil_append]
  exact ingress.recoveredCIPReadings_exact e

/-! ### Support of the full coherent ingress -/

theorem knowledgeData_supported (state : Lipid1976.KnowledgeState) {V : Type*}
    (e : V ≃ SourceAtom input) :
    SourceDataSupported ((ledger.residue residue).support.map e.symm.toEmbedding)
      [FragmentSourceDatum.lipidKnowledge state] := by
  apply SourceDataSupported.singleton
  intro atom atomMem
  simp only [FragmentSourceDatum.atomReferences_lipidKnowledge] at atomMem
  exact absurd atomMem List.not_mem_nil

theorem fischerOption_supported
    (fischer? : Option (FischerBinding input ledger))
    (at_residue : ∀ (fischer : FischerBinding input ledger),
      fischer? = some fischer → fischer.residue = residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    SourceDataSupported ((ledger.residue residue).support.map e.symm.toEmbedding)
      (fischerData fischer? e) := by
  cases fischer? with
  | none =>
      exact SourceDataSupported.nil
  | some fischer =>
      apply SourceDataSupported.singleton
      intro atom atomMem
      simp only [FragmentSourceDatum.atomReferences_lipidFischer, List.mem_singleton] at atomMem
      subst atom
      have resolve : (ledger.residue residue).incidence fischer.sourceLocant =
          some fischer.atom := by
        have original := fischer.atom_eq
        rw [at_residue fischer rfl] at original
        exact original
      exact mem_support_map_symm e residue fischer.atom
        ((ledger.residue residue).incidence_mem_support fischer.sourceLocant fischer.atom
          resolve)

theorem cipReadings_supported
    (readings : List (GlycerolCIPBinding input ledger))
    (at_residue : ∀ (reading : GlycerolCIPBinding input ledger),
      reading ∈ readings → reading.residue = residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    SourceDataSupported ((ledger.residue residue).support.map e.symm.toEmbedding)
      (readings.flatMap fun reading => reading.sourceData e) := by
  induction readings with
  | nil => exact SourceDataSupported.nil
  | cons head tail ih =>
      rw [List.flatMap_cons]
      apply SourceDataSupported.append
      · rw [show head.sourceData e =
            [FragmentSourceDatum.lipidCIP (e.symm head.atom) head.reading] from rfl]
        apply SourceDataSupported.singleton
        intro atom atomMem
        simp only [FragmentSourceDatum.atomReferences_lipidCIP, List.mem_singleton] at atomMem
        subst atom
        have resolve : (ledger.residue residue).incidence head.reading.fixedSnLocant =
            some head.atom := by
          have original := head.atom_eq
          rw [at_residue head (by simp)] at original
          exact original
        exact mem_support_map_symm e residue head.atom
          ((ledger.residue residue).incidence_mem_support head.reading.fixedSnLocant head.atom
            resolve)
      · exact ih (fun reading member => at_residue reading (by simp [member]))

theorem auxiliaryData_supported (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    SourceDataSupported ((ledger.residue residue).support.map e.symm.toEmbedding)
      (ingress.auxiliaryData e) := by
  unfold GlycerolIngressAt.auxiliaryData
  apply SourceDataSupported.append
  · apply SourceDataSupported.append
    · exact knowledgeData_supported ingress.knowledge e
    · exact fischerOption_supported ingress.fischer? ingress.fischer_residue e
  · exact cipReadings_supported ingress.cipReadings ingress.cip_residue e

/-- The full coherent ingress is supported by the actual aggregate residue support.  The
substitution support is derived from its own ledger residue, which is the aggregate index by
`glycerol_residue`. -/
theorem sourceData_supported_of_ledger (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    SourceDataSupported ((ledger.residue residue).support.map e.symm.toEmbedding)
      (ingress.sourceData e) := by
  unfold GlycerolIngressAt.sourceData
  apply SourceDataSupported.append
  · simpa only [ingress.glycerol_residue] using
      snGlycerol_sourceData_supported_of_ledger (ledger := ledger) ingress.glycerol e
  · exact ingress.auxiliaryData_supported e

/-! ### Per-residue routing and the constructed annotated-ledger channel -/

/-- Route the coherent ingress's ordered source data to the residue index.  Data appear at the
aggregate residue only; every other residue gets the empty list. -/
def ledgerSourceData (ingress : GlycerolIngressAt input ledger residue) {V : Type*}
    (e : V ≃ SourceAtom input) : Fin ledger.residueCount → List (FragmentSourceDatum V) :=
  fun index => if index = residue then ingress.sourceData e else []

/-- The routing function satisfies exactly the actual encoded-support invariant consumed by
`encodeWithSourceData`; every index is discharged from ledger incidence. -/
theorem ledgerSourceData_supported (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (e : V ≃ SourceAtom input) :
    ∀ index, ∀ datum ∈ ingress.ledgerSourceData e index,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue index).support.map e.symm.toEmbedding := by
  intro index datum member atom atomMem
  by_cases equal : index = residue
  · rw [equal] at member ⊢
    simp only [GlycerolIngressAt.ledgerSourceData, if_pos rfl] at member ⊢
    exact ingress.sourceData_supported_of_ledger e datum member atom atomMem
  · simp only [GlycerolIngressAt.ledgerSourceData, if_neg equal] at member
    exact absurd member (by simp)

/-- Construct the full annotated-ledger channel.  This is the shared `encodeWithSourceData`
constructor: supports, bindings, links and hierarchy are the existing encoded ledger, and the
ingress data are appended alongside the aggregate residue. -/
def encodeIngress (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    ResidueLedgerAnnotation V ledger.residueCount
      input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover (ingress.ledgerSourceData e)
    (ingress.ledgerSourceData_supported e)

/-- Exact per-index readback of the attached source data. -/
@[simp] theorem encodeIngress_residue_sourceData (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) (index : Fin ledger.residueCount) :
    ((ingress.encodeIngress codec e cover).residue index).sourceData =
      ingress.ledgerSourceData e index :=
  encodeWithSourceData_residue_sourceData codec e ledger cover
    (ingress.ledgerSourceData e) (ingress.ledgerSourceData_supported e) index

/-- At the aggregate residue, the constructed annotation carries exactly the emitted ingress
data.  The left-hand side reads only the constructed channel. -/
@[simp] theorem encodeIngress_sourceData_self (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    ((ingress.encodeIngress codec e cover).residue residue).sourceData =
      ingress.sourceData e := by
  rw [GlycerolIngressAt.encodeIngress_residue_sourceData]
  unfold GlycerolIngressAt.ledgerSourceData
  simp

/-- No ingress datum is routed to a different residue. -/
theorem encodeIngress_sourceData_of_ne (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) (index : Fin ledger.residueCount)
    (different : index ≠ residue) :
    ((ingress.encodeIngress codec e cover).residue index).sourceData = [] := by
  rw [GlycerolIngressAt.encodeIngress_residue_sourceData]
  unfold GlycerolIngressAt.ledgerSourceData
  simp only [if_neg different]

/-- Output-only recovery of the substitution from the constructed full channel. -/
theorem encodeIngress_recoveredSubstitution (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    (firstGlycerolPayload?
        (((ingress.encodeIngress codec e cover).residue residue).sourceData)).map
          (fun payload => payload.substitution) =
      some ingress.glycerol.substitution := by
  rw [GlycerolIngressAt.encodeIngress_sourceData_self]
  exact ingress.recoveredSubstitution?_exact e

/-- Output-only recovery of the scope-level knowledge claim from the constructed full channel. -/
theorem encodeIngress_recoveredKnowledge (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    (knowledgePayloads
        (((ingress.encodeIngress codec e cover).residue residue).sourceData)).head? =
      some ingress.knowledge := by
  rw [GlycerolIngressAt.encodeIngress_sourceData_self]
  exact ingress.recoveredKnowledge?_exact e

/-- Output-only recovery of the optional Fischer projection, absence included, from the
constructed full channel. -/
theorem encodeIngress_recoveredFischer (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    fischerPayloads
        (((ingress.encodeIngress codec e cover).residue residue).sourceData) =
      fischerPayloadData ingress.fischer? e := by
  rw [GlycerolIngressAt.encodeIngress_sourceData_self]
  exact ingress.recoveredFischer?_exact e

/-- Output-only recovery of the ordered CIP readings, order and multiplicity included, from the
constructed full channel. -/
theorem encodeIngress_recoveredCIPReadings (ingress : GlycerolIngressAt input ledger residue)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    cipPayloads
        (((ingress.encodeIngress codec e cover).residue residue).sourceData) =
      ingress.cipReadings.map (fun reading => ⟨e.symm reading.atom, reading.reading⟩) := by
  rw [GlycerolIngressAt.encodeIngress_sourceData_self]
  exact ingress.recoveredCIPReadings_exact e

/-! ### Appending to an existing fragment annotation -/

/-- Append the ingress source data to an existing annotation.  The existing support, bindings and
prior source data are untouched; the ingress data follow them. -/
def attachIngressSourceData {V : Type*} (annotation : FragmentAnnotation V)
    (ingress : GlycerolIngressAt input ledger residue) (e : V ≃ SourceAtom input)
    (supported : SourceDataSupported annotation.support (ingress.sourceData e)) :
    FragmentAnnotation V :=
  annotation.withSourceData (ingress.sourceData e) supported

/-- Old source data are retained as the exact prefix. -/
theorem attachIngressSourceData_old_prefix {V : Type*} (annotation : FragmentAnnotation V)
    (ingress : GlycerolIngressAt input ledger residue) (e : V ≃ SourceAtom input)
    (supported : SourceDataSupported annotation.support (ingress.sourceData e)) :
    (attachIngressSourceData annotation ingress e supported).sourceData.take
        annotation.sourceData.length = annotation.sourceData := by
  rw [show (attachIngressSourceData annotation ingress e supported).sourceData =
      annotation.sourceData ++ ingress.sourceData e from rfl]
  exact List.take_left

/-- The new ingress data are the exact suffix; nothing is overwritten. -/
theorem attachIngressSourceData_new_suffix {V : Type*} (annotation : FragmentAnnotation V)
    (ingress : GlycerolIngressAt input ledger residue) (e : V ≃ SourceAtom input)
    (supported : SourceDataSupported annotation.support (ingress.sourceData e)) :
    (attachIngressSourceData annotation ingress e supported).sourceData.drop
        annotation.sourceData.length = ingress.sourceData e := by
  rw [show (attachIngressSourceData annotation ingress e supported).sourceData =
      annotation.sourceData ++ ingress.sourceData e from rfl]
  exact List.drop_left

/-- Offset-selected output-only recovery of the substitution: the suffix at the old annotation's
length is inspected, not the first payload of the whole fragment. -/
theorem attachIngressSourceData_recoveredSubstitution_at_offset {V : Type*}
    (annotation : FragmentAnnotation V) (ingress : GlycerolIngressAt input ledger residue)
    (e : V ≃ SourceAtom input)
    (supported : SourceDataSupported annotation.support (ingress.sourceData e)) :
    (firstGlycerolPayload?
        ((attachIngressSourceData annotation ingress e supported).sourceData.drop
          annotation.sourceData.length)).map (fun payload => payload.substitution) =
      some ingress.glycerol.substitution := by
  rw [GlycerolIngressAt.attachIngressSourceData_new_suffix]
  exact ingress.recoveredSubstitution?_exact e

/-- Offset-selected output-only recovery of the knowledge claim. -/
theorem attachIngressSourceData_recoveredKnowledge_at_offset {V : Type*}
    (annotation : FragmentAnnotation V) (ingress : GlycerolIngressAt input ledger residue)
    (e : V ≃ SourceAtom input)
    (supported : SourceDataSupported annotation.support (ingress.sourceData e)) :
    (knowledgePayloads
        ((attachIngressSourceData annotation ingress e supported).sourceData.drop
          annotation.sourceData.length)).head? = some ingress.knowledge := by
  rw [GlycerolIngressAt.attachIngressSourceData_new_suffix]
  exact ingress.sourceData_recoveredKnowledge? e

/-- Offset-selected output-only recovery of the optional Fischer projection. -/
theorem attachIngressSourceData_recoveredFischer_at_offset {V : Type*}
    (annotation : FragmentAnnotation V) (ingress : GlycerolIngressAt input ledger residue)
    (e : V ≃ SourceAtom input)
    (supported : SourceDataSupported annotation.support (ingress.sourceData e)) :
    fischerPayloads
        ((attachIngressSourceData annotation ingress e supported).sourceData.drop
          annotation.sourceData.length) =
      fischerPayloadData ingress.fischer? e := by
  rw [GlycerolIngressAt.attachIngressSourceData_new_suffix]
  exact ingress.sourceData_recoveredFischer e

/-- Offset-selected output-only recovery of the ordered CIP readings. -/
theorem attachIngressSourceData_recoveredCIPReadings_at_offset {V : Type*}
    (annotation : FragmentAnnotation V) (ingress : GlycerolIngressAt input ledger residue)
    (e : V ≃ SourceAtom input)
    (supported : SourceDataSupported annotation.support (ingress.sourceData e)) :
    cipPayloads
        ((attachIngressSourceData annotation ingress e supported).sourceData.drop
          annotation.sourceData.length) =
      ingress.cipReadings.map (fun reading => ⟨e.symm reading.atom, reading.reading⟩) := by
  rw [GlycerolIngressAt.attachIngressSourceData_new_suffix]
  exact ingress.sourceData_recoveredCIPReadings e

end GlycerolIngressAt

/-! ## Constructed sphingoid channel -/

/-- Route a sphingoid binding's ordered source data to its actual residue. -/
def sphingoidLedgerSourceData {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (e : V ≃ SourceAtom input) :
    Fin ledger.residueCount → List (FragmentSourceDatum V) :=
  fun index => if index = binding.residue then binding.sourceData e else []

/-- The sphingoid routing satisfies the actual encoded-support invariant; all anchor memberships
are derived from ledger incidence. -/
theorem sphingoidLedgerSourceData_supported {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (e : V ≃ SourceAtom input) :
    ∀ index, ∀ datum ∈ sphingoidLedgerSourceData binding e index,
      ∀ atom ∈ datum.atomReferences,
        atom ∈ (ledger.residue index).support.map e.symm.toEmbedding := by
  intro index datum member atom atomMem
  by_cases equal : index = binding.residue
  · rw [equal] at member ⊢
    simp only [sphingoidLedgerSourceData, if_pos rfl] at member ⊢
    exact sphingoid_sourceData_supported_of_ledger binding e datum member atom atomMem
  · simp only [sphingoidLedgerSourceData, if_neg equal] at member
    exact absurd member (by simp)

/-- Construct the full annotated-ledger channel for one sphingoid binding through the shared
`encodeWithSourceData` constructor. -/
def encodeSphingoidBinding {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    ResidueLedgerAnnotation V ledger.residueCount
      input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover (sphingoidLedgerSourceData binding e)
    (sphingoidLedgerSourceData_supported binding e)

/-- Exact per-index readback of the attached sphingoid source data. -/
@[simp] theorem encodeSphingoidBinding_residue_sourceData
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) (index : Fin ledger.residueCount) :
    ((encodeSphingoidBinding binding codec e cover).residue index).sourceData =
      sphingoidLedgerSourceData binding e index :=
  encodeWithSourceData_residue_sourceData codec e ledger cover
    (sphingoidLedgerSourceData binding e) (sphingoidLedgerSourceData_supported binding e) index

/-- At the sphingoid binding's actual residue, the constructed annotation carries exactly the
emitted source data. -/
@[simp] theorem encodeSphingoidBinding_sourceData_self
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    ((encodeSphingoidBinding binding codec e cover).residue binding.residue).sourceData =
      binding.sourceData e := by
  rw [encodeSphingoidBinding_residue_sourceData]
  unfold sphingoidLedgerSourceData
  simp

/-- Output-only recovery of the whole sphingoid configuration from the constructed channel. -/
theorem encodeSphingoidBinding_recoverConfiguration
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    recoverSphingoidConfiguration?
        (((encodeSphingoidBinding binding codec e cover).residue
          binding.residue).sourceData) =
      some binding.configuration := by
  rw [encodeSphingoidBinding_sourceData_self]
  exact binding.recoverSphingoidConfiguration?_sourceData e

/-- Output-only recovery of the ordered centre annotations from the constructed channel. -/
theorem encodeSphingoidBinding_recoveredCenterAnnotations
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    recoveredCenterAnnotations
        (((encodeSphingoidBinding binding codec e cover).residue
          binding.residue).sourceData) =
      binding.centerAnnotations := by
  rw [encodeSphingoidBinding_sourceData_self]
  exact binding.recoveredCenterAnnotations_sourceData e

/-- Output-only recovery of the ordered double-bond annotations from the constructed channel. -/
theorem encodeSphingoidBinding_recoveredDoubleBondAnnotations
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V : Type*} (codec : LocantCodec Nat) (e : V ≃ SourceAtom input)
    (cover : Fin ledger.residueCount → List Nat) :
    recoveredDoubleBondAnnotations
        (((encodeSphingoidBinding binding codec e cover).residue
          binding.residue).sourceData) =
      binding.configuration.doubleBonds := by
  rw [encodeSphingoidBinding_sourceData_self]
  exact binding.recoveredDoubleBondAnnotations_sourceData e

end LipidLedgerCompletion

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive results -/

assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.snGlycerol_sourceData_supported_of_ledger
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.sphingoid_sourceData_supported_of_ledger
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.sphingoidDoubleBond_actual_interaction_incidence
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.glycerol_scope
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.fischer_scope
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.cipReading_scope
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.cipReadings_residue_map
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.recoveredSubstitution?_exact
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.recoveredFischer?_exact
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.recoveredCIPReadings_exact
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.sourceData_supported_of_ledger
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.ledgerSourceData_supported
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.encodeIngress_sourceData_self
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.encodeIngress_recoveredCIPReadings
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.attachIngressSourceData_old_prefix
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.attachIngressSourceData_new_suffix
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.GlycerolIngressAt.attachIngressSourceData_recoveredCIPReadings_at_offset
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.sphingoidLedgerSourceData_supported
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.encodeSphingoidBinding_sourceData_self
assert_kernel_only
  TetraStereo.OneCenter.LipidLedgerCompletion.encodeSphingoidBinding_recoveredDoubleBondAnnotations
