import TetraStereo.OneCenter.OrganicStereoFragmentSourceData
import TetraStereo.OneCenter.OrganicStereoSpecialistAnnotations
import TetraStereo.OneCenter.OrganicStereoResidueIncidence
import TetraStereo.OneCenter.LipidStereochemistrySemantics
import TetraStereo.OneCenter.GlycolipidStereochemistrySemantics
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Lipid / glycolipid source-record ingress into fragment source data

This module binds the actual configuration-bearing source records of *Nomenclature of Lipids
(Recommendations 1976)* and *Nomenclature of Glycolipids (Recommendations 1997)* to the shared
finite residue-incidence ledger, emits them into the shared
`TetraStereo.OneCenter.FragmentSourceDatum` channel, and proves exact recovery of the original
records from the emitted data alone.

What is preserved literally:

* the three supplied glycerol `sn` locants 1/2/3 as ledger locants, and the actual source atoms
  they resolve to, pairwise distinct;
* `Lipid1976.ReferenceFischerProjection`, `Lipid1976.KnowledgeState` (partial knowledge such as
  `unknownOrUnspecified` and `equalAntipodes`), and `Lipid1976.GlycerolCIPReading` with its
  `fixedSnLocant` numbering kept separate from its `cip` descriptor;
* the whole `Glycolipid1997.SphingoidConfiguration` (C-2, C-3, optional C-4 and every ordered
  `(locant, EZ)` double-bond annotation);
* every sphingoid centre at its supplied source locant with its `RS` descriptor, and every
  configured double bond tied to an **actual** source interaction occurrence whose two resolved
  atoms both occur as participants.

What is never done: a locant is never read as an atom id; numbering is never converted to a CIP
assignment; a double-bond locant is never treated as a bond; no name is parsed; optional absence
and repeated claims are never collapsed.

The recovery functions below take only the emitted `List (FragmentSourceDatum V)`.  They never
take the original `input`, ledger or binding again.

## Binding assumptions

1. The caller supplies the residue index and every resolution proof; nothing is guessed.
2. Pairwise distinctness of the three glycerol atoms and of the two double-bond atoms is an
   explicit caller obligation; it is not inferred from locant inequality.
3. `sourceLocant < targetLocant` is a caller obligation for each ordered double-bond annotation.
4. Participant certificates use `Fin interactions.length` interaction indices, never atom
   numbers.
5. `glycolipidSphingoid` carries no additional `V` anchor; it is scoped by the enclosing
   fragment support.
-/

namespace TetraStereo.OneCenter

namespace LipidAnnotationIngress

/-- A source atom is exactly an index into the actual source atom list. -/
abbrev SourceAtom (input : CertifiedAuthoritativeChemicalInput) : Type :=
  Fin input.input.molecule.atomCount

/-- A source interaction occurrence is exactly an index into the actual interaction list. -/
abbrev SourceInteraction (input : CertifiedAuthoritativeChemicalInput) : Type :=
  Fin input.input.molecule.interactions.length

/-! ## Glycerol source bindings -/

/-- A glycerol `sn` substitution bound to the actual source residue ledger.

The three supplied positions are the stereospecific locants `1`, `2`, `3`; each is resolved
through the residue's scoped incidence, so the binding stores the source locants and the source
atom ids separately.  Pairwise distinctness of the three resolved atoms is a caller obligation;
it is never inferred from locant inequality. -/
structure SnGlycerolBinding (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) where
  residue : Fin ledger.residueCount
  substitution : Lipid1976.SnGlycerolSubstitution
  atOne : SourceAtom input
  atTwo : SourceAtom input
  atThree : SourceAtom input
  atOne_eq : (ledger.residue residue).incidence 1 = some atOne
  atTwo_eq : (ledger.residue residue).incidence 2 = some atTwo
  atThree_eq : (ledger.residue residue).incidence 3 = some atThree
  atOne_ne_atTwo : atOne ≠ atTwo
  atOne_ne_atThree : atOne ≠ atThree
  atTwo_ne_atThree : atTwo ≠ atThree

/-- A `sn` reference Fischer projection bound to the atom at a supplied source locant. -/
structure FischerBinding (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) where
  residue : Fin ledger.residueCount
  sourceLocant : Nat
  atom : SourceAtom input
  atom_eq : (ledger.residue residue).incidence sourceLocant = some atom
  projection : Lipid1976.ReferenceFischerProjection

/-- One supplied glycerol CIP reading bound to the atom at its fixed `sn` locant.

`reading.fixedSnLocant` is source numbering; `reading.cip` is the CIP descriptor.  The two are
kept as separate fields and are never converted into one another. -/
structure GlycerolCIPBinding (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) where
  residue : Fin ledger.residueCount
  reading : Lipid1976.GlycerolCIPReading
  atom : SourceAtom input
  atom_eq : (ledger.residue residue).incidence reading.fixedSnLocant = some atom

/-- Aggregate glycerol ingress: one substitution, one partial-knowledge claim, an optional
Fischer projection (optional absence preserved) and an ordered list of CIP readings (repeated
claims and order preserved; duplicates are not removed). -/
structure GlycerolIngress (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) where
  glycerol : SnGlycerolBinding input ledger
  knowledge : Lipid1976.KnowledgeState
  fischer? : Option (FischerBinding input ledger)
  cipReadings : List (GlycerolCIPBinding input ledger)

namespace SnGlycerolBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Resolve the supplied locant `1` in the actual residue ledger. -/
theorem resolve_one (binding : SnGlycerolBinding input ledger) :
    (ledger.residue binding.residue).incidence 1 = some binding.atOne :=
  binding.atOne_eq

/-- Resolve the supplied locant `2` in the actual residue ledger. -/
theorem resolve_two (binding : SnGlycerolBinding input ledger) :
    (ledger.residue binding.residue).incidence 2 = some binding.atTwo :=
  binding.atTwo_eq

/-- Resolve the supplied locant `3` in the actual residue ledger. -/
theorem resolve_three (binding : SnGlycerolBinding input ledger) :
    (ledger.residue binding.residue).incidence 3 = some binding.atThree :=
  binding.atThree_eq

/-- Emit the substitution into the shared source-data channel.  The three anchors are the actual
source atoms, labelled by the external atom equivalence `e`; the source locants themselves remain
the ledger tokens `1`, `2`, `3`. -/
def sourceData (binding : SnGlycerolBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.lipidGlycerol (e.symm binding.atOne) (e.symm binding.atTwo)
    (e.symm binding.atThree) binding.substitution]

@[simp] theorem sourceData_eq (binding : SnGlycerolBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    binding.sourceData e =
      [FragmentSourceDatum.lipidGlycerol (e.symm binding.atOne) (e.symm binding.atTwo)
        (e.symm binding.atThree) binding.substitution] := rfl

end SnGlycerolBinding

namespace FischerBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Resolve the supplied source locant. -/
theorem resolve (binding : FischerBinding input ledger) :
    (ledger.residue binding.residue).incidence binding.sourceLocant = some binding.atom :=
  binding.atom_eq

/-- Emit the reference Fischer projection with its actual centre atom. -/
def sourceData (binding : FischerBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.lipidFischer (e.symm binding.atom) binding.projection]

end FischerBinding

namespace GlycerolCIPBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Resolve the fixed `sn` locant of the reading. -/
theorem resolve (binding : GlycerolCIPBinding input ledger) :
    (ledger.residue binding.residue).incidence binding.reading.fixedSnLocant =
      some binding.atom :=
  binding.atom_eq

/-- Emit one CIP reading with its actual centre atom. -/
def sourceData (binding : GlycerolCIPBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.lipidCIP (e.symm binding.atom) binding.reading]

end GlycerolCIPBinding

namespace GlycerolIngress

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Auxiliary source data: knowledge claim, optional Fischer projection (appended only when
present) and the ordered CIP readings. -/
def auxiliaryData (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.lipidKnowledge ingress.knowledge]
    ++ (match ingress.fischer? with
        | none => []
        | some fischer => fischer.sourceData e)
    ++ ingress.cipReadings.flatMap (fun reading => reading.sourceData e)

/-- Full emitted source data.  The substitution is emitted first; nothing about the original
binding is stored outside the shared data channel. -/
def sourceData (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  ingress.glycerol.sourceData e ++ ingress.auxiliaryData e

@[simp] theorem sourceData_eq (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    ingress.sourceData e = ingress.glycerol.sourceData e ++ ingress.auxiliaryData e := rfl

end GlycerolIngress

/-! ## Sphingoid source bindings -/

/-- One ordered sphingoid double-bond annotation tied to a real source occurrence.

`sourceLocant` and `targetLocant` are the supplied ordered source locants (`sourceLocant <
targetLocant`); `descriptor` is the supplied `EZ` geometry.  The two resolved atoms must both be
participants of the actual interaction at `interaction`, a `Fin` index into the real source
interaction list.  No atom number is read as a bond. -/
structure SphingoidDoubleBondBinding (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) (residue : Fin ledger.residueCount) where
  sourceLocant : Nat
  targetLocant : Nat
  descriptor : Glycolipid1997.EZ
  sourceAtom : SourceAtom input
  targetAtom : SourceAtom input
  interaction : SourceInteraction input
  source_eq : (ledger.residue residue).incidence sourceLocant = some sourceAtom
  target_eq : (ledger.residue residue).incidence targetLocant = some targetAtom
  source_participant :
    sourceAtom.val ∈ (input.input.molecule.interactions.get interaction).participants
  target_participant :
    targetAtom.val ∈ (input.input.molecule.interactions.get interaction).participants
  ordered : sourceLocant < targetLocant
  distinct_atoms : sourceAtom ≠ targetAtom

/-- A complete sphingoid configuration bound to the actual residue ledger.

All of `configuration` is stored literally: C-2 and C-3 descriptors, the optional C-4 descriptor,
and the ordered list of `(locant, EZ)` annotations.  C-2 and C-3 always resolve; C-4 resolves
exactly when the configuration claims one, and no C-4 atom is asserted when it is absent.  The
ordered double-bond bindings are required to carry exactly the configured annotations. -/
structure SphingoidBinding (input : CertifiedAuthoritativeChemicalInput)
    (ledger : ResidueIncidenceLedger Nat input) where
  residue : Fin ledger.residueCount
  configuration : Glycolipid1997.SphingoidConfiguration
  c2Atom : SourceAtom input
  c3Atom : SourceAtom input
  c2_eq : (ledger.residue residue).incidence 2 = some c2Atom
  c3_eq : (ledger.residue residue).incidence 3 = some c3Atom
  /-- The optional C-4 centre: its actual source atom and its `RS` descriptor.  `none` records
  absence; no atom is asserted then. -/
  c4? : Option (SourceAtom input × Glycolipid1997.RS)
  /-- C-4 is present exactly when the configuration claims a descriptor, and the descriptor is
  the configured one. -/
  c4_descriptor_exact : c4?.map Prod.snd = configuration.c4Center?
  /-- A present C-4 centre resolves at source locant `4`. -/
  c4_eq : ∀ (atom : SourceAtom input) (descriptor : Glycolipid1997.RS),
    c4? = some (atom, descriptor) →
      (ledger.residue residue).incidence 4 = some atom
  /-- Ordered double-bond occurrences, one per supplied annotation. -/
  doubleBonds : List (SphingoidDoubleBondBinding input ledger residue)
  /-- The ordered annotations of the bindings are exactly the configured annotations. -/
  doubleBondAnnotations_exact :
    doubleBonds.map (fun bond => (bond.sourceLocant, bond.descriptor)) =
      configuration.doubleBonds

namespace SphingoidDoubleBondBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}
variable {residue : Fin ledger.residueCount}

/-- Emit one double bond with both actual atom anchors, its ordered source locant and geometry. -/
def sourceData (binding : SphingoidDoubleBondBinding input ledger residue) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.glycolipidDoubleBond (e.symm binding.sourceAtom)
    (e.symm binding.targetAtom) binding.sourceLocant binding.descriptor]

/-- Every field of a double-bond binding denotes real source data: the interaction occurs at its
recorded source index, both resolved atoms are participants of it, and both locants resolve
through the actual residue ledger. -/
theorem real_occurrence (binding : SphingoidDoubleBondBinding input ledger residue) :
    listGet? input.input.molecule.interactions binding.interaction.val =
        some (input.input.molecule.interactions.get binding.interaction) ∧
      binding.sourceAtom.val ∈
        (input.input.molecule.interactions.get binding.interaction).participants ∧
      binding.targetAtom.val ∈
        (input.input.molecule.interactions.get binding.interaction).participants ∧
      (ledger.residue residue).incidence binding.sourceLocant = some binding.sourceAtom ∧
      (ledger.residue residue).incidence binding.targetLocant = some binding.targetAtom :=
  ⟨listGet?_eq_some_get input.input.molecule.interactions binding.interaction,
    binding.source_participant, binding.target_participant, binding.source_eq,
    binding.target_eq⟩

end SphingoidDoubleBondBinding

namespace SphingoidBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- The ordered centre annotations encoded by the configuration: C-2, C-3 and optional C-4. -/
def centerAnnotations (binding : SphingoidBinding input ledger) :
    List (Nat × Glycolipid1997.RS) :=
  [(2, binding.configuration.c2), (3, binding.configuration.c3)]
    ++ (match binding.configuration.c4Center? with
        | none => []
        | some descriptor => [(4, descriptor)])

/-- C-4 centre data: emitted only when the configuration claims a C-4 descriptor. -/
def c4CenterData (binding : SphingoidBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  match binding.c4? with
  | none => []
  | some (atom, descriptor) =>
      [FragmentSourceDatum.glycolipidCenter (e.symm atom) 4 descriptor]

/-- Ordered centre data: C-2, C-3 and optional C-4, at the supplied source locants. -/
def centerData (binding : SphingoidBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.glycolipidCenter (e.symm binding.c2Atom) 2 binding.configuration.c2,
    FragmentSourceDatum.glycolipidCenter (e.symm binding.c3Atom) 3 binding.configuration.c3]
    ++ binding.c4CenterData e

/-- Ordered double-bond data. -/
def doubleBondData (binding : SphingoidBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  binding.doubleBonds.flatMap (fun bond => bond.sourceData e)

/-- Full emitted source data: the whole configuration, every centre, every double bond. -/
def sourceData (binding : SphingoidBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : List (FragmentSourceDatum V) :=
  [FragmentSourceDatum.glycolipidSphingoid binding.configuration]
    ++ (binding.centerData e ++ binding.doubleBondData e)

/-- Resolve the supplied C-2 locant. -/
theorem resolve_two (binding : SphingoidBinding input ledger) :
    (ledger.residue binding.residue).incidence 2 = some binding.c2Atom :=
  binding.c2_eq

/-- Resolve the supplied C-3 locant. -/
theorem resolve_three (binding : SphingoidBinding input ledger) :
    (ledger.residue binding.residue).incidence 3 = some binding.c3Atom :=
  binding.c3_eq

/-- Resolve the claimed C-4 locant. -/
theorem resolve_four (binding : SphingoidBinding input ledger)
    (atom : SourceAtom input) (descriptor : Glycolipid1997.RS)
    (present : binding.c4? = some (atom, descriptor)) :
    (ledger.residue binding.residue).incidence 4 = some atom :=
  binding.c4_eq atom descriptor present

/-- Every configured double bond is tied to a real source occurrence.  The witness binding is
found from the ordered annotation equality, and its participants are actual source participants. -/
theorem configured_doubleBond_has_occurrence (binding : SphingoidBinding input ledger)
    (locant : Nat) (descriptor : Glycolipid1997.EZ)
    (member : (locant, descriptor) ∈ binding.configuration.doubleBonds) :
    ∃ bond ∈ binding.doubleBonds,
      bond.sourceLocant = locant ∧ bond.descriptor = descriptor ∧
        listGet? input.input.molecule.interactions bond.interaction.val =
            some (input.input.molecule.interactions.get bond.interaction) ∧
          bond.sourceAtom.val ∈
            (input.input.molecule.interactions.get bond.interaction).participants ∧
          bond.targetAtom.val ∈
            (input.input.molecule.interactions.get bond.interaction).participants ∧
          (ledger.residue binding.residue).incidence bond.sourceLocant =
            some bond.sourceAtom ∧
          (ledger.residue binding.residue).incidence bond.targetLocant =
            some bond.targetAtom := by
  have mapped : (locant, descriptor) ∈
      binding.doubleBonds.map (fun bond => (bond.sourceLocant, bond.descriptor)) := by
    rw [binding.doubleBondAnnotations_exact]
    exact member
  obtain ⟨bond, bondMember, annotationEq⟩ := List.mem_map.mp mapped
  have sourceEq : bond.sourceLocant = locant := (Prod.mk.inj annotationEq).1
  have descriptorEq : bond.descriptor = descriptor := (Prod.mk.inj annotationEq).2
  obtain ⟨occurrence, sourceParticipant, targetParticipant, sourceResolve, targetResolve⟩ :=
    bond.real_occurrence
  exact ⟨bond, bondMember, sourceEq, descriptorEq, occurrence, sourceParticipant,
    targetParticipant, sourceResolve, targetResolve⟩

end SphingoidBinding

/-! ## Payload accessors and exact recovery -/

/-- The three glycerol anchors together with the supplied substitution. -/
structure GlycerolPayload (V : Type*) where
  atOne : V
  atTwo : V
  atThree : V
  substitution : Lipid1976.SnGlycerolSubstitution

/-- One Fischer payload: the centre anchor and the projection. -/
structure FischerPayload (V : Type*) where
  center : V
  projection : Lipid1976.ReferenceFischerProjection

/-- One CIP payload: the centre anchor and the reading. -/
structure CIPPayload (V : Type*) where
  center : V
  reading : Lipid1976.GlycerolCIPReading

/-- One centre payload: the anchor, its supplied source locant and its `RS` descriptor. -/
structure SphingoidCenterPayload (V : Type*) where
  center : V
  sourceLocant : Nat
  descriptor : Glycolipid1997.RS

/-- One double-bond payload: both anchors, the ordered source locant and the `EZ` geometry. -/
structure SphingoidDoubleBondPayload (V : Type*) where
  sourceAtom : V
  targetAtom : V
  sourceLocant : Nat
  descriptor : Glycolipid1997.EZ

/-- Pattern-matching accessor for a glycerol datum. -/
def glycerolPayload? {V : Type*} : FragmentSourceDatum V → Option (GlycerolPayload V)
  | FragmentSourceDatum.lipidGlycerol first second third substitution =>
      some ⟨first, second, third, substitution⟩
  | _ => none

/-- Pattern-matching accessor for a Fischer datum. -/
def fischerPayload? {V : Type*} : FragmentSourceDatum V → Option (FischerPayload V)
  | FragmentSourceDatum.lipidFischer center projection => some ⟨center, projection⟩
  | _ => none

/-- Pattern-matching accessor for a CIP datum. -/
def cipPayload? {V : Type*} : FragmentSourceDatum V → Option (CIPPayload V)
  | FragmentSourceDatum.lipidCIP center reading => some ⟨center, reading⟩
  | _ => none

/-- Pattern-matching accessor for a knowledge datum. -/
def knowledgePayload? {V : Type*} : FragmentSourceDatum V → Option Lipid1976.KnowledgeState
  | FragmentSourceDatum.lipidKnowledge state => some state
  | _ => none

/-- Pattern-matching accessor for the enclosing sphingoid configuration record. -/
def sphingoidConfigurationPayload? {V : Type*} :
    FragmentSourceDatum V → Option Glycolipid1997.SphingoidConfiguration
  | FragmentSourceDatum.glycolipidSphingoid configuration => some configuration
  | _ => none

/-- Pattern-matching accessor for a centre datum. -/
def sphingoidCenterPayload? {V : Type*} :
    FragmentSourceDatum V → Option (SphingoidCenterPayload V)
  | FragmentSourceDatum.glycolipidCenter center sourceLocant descriptor =>
      some ⟨center, sourceLocant, descriptor⟩
  | _ => none

/-- Pattern-matching accessor for a double-bond datum. -/
def sphingoidDoubleBondPayload? {V : Type*} :
    FragmentSourceDatum V → Option (SphingoidDoubleBondPayload V)
  | FragmentSourceDatum.glycolipidDoubleBond source target sourceLocant descriptor =>
      some ⟨source, target, sourceLocant, descriptor⟩
  | _ => none

def glycerolPayloads {V : Type*} (data : List (FragmentSourceDatum V)) :
    List (GlycerolPayload V) :=
  data.filterMap glycerolPayload?

def fischerPayloads {V : Type*} (data : List (FragmentSourceDatum V)) :
    List (FischerPayload V) :=
  data.filterMap fischerPayload?

def cipPayloads {V : Type*} (data : List (FragmentSourceDatum V)) :
    List (CIPPayload V) :=
  data.filterMap cipPayload?

def knowledgePayloads {V : Type*} (data : List (FragmentSourceDatum V)) :
    List Lipid1976.KnowledgeState :=
  data.filterMap knowledgePayload?

def sphingoidConfigurationPayloads {V : Type*} (data : List (FragmentSourceDatum V)) :
    List Glycolipid1997.SphingoidConfiguration :=
  data.filterMap sphingoidConfigurationPayload?

def sphingoidCenterPayloads {V : Type*} (data : List (FragmentSourceDatum V)) :
    List (SphingoidCenterPayload V) :=
  data.filterMap sphingoidCenterPayload?

def sphingoidDoubleBondPayloads {V : Type*} (data : List (FragmentSourceDatum V)) :
    List (SphingoidDoubleBondPayload V) :=
  data.filterMap sphingoidDoubleBondPayload?

def firstGlycerolPayload? {V : Type*} (data : List (FragmentSourceDatum V)) :
    Option (GlycerolPayload V) :=
  (glycerolPayloads data).head?

/-- Ordered centre annotations recovered from an emitted data list. -/
def recoveredCenterAnnotations {V : Type*} (data : List (FragmentSourceDatum V)) :
    List (Nat × Glycolipid1997.RS) :=
  (sphingoidCenterPayloads data).map fun payload =>
    (payload.sourceLocant, payload.descriptor)

/-- Ordered double-bond annotations recovered from an emitted data list. -/
def recoveredDoubleBondAnnotations {V : Type*} (data : List (FragmentSourceDatum V)) :
    List (Nat × Glycolipid1997.EZ) :=
  (sphingoidDoubleBondPayloads data).map fun payload =>
    (payload.sourceLocant, payload.descriptor)

/-- Recover the whole sphingoid configuration from the emitted data alone. -/
def recoverSphingoidConfiguration? {V : Type*} (data : List (FragmentSourceDatum V)) :
    Option Glycolipid1997.SphingoidConfiguration :=
  (sphingoidConfigurationPayloads data).head?

/-! ### Append and flat-map laws for the accessors -/

@[simp] theorem glycerolPayloads_append {V : Type*}
    (first second : List (FragmentSourceDatum V)) :
    glycerolPayloads (first ++ second) =
      glycerolPayloads first ++ glycerolPayloads second := by
  unfold glycerolPayloads
  exact List.filterMap_append

@[simp] theorem fischerPayloads_append {V : Type*}
    (first second : List (FragmentSourceDatum V)) :
    fischerPayloads (first ++ second) =
      fischerPayloads first ++ fischerPayloads second := by
  unfold fischerPayloads
  exact List.filterMap_append

@[simp] theorem cipPayloads_append {V : Type*}
    (first second : List (FragmentSourceDatum V)) :
    cipPayloads (first ++ second) = cipPayloads first ++ cipPayloads second := by
  unfold cipPayloads
  exact List.filterMap_append

@[simp] theorem knowledgePayloads_append {V : Type*}
    (first second : List (FragmentSourceDatum V)) :
    knowledgePayloads (first ++ second) =
      knowledgePayloads first ++ knowledgePayloads second := by
  unfold knowledgePayloads
  exact List.filterMap_append

@[simp] theorem sphingoidConfigurationPayloads_append {V : Type*}
    (first second : List (FragmentSourceDatum V)) :
    sphingoidConfigurationPayloads (first ++ second) =
      sphingoidConfigurationPayloads first ++ sphingoidConfigurationPayloads second := by
  unfold sphingoidConfigurationPayloads
  exact List.filterMap_append

@[simp] theorem sphingoidCenterPayloads_append {V : Type*}
    (first second : List (FragmentSourceDatum V)) :
    sphingoidCenterPayloads (first ++ second) =
      sphingoidCenterPayloads first ++ sphingoidCenterPayloads second := by
  unfold sphingoidCenterPayloads
  exact List.filterMap_append

@[simp] theorem sphingoidDoubleBondPayloads_append {V : Type*}
    (first second : List (FragmentSourceDatum V)) :
    sphingoidDoubleBondPayloads (first ++ second) =
      sphingoidDoubleBondPayloads first ++ sphingoidDoubleBondPayloads second := by
  unfold sphingoidDoubleBondPayloads
  exact List.filterMap_append

/-- A `filterMap` with an option map composes: mapping inside an accessor is mapping outside the
recovered list. -/
private theorem filterMap_option_map {α β γ : Type*} (values : List α)
    (accessor : α → Option β) (relabel : β → γ) :
    (values.filterMap fun value => (accessor value).map relabel) =
      (values.filterMap accessor).map relabel := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      cases h : accessor head with
      | none => simp [h, ih]
      | some value => simp [h, ih]

/-- The CIP-reading list contributes no glycerol payload. -/
private theorem glycerolPayloads_flatMap_cip
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (readings : List (GlycerolCIPBinding input ledger)) {V : Type*}
    (e : V ≃ SourceAtom input) :
    glycerolPayloads (readings.flatMap (fun reading => reading.sourceData e)) = [] := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [glycerolPayloads_append]
      rw [show glycerolPayloads (head.sourceData e) = [] from rfl]
      rw [ih, List.append_nil]

/-- The CIP-reading list contributes no knowledge payload. -/
private theorem knowledgePayloads_flatMap_cip
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (readings : List (GlycerolCIPBinding input ledger)) {V : Type*}
    (e : V ≃ SourceAtom input) :
    knowledgePayloads (readings.flatMap (fun reading => reading.sourceData e)) = [] := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [knowledgePayloads_append]
      rw [show knowledgePayloads (head.sourceData e) = [] from rfl]
      rw [ih, List.append_nil]

/-- The CIP-reading list contributes no Fischer payload. -/
private theorem fischerPayloads_flatMap_cip
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (readings : List (GlycerolCIPBinding input ledger)) {V : Type*}
    (e : V ≃ SourceAtom input) :
    fischerPayloads (readings.flatMap (fun reading => reading.sourceData e)) = [] := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [fischerPayloads_append]
      rw [show fischerPayloads (head.sourceData e) = [] from rfl]
      rw [ih, List.append_nil]

/-- The CIP-reading list recovers exactly the ordered CIP payloads. -/
private theorem cipPayloads_flatMap_cip
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (readings : List (GlycerolCIPBinding input ledger)) {V : Type*}
    (e : V ≃ SourceAtom input) :
    cipPayloads (readings.flatMap (fun reading => reading.sourceData e)) =
      readings.map (fun reading => ⟨e.symm reading.atom, reading.reading⟩) := by
  induction readings with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [cipPayloads_append]
      rw [show cipPayloads (head.sourceData e) =
          [⟨e.symm head.atom, head.reading⟩] from rfl]
      rw [ih]
      rfl

/-- Emitted double bonds contribute no centre payload. -/
private theorem sphingoidCenterPayloads_flatMap_sourceData
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    {residue : Fin ledger.residueCount}
    (bonds : List (SphingoidDoubleBondBinding input ledger residue)) {V : Type*}
    (e : V ≃ SourceAtom input) :
    sphingoidCenterPayloads (bonds.flatMap (fun bond => bond.sourceData e)) = [] := by
  induction bonds with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [sphingoidCenterPayloads_append]
      rw [show sphingoidCenterPayloads (head.sourceData e) = [] from rfl]
      rw [ih, List.append_nil]

/-- Emitted double bonds recover exactly the ordered double-bond payloads. -/
private theorem sphingoidDoubleBondPayloads_flatMap_sourceData
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    {residue : Fin ledger.residueCount}
    (bonds : List (SphingoidDoubleBondBinding input ledger residue)) {V : Type*}
    (e : V ≃ SourceAtom input) :
    sphingoidDoubleBondPayloads (bonds.flatMap (fun bond => bond.sourceData e)) =
      bonds.map (fun bond =>
        ⟨e.symm bond.sourceAtom, e.symm bond.targetAtom, bond.sourceLocant, bond.descriptor⟩) := by
  induction bonds with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [sphingoidDoubleBondPayloads_append]
      rw [show sphingoidDoubleBondPayloads (head.sourceData e) =
          [⟨e.symm head.sourceAtom, e.symm head.targetAtom, head.sourceLocant,
            head.descriptor⟩] from rfl]
      rw [ih]
      rfl

/-- Emitted double bonds carry no enclosing sphingoid configuration record. -/
private theorem sphingoidConfigurationPayloads_flatMap_sourceData
    {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    {residue : Fin ledger.residueCount}
    (bonds : List (SphingoidDoubleBondBinding input ledger residue)) {V : Type*}
    (e : V ≃ SourceAtom input) :
    sphingoidConfigurationPayloads (bonds.flatMap (fun bond => bond.sourceData e)) = [] := by
  induction bonds with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons]
      rw [sphingoidConfigurationPayloads_append]
      rw [show sphingoidConfigurationPayloads (head.sourceData e) = [] from rfl]
      rw [ih, List.append_nil]

/-! ### Exact accessor equations on single data -/

@[simp] theorem glycerolPayload?_lipidFischer {V : Type*} (center : V)
    (projection : Lipid1976.ReferenceFischerProjection) :
    glycerolPayload? (FragmentSourceDatum.lipidFischer center projection) = none := rfl

@[simp] theorem glycerolPayload?_lipidKnowledge {V : Type*}
    (state : Lipid1976.KnowledgeState) :
    glycerolPayload? (@FragmentSourceDatum.lipidKnowledge V state) = none := rfl

@[simp] theorem glycerolPayload?_lipidCIP {V : Type*} (center : V)
    (reading : Lipid1976.GlycerolCIPReading) :
    glycerolPayload? (FragmentSourceDatum.lipidCIP center reading) = none := rfl

@[simp] theorem fischerPayload?_lipidKnowledge {V : Type*} (state : Lipid1976.KnowledgeState) :
    fischerPayload? (@FragmentSourceDatum.lipidKnowledge V state) = none := rfl

@[simp] theorem fischerPayload?_lipidGlycerol {V : Type*} (first second third : V)
    (substitution : Lipid1976.SnGlycerolSubstitution) :
    fischerPayload? (FragmentSourceDatum.lipidGlycerol first second third substitution) = none :=
  rfl

@[simp] theorem fischerPayload?_lipidCIP {V : Type*} (center : V)
    (reading : Lipid1976.GlycerolCIPReading) :
    fischerPayload? (FragmentSourceDatum.lipidCIP center reading) = none := rfl

@[simp] theorem cipPayload?_lipidKnowledge {V : Type*} (state : Lipid1976.KnowledgeState) :
    cipPayload? (@FragmentSourceDatum.lipidKnowledge V state) = none := rfl

@[simp] theorem cipPayload?_lipidGlycerol {V : Type*} (first second third : V)
    (substitution : Lipid1976.SnGlycerolSubstitution) :
    cipPayload? (FragmentSourceDatum.lipidGlycerol first second third substitution) = none := rfl

@[simp] theorem cipPayload?_lipidFischer {V : Type*} (center : V)
    (projection : Lipid1976.ReferenceFischerProjection) :
    cipPayload? (FragmentSourceDatum.lipidFischer center projection) = none := rfl

@[simp] theorem knowledgePayload?_lipidGlycerol {V : Type*} (first second third : V)
    (substitution : Lipid1976.SnGlycerolSubstitution) :
    knowledgePayload? (FragmentSourceDatum.lipidGlycerol first second third substitution) = none :=
  rfl

@[simp] theorem knowledgePayload?_lipidFischer {V : Type*} (center : V)
    (projection : Lipid1976.ReferenceFischerProjection) :
    knowledgePayload? (FragmentSourceDatum.lipidFischer center projection) = none := rfl

@[simp] theorem knowledgePayload?_lipidCIP {V : Type*} (center : V)
    (reading : Lipid1976.GlycerolCIPReading) :
    knowledgePayload? (FragmentSourceDatum.lipidCIP center reading) = none := rfl

@[simp] theorem sphingoidConfigurationPayload?_lipidGlycerol {V : Type*}
    (first second third : V) (substitution : Lipid1976.SnGlycerolSubstitution) :
    sphingoidConfigurationPayload?
      (FragmentSourceDatum.lipidGlycerol first second third substitution) = none := rfl

@[simp] theorem sphingoidConfigurationPayload?_glycolipidCenter {V : Type*} (center : V)
    (sourceLocant : Nat) (descriptor : Glycolipid1997.RS) :
    sphingoidConfigurationPayload?
      (FragmentSourceDatum.glycolipidCenter center sourceLocant descriptor) = none := rfl

@[simp] theorem sphingoidConfigurationPayload?_glycolipidDoubleBond {V : Type*}
    (source target : V) (sourceLocant : Nat) (descriptor : Glycolipid1997.EZ) :
    sphingoidConfigurationPayload?
      (FragmentSourceDatum.glycolipidDoubleBond source target sourceLocant descriptor) = none :=
  rfl

@[simp] theorem sphingoidCenterPayload?_glycolipidSphingoid {V : Type*}
    (configuration : Glycolipid1997.SphingoidConfiguration) :
    sphingoidCenterPayload?
      (@FragmentSourceDatum.glycolipidSphingoid V configuration) = none := rfl

@[simp] theorem sphingoidCenterPayload?_glycolipidDoubleBond {V : Type*}
    (source target : V) (sourceLocant : Nat) (descriptor : Glycolipid1997.EZ) :
    sphingoidCenterPayload?
      (FragmentSourceDatum.glycolipidDoubleBond source target sourceLocant descriptor) = none :=
  rfl

@[simp] theorem sphingoidDoubleBondPayload?_glycolipidSphingoid {V : Type*}
    (configuration : Glycolipid1997.SphingoidConfiguration) :
    sphingoidDoubleBondPayload?
      (@FragmentSourceDatum.glycolipidSphingoid V configuration) = none := rfl

@[simp] theorem sphingoidDoubleBondPayload?_glycolipidCenter {V : Type*} (center : V)
    (sourceLocant : Nat) (descriptor : Glycolipid1997.RS) :
    sphingoidDoubleBondPayload?
      (FragmentSourceDatum.glycolipidCenter center sourceLocant descriptor) = none := rfl

/-! ### Glycerol recovery theorems -/

namespace SnGlycerolBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Exact glycerol payload recovery. -/
@[simp] theorem glycerolPayloads_sourceData (binding : SnGlycerolBinding input ledger)
    {V : Type*} (e : V ≃ SourceAtom input) :
    glycerolPayloads (binding.sourceData e) =
      [⟨e.symm binding.atOne, e.symm binding.atTwo, e.symm binding.atThree,
        binding.substitution⟩] := by
  rfl

/-- The first (and only) recovered glycerol payload is the original one. -/
theorem firstGlycerolPayload?_sourceData (binding : SnGlycerolBinding input ledger)
    {V : Type*} (e : V ≃ SourceAtom input) :
    firstGlycerolPayload? (binding.sourceData e) =
      some ⟨e.symm binding.atOne, e.symm binding.atTwo, e.symm binding.atThree,
        binding.substitution⟩ := by
  unfold firstGlycerolPayload?
  rw [binding.glycerolPayloads_sourceData]
  rfl

/-- Recover the supplied substitution from the emitted data alone. -/
def recoveredSubstitution? (binding : SnGlycerolBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) : Option Lipid1976.SnGlycerolSubstitution :=
  (firstGlycerolPayload? (binding.sourceData e)).map (fun payload => payload.substitution)

/-- Exact recovery theorem for the glycerol substitution. -/
@[simp] theorem recoveredSubstitution?_sourceData (binding : SnGlycerolBinding input ledger)
    {V : Type*} (e : V ≃ SourceAtom input) :
    binding.recoveredSubstitution? e = some binding.substitution := by
  unfold recoveredSubstitution?
  rw [binding.firstGlycerolPayload?_sourceData]
  rfl

end SnGlycerolBinding

namespace GlycerolCIPBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Exact CIP payload recovery. -/
@[simp] theorem cipPayloads_sourceData (binding : GlycerolCIPBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    cipPayloads (binding.sourceData e) =
      [⟨e.symm binding.atom, binding.reading⟩] := rfl

/-- Both the source numbering and the CIP descriptor are recovered, still as separate values. -/
theorem recovered_numbering_and_cip (binding : GlycerolCIPBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    (cipPayloads (binding.sourceData e)).map
        (fun payload => (payload.reading.fixedSnLocant, payload.reading.cip)) =
      [(binding.reading.fixedSnLocant, binding.reading.cip)] := by
  rw [cipPayloads_sourceData]
  rfl

end GlycerolCIPBinding

namespace FischerBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Exact Fischer payload recovery. -/
@[simp] theorem fischerPayloads_sourceData (binding : FischerBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    fischerPayloads (binding.sourceData e) = [⟨e.symm binding.atom, binding.projection⟩] := rfl

end FischerBinding

namespace GlycerolIngress

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Auxiliary data references no glycerol anchor. -/
theorem glycerolPayloads_auxiliaryData (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    glycerolPayloads (ingress.auxiliaryData e) = [] := by
  unfold GlycerolIngress.auxiliaryData
  rw [glycerolPayloads_append, glycerolPayloads_append]
  rw [show glycerolPayloads
      [FragmentSourceDatum.lipidKnowledge ingress.knowledge] = [] from rfl]
  cases h : ingress.fischer? with
  | none =>
      simp only [h]
      rw [show glycerolPayloads ([] : List (FragmentSourceDatum V)) = [] from rfl]
      rw [glycerolPayloads_flatMap_cip]
      rfl
  | some fischer =>
      simp only [h]
      rw [show glycerolPayloads (fischer.sourceData e) = [] from rfl]
      rw [glycerolPayloads_flatMap_cip]
      rfl

/-- The substitution recovered from the full ingress is the supplied one. -/
theorem recoveredSubstitution?_exact (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    (firstGlycerolPayload? (ingress.sourceData e)).map
        (fun payload => payload.substitution) =
      some ingress.glycerol.substitution := by
  have split : firstGlycerolPayload? (ingress.sourceData e) =
      firstGlycerolPayload? (ingress.glycerol.sourceData e) := by
    unfold GlycerolIngress.sourceData firstGlycerolPayload?
    rw [glycerolPayloads_append, ingress.glycerolPayloads_auxiliaryData, List.append_nil]
  rw [split, SnGlycerolBinding.firstGlycerolPayload?_sourceData]
  rfl

/-- The knowledge claim recovered from the auxiliary data is the supplied one. -/
theorem recoveredKnowledge?_exact (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    (knowledgePayloads (ingress.auxiliaryData e)).head? = some ingress.knowledge := by
  unfold GlycerolIngress.auxiliaryData
  rw [knowledgePayloads_append, knowledgePayloads_append]
  rw [show knowledgePayloads
      [FragmentSourceDatum.lipidKnowledge ingress.knowledge] = [ingress.knowledge] from rfl]
  cases h : ingress.fischer? with
  | none =>
      simp only [h]
      rw [show knowledgePayloads ([] : List (FragmentSourceDatum V)) = [] from rfl]
      rw [knowledgePayloads_flatMap_cip]
      rfl
  | some fischer =>
      simp only [h]
      rw [show knowledgePayloads (fischer.sourceData e) = [] from rfl]
      rw [knowledgePayloads_flatMap_cip]
      rfl

/-- The optional Fischer projection recovered from the auxiliary data is the supplied one. -/
theorem recoveredFischer?_exact (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    fischerPayloads (ingress.auxiliaryData e) =
      (match ingress.fischer? with
       | none => []
       | some fischer => [⟨e.symm fischer.atom, fischer.projection⟩]) := by
  unfold GlycerolIngress.auxiliaryData
  rw [fischerPayloads_append, fischerPayloads_append]
  rw [show fischerPayloads
      [FragmentSourceDatum.lipidKnowledge ingress.knowledge] = [] from rfl]
  cases h : ingress.fischer? with
  | none =>
      simp only [h]
      rw [show fischerPayloads ([] : List (FragmentSourceDatum V)) = [] from rfl]
      rw [fischerPayloads_flatMap_cip]
      rfl
  | some fischer =>
      simp only [h]
      rw [show fischerPayloads (fischer.sourceData e) =
          [⟨e.symm fischer.atom, fischer.projection⟩] from rfl]
      rw [fischerPayloads_flatMap_cip]
      rfl

/-- The ordered CIP readings recovered from the auxiliary data are exactly the supplied ones,
including duplicates and their order. -/
theorem recoveredCIPReadings_exact (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    cipPayloads (ingress.auxiliaryData e) =
      ingress.cipReadings.map (fun reading => ⟨e.symm reading.atom, reading.reading⟩) := by
  unfold GlycerolIngress.auxiliaryData
  rw [cipPayloads_append, cipPayloads_append]
  rw [show cipPayloads
      [FragmentSourceDatum.lipidKnowledge ingress.knowledge] = [] from rfl]
  cases h : ingress.fischer? with
  | none =>
      simp only [h]
      rw [show cipPayloads ([] : List (FragmentSourceDatum V)) = [] from rfl]
      rw [cipPayloads_flatMap_cip]
      rfl
  | some fischer =>
      simp only [h]
      rw [show cipPayloads (fischer.sourceData e) = [] from rfl]
      rw [cipPayloads_flatMap_cip]
      rfl

/-- Repeated CIP claims are preserved with their order and multiplicity. -/
theorem cipReadings_length (ingress : GlycerolIngress input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    (cipPayloads (ingress.auxiliaryData e)).length = ingress.cipReadings.length := by
  rw [ingress.recoveredCIPReadings_exact]
  simp

end GlycerolIngress

/-! ### Sphingoid recovery theorems -/

namespace SphingoidBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Emitted double bonds contribute no enclosing configuration record. -/
private theorem sphingoidConfigurationPayloads_doubleBondData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    sphingoidConfigurationPayloads (binding.doubleBondData e) = [] := by
  unfold SphingoidBinding.doubleBondData
  exact sphingoidConfigurationPayloads_flatMap_sourceData binding.doubleBonds e

/-- Emitted C-4 centre data carries no enclosing configuration record. -/
private theorem sphingoidConfigurationPayloads_c4CenterData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    sphingoidConfigurationPayloads (binding.c4CenterData e) = [] := by
  unfold SphingoidBinding.c4CenterData
  split <;> rfl

/-- Emitted centres contribute no enclosing configuration record. -/
private theorem sphingoidConfigurationPayloads_centerData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    sphingoidConfigurationPayloads (binding.centerData e) = [] := by
  unfold SphingoidBinding.centerData
  rw [sphingoidConfigurationPayloads_append]
  rw [show sphingoidConfigurationPayloads
      [FragmentSourceDatum.glycolipidCenter (e.symm binding.c2Atom) 2 binding.configuration.c2,
       FragmentSourceDatum.glycolipidCenter (e.symm binding.c3Atom) 3 binding.configuration.c3]
      = [] from rfl]
  rw [List.nil_append]
  exact sphingoidConfigurationPayloads_c4CenterData binding e

/-- Exact recovery of the whole configuration. -/
@[simp] theorem recoverSphingoidConfiguration?_sourceData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    recoverSphingoidConfiguration? (binding.sourceData e) = some binding.configuration := by
  unfold recoverSphingoidConfiguration? SphingoidBinding.sourceData
  rw [sphingoidConfigurationPayloads_append, sphingoidConfigurationPayloads_append]
  rw [show sphingoidConfigurationPayloads
      [FragmentSourceDatum.glycolipidSphingoid binding.configuration] =
      [binding.configuration] from rfl]
  rw [show sphingoidConfigurationPayloads (binding.centerData e) = [] from
    sphingoidConfigurationPayloads_centerData binding e]
  rw [show sphingoidConfigurationPayloads (binding.doubleBondData e) = [] from
    sphingoidConfigurationPayloads_doubleBondData binding e]
  rfl

/-- Centre payloads of the centre data: C-2, C-3, then optional C-4, when absent. -/
private theorem sphingoidCenterPayloads_centerData_none
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input)
    (absent : binding.c4? = none) :
    sphingoidCenterPayloads (binding.centerData e) =
      [⟨e.symm binding.c2Atom, 2, binding.configuration.c2⟩,
       ⟨e.symm binding.c3Atom, 3, binding.configuration.c3⟩] := by
  unfold SphingoidBinding.centerData SphingoidBinding.c4CenterData
  rw [sphingoidCenterPayloads_append]
  rw [show sphingoidCenterPayloads
      [FragmentSourceDatum.glycolipidCenter (e.symm binding.c2Atom) 2 binding.configuration.c2,
       FragmentSourceDatum.glycolipidCenter (e.symm binding.c3Atom) 3 binding.configuration.c3]
      = [⟨e.symm binding.c2Atom, 2, binding.configuration.c2⟩,
         ⟨e.symm binding.c3Atom, 3, binding.configuration.c3⟩] from rfl]
  rw [absent]
  rw [show sphingoidCenterPayloads ([] : List (FragmentSourceDatum V)) = [] from rfl]
  rw [List.append_nil]

/-- Centre payloads of the centre data: C-2, C-3, then the claimed C-4, when present. -/
private theorem sphingoidCenterPayloads_centerData_some
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input)
    (atom : SourceAtom input) (descriptor : Glycolipid1997.RS)
    (present : binding.c4? = some (atom, descriptor)) :
    sphingoidCenterPayloads (binding.centerData e) =
      [⟨e.symm binding.c2Atom, 2, binding.configuration.c2⟩,
       ⟨e.symm binding.c3Atom, 3, binding.configuration.c3⟩,
       ⟨e.symm atom, 4, descriptor⟩] := by
  unfold SphingoidBinding.centerData SphingoidBinding.c4CenterData
  rw [sphingoidCenterPayloads_append]
  rw [show sphingoidCenterPayloads
      [FragmentSourceDatum.glycolipidCenter (e.symm binding.c2Atom) 2 binding.configuration.c2,
       FragmentSourceDatum.glycolipidCenter (e.symm binding.c3Atom) 3 binding.configuration.c3]
      = [⟨e.symm binding.c2Atom, 2, binding.configuration.c2⟩,
         ⟨e.symm binding.c3Atom, 3, binding.configuration.c3⟩] from rfl]
  rw [present]
  rfl

/-- Emitted double bonds contribute centre payloads only through the centre data. -/
private theorem sphingoidCenterPayloads_doubleBondData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    sphingoidCenterPayloads (binding.doubleBondData e) = [] := by
  unfold SphingoidBinding.doubleBondData
  exact sphingoidCenterPayloads_flatMap_sourceData binding.doubleBonds e

/-- Double-bond payloads of the emitted double-bond data. -/
private theorem sphingoidDoubleBondPayloads_doubleBondData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    sphingoidDoubleBondPayloads (binding.doubleBondData e) =
      binding.doubleBonds.map (fun bond =>
        ⟨e.symm bond.sourceAtom, e.symm bond.targetAtom, bond.sourceLocant, bond.descriptor⟩) := by
  unfold SphingoidBinding.doubleBondData
  exact sphingoidDoubleBondPayloads_flatMap_sourceData binding.doubleBonds e

/-- Emitted C-4 centre data carries no double-bond payload. -/
private theorem sphingoidDoubleBondPayloads_c4CenterData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    sphingoidDoubleBondPayloads (binding.c4CenterData e) = [] := by
  unfold SphingoidBinding.c4CenterData
  split <;> rfl

/-- Emitted centres contribute no double-bond payload. -/
private theorem sphingoidDoubleBondPayloads_centerData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    sphingoidDoubleBondPayloads (binding.centerData e) = [] := by
  unfold SphingoidBinding.centerData
  rw [sphingoidDoubleBondPayloads_append]
  rw [show sphingoidDoubleBondPayloads
      [FragmentSourceDatum.glycolipidCenter (e.symm binding.c2Atom) 2 binding.configuration.c2,
       FragmentSourceDatum.glycolipidCenter (e.symm binding.c3Atom) 3 binding.configuration.c3]
      = [] from rfl]
  rw [List.nil_append]
  exact sphingoidDoubleBondPayloads_c4CenterData binding e

/-- Exact ordered centre annotations. -/
theorem recoveredCenterAnnotations_sourceData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    recoveredCenterAnnotations (binding.sourceData e) = binding.centerAnnotations := by
  unfold recoveredCenterAnnotations SphingoidBinding.sourceData SphingoidBinding.centerAnnotations
  rw [sphingoidCenterPayloads_append, sphingoidCenterPayloads_append]
  rw [show sphingoidCenterPayloads
      [FragmentSourceDatum.glycolipidSphingoid binding.configuration] = [] from rfl]
  rw [sphingoidCenterPayloads_doubleBondData, List.append_nil]
  exact match h : binding.c4? with
    | none => by
        have hc : binding.configuration.c4Center? = none := by
          have descriptorExact := binding.c4_descriptor_exact
          rw [h] at descriptorExact
          exact descriptorExact.symm
        rw [sphingoidCenterPayloads_centerData_none binding e h]
        simp [hc]
    | some pair => by
        obtain ⟨atom, descriptor⟩ := pair
        have hc : binding.configuration.c4Center? = some descriptor := by
          have descriptorExact := binding.c4_descriptor_exact
          rw [h] at descriptorExact
          exact descriptorExact.symm
        rw [sphingoidCenterPayloads_centerData_some binding e atom descriptor h]
        simp [hc]

/-- Exact ordered double-bond annotations, equal to the configured annotations. -/
theorem recoveredDoubleBondAnnotations_sourceData
    (binding : SphingoidBinding input ledger) {V : Type*} (e : V ≃ SourceAtom input) :
    recoveredDoubleBondAnnotations (binding.sourceData e) = binding.configuration.doubleBonds := by
  unfold recoveredDoubleBondAnnotations SphingoidBinding.sourceData
  rw [sphingoidDoubleBondPayloads_append, sphingoidDoubleBondPayloads_append]
  rw [show sphingoidDoubleBondPayloads
      [FragmentSourceDatum.glycolipidSphingoid binding.configuration] = [] from rfl]
  rw [sphingoidDoubleBondPayloads_centerData, List.nil_append]
  rw [sphingoidDoubleBondPayloads_doubleBondData]
  rw [List.nil_append]
  rw [List.map_map]
  exact binding.doubleBondAnnotations_exact

/-- The emitted double-bond data has exactly as many entries as the configured annotations. -/
theorem doubleBondData_length (binding : SphingoidBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) :
    (binding.doubleBondData e).length = binding.configuration.doubleBonds.length := by
  have lengthEq : ∀ (bonds : List (SphingoidDoubleBondBinding input ledger binding.residue)),
      (bonds.flatMap (fun bond => bond.sourceData e)).length = bonds.length := by
    intro bonds
    induction bonds with
    | nil => rfl
    | cons head tail ih =>
        rw [List.flatMap_cons]
        rw [List.length_append, ih]
        rw [show (head.sourceData e).length = 1 from rfl]
        rw [List.length_cons]
        exact Nat.add_comm 1 tail.length
  unfold SphingoidBinding.doubleBondData
  rw [lengthEq]
  simpa using congrArg List.length binding.doubleBondAnnotations_exact

end SphingoidBinding

/-! ## Atom references and support

The emitted data reference exactly the source atoms named by the bindings.  The support theorems
let the caller extend an existing `FragmentAnnotation` without inventing membership. -/

/-- Every datum atom reference lies in the supplied support. -/
def SourceDataSupported {V : Type*} (support : Finset V)
    (data : List (FragmentSourceDatum V)) : Prop :=
  ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ support

namespace SourceDataSupported

variable {V : Type*} {support : Finset V}

theorem nil : SourceDataSupported support ([] : List (FragmentSourceDatum V)) := by
  intro datum member
  simp at member

theorem cons {datum : FragmentSourceDatum V} {rest : List (FragmentSourceDatum V)}
    (headSupported : ∀ atom ∈ datum.atomReferences, atom ∈ support)
    (tailSupported : SourceDataSupported support rest) :
    SourceDataSupported support (datum :: rest) := by
  intro other member atom atomMem
  rcases List.mem_cons.mp member with rfl | restMember
  · exact headSupported atom atomMem
  · exact tailSupported other restMember atom atomMem

theorem append {first second : List (FragmentSourceDatum V)}
    (firstSupported : SourceDataSupported support first)
    (secondSupported : SourceDataSupported support second) :
    SourceDataSupported support (first ++ second) := by
  intro datum member atom atomMem
  rcases List.mem_append.mp member with old | fresh
  · exact firstSupported datum old atom atomMem
  · exact secondSupported datum fresh atom atomMem

theorem singleton {datum : FragmentSourceDatum V}
    (supported : ∀ atom ∈ datum.atomReferences, atom ∈ support) :
    SourceDataSupported support [datum] :=
  cons supported nil

end SourceDataSupported

namespace SnGlycerolBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Emitted glycerol data is supported by any support containing the three resolved atoms. -/
theorem sourceData_supported (binding : SnGlycerolBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) {support : Finset V}
    (atOneMem : e.symm binding.atOne ∈ support)
    (atTwoMem : e.symm binding.atTwo ∈ support)
    (atThreeMem : e.symm binding.atThree ∈ support) :
    SourceDataSupported support (binding.sourceData e) := by
  apply SourceDataSupported.singleton
  intro atom atomMem
  simp only [FragmentSourceDatum.atomReferences_lipidGlycerol, List.mem_cons,
    List.not_mem_nil, or_false] at atomMem
  rcases atomMem with rfl | rfl | rfl
  · exact atOneMem
  · exact atTwoMem
  · exact atThreeMem

end SnGlycerolBinding

namespace SphingoidBinding

variable {input : CertifiedAuthoritativeChemicalInput}
variable {ledger : ResidueIncidenceLedger Nat input}

/-- Emitted sphingoid data is supported whenever the support contains C-2, C-3, every claimed
C-4 atom and both atoms of every bound double bond. -/
theorem sourceData_supported (binding : SphingoidBinding input ledger) {V : Type*}
    (e : V ≃ SourceAtom input) {support : Finset V}
    (c2Mem : e.symm binding.c2Atom ∈ support)
    (c3Mem : e.symm binding.c3Atom ∈ support)
    (c4Mem : ∀ (atom : SourceAtom input) (descriptor : Glycolipid1997.RS),
      binding.c4? = some (atom, descriptor) → e.symm atom ∈ support)
    (bondMem : ∀ bond ∈ binding.doubleBonds,
      e.symm bond.sourceAtom ∈ support ∧ e.symm bond.targetAtom ∈ support) :
    SourceDataSupported support (binding.sourceData e) := by
  have c4Supported : SourceDataSupported support (binding.c4CenterData e) := by
    unfold SphingoidBinding.c4CenterData
    cases h : binding.c4? with
    | none => exact SourceDataSupported.nil
    | some pair =>
        obtain ⟨atom, descriptor⟩ := pair
        apply SourceDataSupported.singleton
        intro other otherMem
        simp only [FragmentSourceDatum.atomReferences_glycolipidCenter, List.mem_singleton]
          at otherMem
        subst other
        exact c4Mem atom descriptor h
  have centerSupported : SourceDataSupported support (binding.centerData e) := by
    unfold SphingoidBinding.centerData
    change SourceDataSupported support
      (FragmentSourceDatum.glycolipidCenter (e.symm binding.c2Atom) 2 binding.configuration.c2
        :: FragmentSourceDatum.glycolipidCenter (e.symm binding.c3Atom) 3 binding.configuration.c3
          :: binding.c4CenterData e)
    apply SourceDataSupported.cons
    · intro atom atomMem
      simp only [FragmentSourceDatum.atomReferences_glycolipidCenter, List.mem_singleton]
        at atomMem
      subst atom
      exact c2Mem
    apply SourceDataSupported.cons
    · intro atom atomMem
      simp only [FragmentSourceDatum.atomReferences_glycolipidCenter, List.mem_singleton]
        at atomMem
      subst atom
      exact c3Mem
    exact c4Supported
  have bondsSupported : SourceDataSupported support (binding.doubleBondData e) := by
    unfold SphingoidBinding.doubleBondData
    have aux : ∀ (bonds : List (SphingoidDoubleBondBinding input ledger binding.residue)),
        (∀ bond ∈ bonds,
          e.symm bond.sourceAtom ∈ support ∧ e.symm bond.targetAtom ∈ support) →
        SourceDataSupported support (bonds.flatMap fun bond => bond.sourceData e) := by
      intro bonds
      induction bonds with
      | nil =>
          intro _
          exact SourceDataSupported.nil
      | cons head tail ih =>
          intro hb
          rw [List.flatMap_cons]
          change SourceDataSupported support
            (FragmentSourceDatum.glycolipidDoubleBond (e.symm head.sourceAtom)
              (e.symm head.targetAtom) head.sourceLocant head.descriptor
                :: tail.flatMap (fun bond => bond.sourceData e))
          apply SourceDataSupported.cons
          · intro atom atomMem
            simp only [FragmentSourceDatum.atomReferences_glycolipidDoubleBond,
              List.mem_cons, List.not_mem_nil, or_false] at atomMem
            rcases atomMem with rfl | rfl
            · exact (hb head (by simp)).1
            · exact (hb head (by simp)).2
          · exact ih (fun bond member => hb bond (by simp [member]))
    exact aux binding.doubleBonds bondMem
  unfold SphingoidBinding.sourceData
  change SourceDataSupported support
    (FragmentSourceDatum.glycolipidSphingoid binding.configuration
      :: (binding.centerData e ++ binding.doubleBondData e))
  apply SourceDataSupported.cons
  · intro atom atomMem
    simp only [FragmentSourceDatum.atomReferences_glycolipidSphingoid] at atomMem
    exact False.elim (List.not_mem_nil atomMem)
  · exact SourceDataSupported.append centerSupported bondsSupported

end SphingoidBinding

/-! ## Attaching the emitted data to a fragment annotation -/

/-- Attach ordered source data to an existing fragment annotation, **appending** after any data
already present.  Support, locant bindings and prior source data are untouched. -/
def attachSourceData {V : Type*} (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : SourceDataSupported annotation.support data) : FragmentAnnotation V :=
  annotation.withSourceData data supported

@[simp] theorem attachSourceData_sourceData {V : Type*} (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : SourceDataSupported annotation.support data) :
    (attachSourceData annotation data supported).sourceData = annotation.sourceData ++ data :=
  FragmentAnnotation.withSourceData_sourceData annotation data supported

@[simp] theorem attachSourceData_support {V : Type*} (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : SourceDataSupported annotation.support data) :
    (attachSourceData annotation data supported).support = annotation.support :=
  FragmentAnnotation.withSourceData_support annotation data supported

@[simp] theorem attachSourceData_bindings {V : Type*} (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : SourceDataSupported annotation.support data) :
    (attachSourceData annotation data supported).bindings = annotation.bindings :=
  FragmentAnnotation.withSourceData_bindings annotation data supported

/-! ## Relabelling preserves every source payload -/

/-- Relabel a whole emitted list. -/
def relabelSourceData {V W : Type*} (f : V ≃ W)
    (data : List (FragmentSourceDatum V)) : List (FragmentSourceDatum W) :=
  data.map (FragmentSourceDatum.relabel f)

@[simp] theorem glycerolPayload?_relabel {V W : Type*} (f : V ≃ W)
    (datum : FragmentSourceDatum V) :
    glycerolPayload? (FragmentSourceDatum.relabel f datum) =
      (glycerolPayload? datum).map (fun payload =>
        ⟨f payload.atOne, f payload.atTwo, f payload.atThree, payload.substitution⟩) := by
  cases datum <;> rfl

@[simp] theorem fischerPayload?_relabel {V W : Type*} (f : V ≃ W)
    (datum : FragmentSourceDatum V) :
    fischerPayload? (FragmentSourceDatum.relabel f datum) =
      (fischerPayload? datum).map (fun payload => ⟨f payload.center, payload.projection⟩) := by
  cases datum <;> rfl

@[simp] theorem cipPayload?_relabel {V W : Type*} (f : V ≃ W)
    (datum : FragmentSourceDatum V) :
    cipPayload? (FragmentSourceDatum.relabel f datum) =
      (cipPayload? datum).map (fun payload => ⟨f payload.center, payload.reading⟩) := by
  cases datum <;> rfl

@[simp] theorem knowledgePayload?_relabel {V W : Type*} (f : V ≃ W)
    (datum : FragmentSourceDatum V) :
    knowledgePayload? (FragmentSourceDatum.relabel f datum) = knowledgePayload? datum := by
  cases datum <;> rfl

@[simp] theorem sphingoidConfigurationPayload?_relabel {V W : Type*} (f : V ≃ W)
    (datum : FragmentSourceDatum V) :
    sphingoidConfigurationPayload? (FragmentSourceDatum.relabel f datum) =
      sphingoidConfigurationPayload? datum := by
  cases datum <;> rfl

@[simp] theorem sphingoidCenterPayload?_relabel {V W : Type*} (f : V ≃ W)
    (datum : FragmentSourceDatum V) :
    sphingoidCenterPayload? (FragmentSourceDatum.relabel f datum) =
      (sphingoidCenterPayload? datum).map (fun payload =>
        ⟨f payload.center, payload.sourceLocant, payload.descriptor⟩) := by
  cases datum <;> rfl

@[simp] theorem sphingoidDoubleBondPayload?_relabel {V W : Type*} (f : V ≃ W)
    (datum : FragmentSourceDatum V) :
    sphingoidDoubleBondPayload? (FragmentSourceDatum.relabel f datum) =
      (sphingoidDoubleBondPayload? datum).map (fun payload =>
        ⟨f payload.sourceAtom, f payload.targetAtom, payload.sourceLocant,
          payload.descriptor⟩) := by
  cases datum <;> rfl

/-- Relabelling commutes with recovering a glycerol payload list. -/
private theorem filterMap_glycerolPayload?_map_relabel {V W : Type*}
    (f : V ≃ W) (data : List (FragmentSourceDatum V)) :
    (data.map (FragmentSourceDatum.relabel f)).filterMap glycerolPayload? =
      (data.filterMap glycerolPayload?).map (fun payload =>
        ⟨f payload.atOne, f payload.atTwo, f payload.atThree, payload.substitution⟩) := by
  rw [List.filterMap_map]
  change data.filterMap (fun datum => glycerolPayload? (FragmentSourceDatum.relabel f datum)) =
    (data.filterMap glycerolPayload?).map (fun payload =>
      ⟨f payload.atOne, f payload.atTwo, f payload.atThree, payload.substitution⟩)
  simp only [glycerolPayload?_relabel]
  exact filterMap_option_map data glycerolPayload? _

/-- Relabelling leaves the recovered sphingoid configuration list unchanged. -/
private theorem filterMap_sphingoidConfigurationPayload?_map_relabel {V W : Type*}
    (f : V ≃ W) (data : List (FragmentSourceDatum V)) :
    (data.map (FragmentSourceDatum.relabel f)).filterMap sphingoidConfigurationPayload? =
      data.filterMap sphingoidConfigurationPayload? := by
  rw [List.filterMap_map]
  change data.filterMap
      (fun datum => sphingoidConfigurationPayload? (FragmentSourceDatum.relabel f datum)) =
    data.filterMap sphingoidConfigurationPayload?
  simp only [sphingoidConfigurationPayload?_relabel]

/-- Relabelling changes only atom anchors: the recovered glycerol substitution is unchanged. -/
theorem recoveredSubstitution?_relabel {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SnGlycerolBinding input ledger)
    {V W : Type*} (e : V ≃ SourceAtom input) (f : V ≃ W) :
    (firstGlycerolPayload? (relabelSourceData f (binding.sourceData e))).map
        (fun payload => payload.substitution) =
      (firstGlycerolPayload? (binding.sourceData e)).map
        (fun payload => payload.substitution) := by
  unfold relabelSourceData firstGlycerolPayload? glycerolPayloads
  rw [filterMap_glycerolPayload?_map_relabel]
  rw [List.head?_map]
  cases h : (binding.sourceData e).filterMap glycerolPayload? with
  | nil => rfl
  | cons payload rest => rfl

/-- Relabelling changes only atom anchors: the recovered sphingoid configuration is unchanged. -/
theorem recoverSphingoidConfiguration?_relabel {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (binding : SphingoidBinding input ledger)
    {V W : Type*} (e : V ≃ SourceAtom input) (f : V ≃ W) :
    recoverSphingoidConfiguration? (relabelSourceData f (binding.sourceData e)) =
      recoverSphingoidConfiguration? (binding.sourceData e) := by
  unfold relabelSourceData recoverSphingoidConfiguration? sphingoidConfigurationPayloads
  rw [filterMap_sphingoidConfigurationPayload?_map_relabel]

end LipidAnnotationIngress

end TetraStereo.OneCenter

/-! ## Kernel-authority guards for the decisive recovery theorems -/

assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SnGlycerolBinding.firstGlycerolPayload?_sourceData
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SnGlycerolBinding.recoveredSubstitution?_sourceData
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.GlycerolCIPBinding.recovered_numbering_and_cip
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.GlycerolIngress.recoveredSubstitution?_exact
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.GlycerolIngress.recoveredKnowledge?_exact
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.GlycerolIngress.recoveredFischer?_exact
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.GlycerolIngress.recoveredCIPReadings_exact
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SphingoidBinding.recoverSphingoidConfiguration?_sourceData
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SphingoidBinding.recoveredCenterAnnotations_sourceData
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SphingoidBinding.recoveredDoubleBondAnnotations_sourceData
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SphingoidBinding.doubleBondData_length
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SphingoidBinding.configured_doubleBond_has_occurrence
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.SphingoidDoubleBondBinding.real_occurrence
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.recoveredSubstitution?_relabel
assert_kernel_only
  TetraStereo.OneCenter.LipidAnnotationIngress.recoverSphingoidConfiguration?_relabel
