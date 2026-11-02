import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace TetraStereo.OneCenter

variable {V : Type*} [DecidableEq V] [Fintype V]

namespace OrganicStereoIndependentElectronicEncoding

/-- Extensionality for independently supplied electronic site sources.  The only
proposition-valued field is the source-semantic unpaired-electron tie; two sources with the same
counts are therefore equal.  This is used below to recover a supplied source from its ingress
without assuming the source's own proof term. -/
theorem IndependentElectronicSiteSource.ext {graph : FiniteAtomInteractionHypergraph V}
    {first second : IndependentElectronicSiteSource graph}
    (counts : first.siteCounts = second.siteCounts) : first = second := by
  cases first with
  | mk firstCounts firstTied =>
    cases second with
    | mk secondCounts secondTied =>
      dsimp only at counts
      cases counts
      have tied : firstTied = secondTied := Subsingleton.elim _ _
      rw [tied]

end OrganicStereoIndependentElectronicEncoding

namespace OrganicStereoElectronicDescriptionIngress

open OrganicStereoElectronicSites
open OrganicStereoElectronicSites.ReferenceGeometryEvidence
open OrganicStereoIndependentElectronicEncoding

/-!
# Ingress of an independent electronic description into the whole state

The whole-state record `WholeState V E B` already carries an optional electronic channel
(`ElectronicChannel V`) together with the single source-semantic tie to the graph.  The staged
electronic modules supply an *independent* source over atom labels and an independent per-site
evidence assignment

* `source : IndependentElectronicSiteSource graph`, with the only graph tie
  `(source.siteCounts.counts owner).unpairedElectronPositions =
    (graph.atomData owner).unpairedElectrons`, and
* `assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence`, one
  `ReferenceGeometryEvidence` value at each counted `(owner, kind, slot)` identity.

This module builds the actual ingress of exactly those data into `WholeState V (Fin 0) (Fin 0)`:

* `electronic? = some channel`, where the channel's counts are the supplied
  `source.siteCounts` and its per-owner/per-kind evidence list is the canonical enumeration of the
  supplied assignment over the actual `Fin` slots;
* the channel's evidence list length is proved equal to the supplied multiplicity, so no slot is
  invented or dropped;
* the whole-state unpaired tie is *derived* from `source.unpaired_tied`, not assumed;
* every irrelevant channel is empty: no roles, no paths (`Fin 0`), no bands (`Fin 0`), no drawing
  data, no fragments, no conventions and no cages, and the optional rational positions are absent;
* the supplied conformation is stored literally.

The main results are the actual recoveries

* `toIndependentElectronicSiteSource` returns the originally supplied source,
* `electronicAssignment` returns the originally supplied evidence assignment, and
* the per-site evidence therefore recovers every supplied value, including all four
  `ReferenceGeometryEvidence` constructors (absence of a component is never confused with an
  explicit zero).

A separate `ingressStateWithoutElectronic` constructor keeps a genuinely absent inventory
(`electronic? = none`) distinct from a present channel with all-zero counts.
-/

/-! ## The canonical per-slot evidence list -/

/-- The ordered list of per-slot reference geometry evidence at one owner and site kind.  Its
positions are the supplied `Fin` slots, in order, so every counted identity occurs exactly once and
no evidence is fabricated. -/
def ingressEvidence {graph : FiniteAtomInteractionHypergraph V}
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind) : List ReferenceGeometryEvidence :=
  List.ofFn fun slot : Fin ((source.siteCounts.counts owner).count kind) =>
    assignment.valueAt ⟨owner, kind, slot⟩

/-- The evidence list at an owner and kind has exactly the supplied multiplicity.  This is the
field required by `ElectronicChannel`, proved rather than assumed. -/
@[simp] theorem ingressEvidence_length {graph : FiniteAtomInteractionHypergraph V}
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind) :
    (ingressEvidence source assignment owner kind).length =
      (source.siteCounts.counts owner).count kind := by
  simp [ingressEvidence]

/-- A generic list lookup lemma: reading `List.ofFn f` at the numeral of an index `i` returns
`f i`, whatever proof of the length bound is supplied. -/
theorem get_ofFn_value {n : ℕ} {α : Type*} (f : Fin n → α) (index : Fin n)
    (bound : index.val < (List.ofFn f).length) :
    (List.ofFn f).get ⟨index.val, bound⟩ = f index := by
  rw [List.get_ofFn]
  congr 1

/-- At every counted owner/kind/slot identity, the evidence list holds exactly the assigned
evidence at that identity.  The dependent slot bound is handled by `get_ofFn_value`. -/
theorem ingressEvidence_get {graph : FiniteAtomInteractionHypergraph V}
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind)
    (slot : Fin ((source.siteCounts.counts owner).count kind))
    (bound : slot.val < (ingressEvidence source assignment owner kind).length) :
    (ingressEvidence source assignment owner kind).get ⟨slot.val, bound⟩ =
      assignment.valueAt ⟨owner, kind, slot⟩ := by
  unfold ingressEvidence at bound ⊢
  exact get_ofFn_value _ slot bound

/-! ## The electronic channel and the whole state -/

/-- The electronic channel ingressing the independent source and assignment: the supplied counts
literally, and per owner/kind the canonical slot enumeration of the supplied evidence. -/
def ingressChannel {graph : FiniteAtomInteractionHypergraph V}
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    ElectronicChannel V where
  counts := source.siteCounts
  evidence := ingressEvidence source assignment
  evidence_length := ingressEvidence_length source assignment

/-- The ingress channel's counts are exactly the independent counts. -/
@[simp] theorem ingressChannel_counts {graph : FiniteAtomInteractionHypergraph V}
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (ingressChannel source assignment).counts = source.siteCounts := rfl

/-- The ingress channel's evidence is exactly the canonical slot enumeration. -/
@[simp] theorem ingressChannel_evidence {graph : FiniteAtomInteractionHypergraph V}
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (ingressChannel source assignment).evidence = ingressEvidence source assignment := rfl

/-- The actual whole state obtained from a graph, an independently supplied conformation, an
independent electronic source and an independent evidence assignment, with every irrelevant
channel empty (`Fin 0` paths and bands, no drawing, fragment, convention or cage data) and the
optional rational positions absent.  The electronic inventory is present (`some`), never absent and
never fabricated. -/
def ingressState {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    WholeState V (Fin 0) (Fin 0) where
  graph := graph
  electronic? := some (ingressChannel source assignment)
  electronic_unpaired := by
    intro channel present owner
    have channelEq : ingressChannel source assignment = channel := Option.some_inj.mp present
    subst channel
    exact source.unpaired_tied owner
  conformation := conformation
  rationalPositions_valid := by
    intro positions present
    simp at present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  paths := fun edge => Fin.elim0 edge
  path_valid := fun edge => Fin.elim0 edge
  path_source_endpoint := fun edge => Fin.elim0 edge
  path_target_endpoint := fun edge => Fin.elim0 edge
  bandFamily := fun band => Fin.elim0 band
  band_agreement := fun band => Fin.elim0 band
  diagram_valid := by
    intro row member
    simp at member

/-- The ingress state keeps the supplied graph literally. -/
@[simp] theorem ingressState_graph {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (ingressState conformation source assignment).graph = graph := rfl

/-- The ingress state stores the supplied conformation literally. -/
@[simp] theorem ingressState_conformation {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (ingressState conformation source assignment).conformation = conformation := rfl

/-- The electronic inventory is present, and is exactly the ingress channel. -/
@[simp] theorem ingressState_electronic? {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (ingressState conformation source assignment).electronic? =
      some (ingressChannel source assignment) := rfl

/-- The whole-state unpaired tie is derived from the independent source, not assumed: it is the
source's own source-semantic tie at every label. -/
theorem ingressState_unpaired {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) :
    ((ingressChannel source assignment).counts.counts owner).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons :=
  (ingressState conformation source assignment).electronic_unpaired
    (ingressChannel source assignment) rfl owner

/-! ## Recovery of the supplied source -/

/-- The existing `toIndependentElectronicSiteSource` projection of the ingress recovers the
originally supplied independent source exactly, including its counts and its own unpaired tie. -/
theorem ingressState_toIndependentElectronicSiteSource
    {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    toIndependentElectronicSiteSource (ingressState conformation source assignment)
      (ingressChannel source assignment) rfl = source := by
  apply IndependentElectronicSiteSource.ext
  rfl

/-- The recovered source's whole count record at a label is the supplied record. -/
theorem ingressState_counts {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (toIndependentElectronicSiteSource (ingressState conformation source assignment)
      (ingressChannel source assignment) rfl).siteCounts = source.siteCounts := by
  rw [ingressState_toIndependentElectronicSiteSource]

/-- At every label, the recovered inventory's multiplicity of every kind is the supplied one. -/
theorem ingressState_counts_apply {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind) :
    (((toIndependentElectronicSiteSource (ingressState conformation source assignment)
        (ingressChannel source assignment) rfl).siteCounts.counts owner).count kind) =
      (source.siteCounts.counts owner).count kind := by
  rw [ingressState_toIndependentElectronicSiteSource]

/-! ## Recovery of the supplied evidence assignment -/

/-- The existing `electronicAssignment` projection of the ingress recovers the supplied evidence
assignment exactly.  The dependent slot equalities are discharged by `ingressEvidence_get`; no
evidence value is altered and no slot is added or removed. -/
theorem ingressState_electronicAssignment {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    electronicAssignment (ingressState conformation source assignment)
      (ingressChannel source assignment) rfl = assignment := by
  apply IndependentSiteAssignment.ext
  intro identity
  exact ingressEvidence_get source assignment identity.owner identity.kind identity.slot _

/-- At every supplied identity, the projected evidence is exactly the supplied evidence. -/
theorem ingressState_evidenceAt {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (identity : IndependentSiteIdentity source.siteCounts) :
    (electronicAssignment (ingressState conformation source assignment)
      (ingressChannel source assignment) rfl).valueAt identity = assignment.valueAt identity := by
  rw [ingressState_electronicAssignment]

/-- The actual evidence stored at every site lies in one of the four states of
`ReferenceGeometryEvidence`: absent, point only, direction only, or both.  This is inherited from
the supplied assignment, so the ingress genuinely carries full four-case evidence rather than a
collapsed complete geometry. -/
theorem ingressState_evidence_cases {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (identity : IndependentSiteIdentity source.siteCounts) :
    (electronicAssignment (ingressState conformation source assignment)
        (ingressChannel source assignment) rfl).valueAt identity = unspecified ∨
      (∃ point,
        (electronicAssignment (ingressState conformation source assignment)
          (ingressChannel source assignment) rfl).valueAt identity = pointOnly point) ∨
      (∃ direction,
        (electronicAssignment (ingressState conformation source assignment)
          (ingressChannel source assignment) rfl).valueAt identity = directionOnly direction) ∨
      (∃ point direction,
        (electronicAssignment (ingressState conformation source assignment)
            (ingressChannel source assignment) rfl).valueAt identity =
          pointAndDirection point direction) := by
  rw [ingressState_electronicAssignment]
  exact evidence_cases (assignment.valueAt identity)

/-- Ingress is injective on the supplied evidence assignment: the whole-state constructor does not
merge two distinct assignments.  Evidence is recovered pointwise through the actual channel. -/
theorem ingressState_assignment_injective {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph) :
    Function.Injective fun assignment :
        IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence =>
      ingressState conformation source assignment := by
  intro first second equal
  have someEq : some (ingressChannel source first) = some (ingressChannel source second) := by
    simpa [ingressState] using
      congrArg (fun state : WholeState V (Fin 0) (Fin 0) => state.electronic?) equal
  have channelEq : ingressChannel source first = ingressChannel source second :=
    Option.some_inj.mp someEq
  have evidenceEq :
      (ingressChannel source first).evidence = (ingressChannel source second).evidence :=
    congrArg (fun channel : ElectronicChannel V => channel.evidence) channelEq
  apply IndependentSiteAssignment.ext
  intro identity
  rcases identity with ⟨owner, kind, slot⟩
  have atKind :
      ingressEvidence source first owner kind = ingressEvidence source second owner kind :=
    congrFun (congrFun evidenceEq owner) kind
  have functionsEq :
      (fun slot : Fin ((source.siteCounts.counts owner).count kind) =>
          first.valueAt ⟨owner, kind, slot⟩) =
        (fun slot => second.valueAt ⟨owner, kind, slot⟩) := by
    simpa [ingressEvidence] using atKind
  exact congrFun functionsEq slot

/-! ## Genuine absence of an electronic inventory

`electronic? = none` records that no inventory was supplied.  It is kept as a separate constructor
and is never identified with a present channel of all-zero counts. -/

/-- The same empty-shell whole state but with no electronic inventory at all.  Every other channel
is exactly as in `ingressState`. -/
def ingressStateWithoutElectronic {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V) : WholeState V (Fin 0) (Fin 0) where
  graph := graph
  electronic? := none
  electronic_unpaired := by
    intro channel present
    simp at present
  conformation := conformation
  rationalPositions_valid := by
    intro positions present
    simp at present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  paths := fun edge => Fin.elim0 edge
  path_valid := fun edge => Fin.elim0 edge
  path_source_endpoint := fun edge => Fin.elim0 edge
  path_target_endpoint := fun edge => Fin.elim0 edge
  bandFamily := fun band => Fin.elim0 band
  band_agreement := fun band => Fin.elim0 band
  diagram_valid := by
    intro row member
    simp at member

/-- The absent-inventory state really has no electronic channel. -/
@[simp] theorem ingressStateWithoutElectronic_electronic? {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V) :
    (ingressStateWithoutElectronic (graph := graph) conformation).electronic? = none := rfl

/-- A present inventory (even of all-zero counts) is not the absent inventory. -/
theorem ingressState_ne_withoutElectronic {graph : FiniteAtomInteractionHypergraph V}
    (conformation : MolecularConformation V)
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    ingressState conformation source assignment ≠
      ingressStateWithoutElectronic (graph := graph) conformation := by
  intro equal
  have present := congrArg (fun state => state.electronic?) equal
  simp [ingressState, ingressStateWithoutElectronic] at present

/-! ## A concrete non-vacuous ingress -/

namespace Example

/-- A concrete conformation on the two labels of the existing electronic example. -/
def conformation : MolecularConformation (Fin 2) := fun _ => 0

/-- Concrete whole-state evidence: a point together with a direction, the fourth constructor of
`ReferenceGeometryEvidence`. -/
def assignment : IndependentSiteAssignment exampleSource.siteCounts ReferenceGeometryEvidence :=
  IndependentSiteAssignment.constant
    (ReferenceGeometryEvidence.pointAndDirection
      EvidenceFacts.originPoint EvidenceFacts.zeroDirection)

/-- The concrete ingress of the existing two-label electronic example. -/
def state : WholeState (Fin 2) (Fin 0) (Fin 0) :=
  ingressState conformation exampleSource assignment

/-- The concrete ingress recovers the existing independent source. -/
theorem state_source :
    toIndependentElectronicSiteSource state (ingressChannel exampleSource assignment) rfl =
      exampleSource :=
  ingressState_toIndependentElectronicSiteSource conformation exampleSource assignment

/-- The concrete ingress recovers the supplied evidence at the existing site identity. -/
theorem state_evidence :
    (electronicAssignment state (ingressChannel exampleSource assignment) rfl).valueAt
        exampleIdentity =
      ReferenceGeometryEvidence.pointAndDirection
        EvidenceFacts.originPoint EvidenceFacts.zeroDirection := by
  show (electronicAssignment (ingressState conformation exampleSource assignment)
      (ingressChannel exampleSource assignment) rfl).valueAt exampleIdentity = _
  rw [ingressState_electronicAssignment]
  rfl

/-- The concrete present inventory is distinct from the absent-inventory constructor. -/
theorem state_ne_absent :
    state ≠ ingressStateWithoutElectronic (graph := exampleGraph) conformation :=
  ingressState_ne_withoutElectronic conformation exampleSource assignment

end Example

end OrganicStereoElectronicDescriptionIngress

end TetraStereo.OneCenter
