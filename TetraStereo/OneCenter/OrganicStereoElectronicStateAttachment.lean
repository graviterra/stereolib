import TetraStereo.OneCenter.OrganicStereoElectronicDescriptionIngress

set_option autoImplicit false

namespace TetraStereo.OneCenter

open OrganicStereoElectronicSites
open OrganicStereoElectronicSites.ReferenceGeometryEvidence
open OrganicStereoIndependentElectronicEncoding
open OrganicStereoElectronicDescriptionIngress

variable {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
















































namespace OrganicStereoElectronicStateAttachment

/-! ## The attachment operation -/

/-- Attach a supplied electronic inventory and evidence assignment to an arbitrary whole state.
Only `electronic?` and `electronic_unpaired` are updated; the graph, conformation, paths, bands,
roles and all annotation channels are inherited from `state` by the record update.  The new
unpaired tie is derived from the supplied source at the newly stored channel. -/
def attachElectronic (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    WholeState V E B :=
  { state with
    electronic? := some (ingressChannel source assignment)
    electronic_unpaired := by
      intro channel present owner
      have channelEq : ingressChannel source assignment = channel :=
        Option.some_inj.mp present
      subst channel
      exact source.unpaired_tied owner }

/-! ## Every other field is inherited literally -/

/-- The graph is unchanged. -/
@[simp] theorem attachElectronic_graph (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).graph = state.graph := rfl

/-- The stored inventory is exactly the supplied ingress channel.  This is the replacement, not a
recovery of any previous inventory. -/
@[simp] theorem attachElectronic_electronic? (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).electronic? =
      some (ingressChannel source assignment) := rfl

/-- The shared conformation is unchanged. -/
@[simp] theorem attachElectronic_conformation (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).conformation = state.conformation := rfl

/-- An absent optional rational position channel stays absent; a present one is unchanged. -/
@[simp] theorem attachElectronic_rationalPositions? (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).rationalPositions? =
      state.rationalPositions? := rfl

/-- The ordered role ledger, with every annotation, is unchanged. -/
@[simp] theorem attachElectronic_roles (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).roles = state.roles := rfl

/-- Every bond path, with its occurrence index, oriented endpoints and arc, is unchanged. -/
@[simp] theorem attachElectronic_paths (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (edge : E) :
    (attachElectronic state source assignment).paths edge = state.paths edge := rfl

/-- Every band attachment family, with its band, attachment type and parameter, is unchanged. -/
@[simp] theorem attachElectronic_bandFamily (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (band : B) :
    (attachElectronic state source assignment).bandFamily band = state.bandFamily band := rfl

/-- Optional drawing data is unchanged; in particular `none` stays `none`. -/
@[simp] theorem attachElectronic_diagram? (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).diagram? = state.diagram? := rfl

/-- Optional sparse drawing positions are unchanged; absent coordinates stay absent. -/
@[simp] theorem attachElectronic_diagramPartial? (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).diagramPartial? = state.diagramPartial? := rfl

/-- The raw drawing incidence ledger is unchanged. -/
@[simp] theorem attachElectronic_diagramIncidence (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).diagramIncidence = state.diagramIncidence := rfl

/-- The fragment annotation channel is unchanged, including order and multiplicity. -/
@[simp] theorem attachElectronic_fragments (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).fragments = state.fragments := rfl

/-- The drawing-convention channel is unchanged. -/
@[simp] theorem attachElectronic_conventions (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).conventions = state.conventions := rfl

/-- The numbered cage/face annotation channel is unchanged. -/
@[simp] theorem attachElectronic_cages (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).cages = state.cages := rfl

/-- Optional residue-link and naming-hierarchy data is unchanged; `none` stays `none`. -/
@[simp] theorem attachElectronic_residueLedger? (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).residueLedger? = state.residueLedger? := rfl

/-- Bundled form: attachment preserves every other data channel literally.  Arbitrary paths,
arbitrary bands, roles, the shared conformation and every annotation channel are untouched. -/
theorem attachElectronic_preserves (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).graph = state.graph ∧
      (attachElectronic state source assignment).conformation = state.conformation ∧
      (attachElectronic state source assignment).rationalPositions? =
        state.rationalPositions? ∧
      (attachElectronic state source assignment).roles = state.roles ∧
      (attachElectronic state source assignment).paths = state.paths ∧
      (attachElectronic state source assignment).bandFamily = state.bandFamily ∧
      (attachElectronic state source assignment).diagram? = state.diagram? ∧
      (attachElectronic state source assignment).diagramPartial? = state.diagramPartial? ∧
      (attachElectronic state source assignment).diagramIncidence = state.diagramIncidence ∧
      (attachElectronic state source assignment).fragments = state.fragments ∧
      (attachElectronic state source assignment).conventions = state.conventions ∧
      (attachElectronic state source assignment).cages = state.cages ∧
      (attachElectronic state source assignment).residueLedger? = state.residueLedger? :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Attachment applies uniformly to states with arbitrary nonempty path and band index types: the
path at every edge and the band family at every band index are literally the original ones.  Hence
a path-description ingress state and an arbitrary band-carrying state are both covered by this one
generic operation, with no case split and no shared-state flattening. -/
theorem attachElectronic_paths_and_bands (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (edge : E) (band : B) :
    (attachElectronic state source assignment).paths edge = state.paths edge ∧
      (attachElectronic state source assignment).bandFamily band = state.bandFamily band :=
  ⟨rfl, rfl⟩

/-- Explicit absence is preserved on every optional data channel: if the original state has no
optional positions, drawing data, sparse positions or residue ledger, neither does the attached
state. -/
theorem attachElectronic_preserves_optional_absence (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (rational : state.rationalPositions? = none)
    (diagram : state.diagram? = none)
    (diagramPartial : state.diagramPartial? = none)
    (residueLedger : state.residueLedger? = none) :
    (attachElectronic state source assignment).rationalPositions? = none ∧
      (attachElectronic state source assignment).diagram? = none ∧
      (attachElectronic state source assignment).diagramPartial? = none ∧
      (attachElectronic state source assignment).residueLedger? = none := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [attachElectronic_rationalPositions?, rational]
  · rw [attachElectronic_diagram?, diagram]
  · rw [attachElectronic_diagramPartial?, diagramPartial]
  · rw [attachElectronic_residueLedger?, residueLedger]

/-! ## The stored channel is the actual ingress of the supplied data -/

/-- The stored channel's evidence at one owner and kind is the canonical `List.ofFn` enumeration of
the supplied assignment over the actual `Fin` slots.  No slot is invented or dropped. -/
theorem attachElectronic_evidence_eq_ofFn (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind) :
    (ingressChannel source assignment).evidence owner kind =
      List.ofFn fun slot : Fin ((source.siteCounts.counts owner).count kind) =>
        assignment.valueAt ⟨owner, kind, slot⟩ := rfl

/-- The stored evidence list at every owner and kind has exactly the supplied multiplicity. -/
theorem attachElectronic_evidence_length (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind) :
    ((ingressChannel source assignment).evidence owner kind).length =
      (source.siteCounts.counts owner).count kind :=
  ingressEvidence_length source assignment owner kind

/-- Reading the stored evidence at any actual slot returns exactly the supplied evidence there;
the dependent slot bound is handled by the existing ingress lemma. -/
theorem attachElectronic_evidence_get (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind)
    (slot : Fin ((source.siteCounts.counts owner).count kind))
    (bound : slot.val < ((ingressChannel source assignment).evidence owner kind).length) :
    ((ingressChannel source assignment).evidence owner kind).get ⟨slot.val, bound⟩ =
      assignment.valueAt ⟨owner, kind, slot⟩ :=
  ingressEvidence_get source assignment owner kind slot bound

/-! ## The whole-state unpaired tie is derived from the source -/

/-- The unpaired tie stored in the attached state at the supplied channel is exactly the supplied
source's own tie.  It is not assumed separately: this is the state's actual field, and it reduces
to `source.unpaired_tied`. -/
theorem attachElectronic_electronic_unpaired (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) :
    ((ingressChannel source assignment).counts.counts owner).unpairedElectronPositions =
      (state.graph.atomData owner).unpairedElectrons := by
  simpa using
    (attachElectronic state source assignment).electronic_unpaired
      (ingressChannel source assignment) rfl owner

/-- The attached state's tie is literally the supplied source's tie. -/
theorem attachElectronic_unpaired_eq_source (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) :
    ((ingressChannel source assignment).counts.counts owner).unpairedElectronPositions =
      (state.graph.atomData owner).unpairedElectrons :=
  source.unpaired_tied owner

/-! ## Recovery of the supplied source -/

/-- The existing `toIndependentElectronicSiteSource` projection of the attached state at the
supplied channel returns the originally supplied independent source exactly, including its counts
and its own unpaired tie. -/
theorem attachElectronic_toIndependentElectronicSiteSource (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    toIndependentElectronicSiteSource (attachElectronic state source assignment)
      (ingressChannel source assignment) rfl = source := by
  apply IndependentElectronicSiteSource.ext
  rfl

/-- The recovered source's counts are exactly the supplied counts. -/
theorem attachElectronic_siteCounts (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (toIndependentElectronicSiteSource (attachElectronic state source assignment)
      (ingressChannel source assignment) rfl).siteCounts = source.siteCounts := by
  rw [attachElectronic_toIndependentElectronicSiteSource]

/-- At every owner and kind, the recovered inventory's multiplicity is the supplied multiplicity. -/
theorem attachElectronic_counts_apply (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind) :
    (((toIndependentElectronicSiteSource (attachElectronic state source assignment)
        (ingressChannel source assignment) rfl).siteCounts.counts owner).count kind) =
      (source.siteCounts.counts owner).count kind := by
  rw [attachElectronic_toIndependentElectronicSiteSource]

/-! ## Recovery of the complete supplied assignment -/

/-- The existing `electronicAssignment` projection of the attached state at the supplied channel
returns the originally supplied evidence assignment **exactly**.  The dependent slot equalities are
discharged by `ingressEvidence_get`; no evidence value is altered and no slot is added or removed. -/
theorem attachElectronic_electronicAssignment (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    electronicAssignment (attachElectronic state source assignment)
      (ingressChannel source assignment) rfl = assignment := by
  apply IndependentSiteAssignment.ext
  intro identity
  exact ingressEvidence_get source assignment identity.owner identity.kind identity.slot _

/-- Every counted identity recovers the supplied evidence at that identity — hence every owner,
kind and slot is preserved, not merely the aggregate list. -/
theorem attachElectronic_electronicAssignment_valueAt (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (identity : IndependentSiteIdentity source.siteCounts) :
    (electronicAssignment (attachElectronic state source assignment)
      (ingressChannel source assignment) rfl).valueAt identity =
      assignment.valueAt identity := by
  rw [attachElectronic_electronicAssignment]

/-- Explicit owner/kind/slot form of complete-assignment recovery. -/
theorem attachElectronic_electronicAssignment_slot (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (owner : V) (kind : SiteKind)
    (slot : Fin ((source.siteCounts.counts owner).count kind)) :
    (electronicAssignment (attachElectronic state source assignment)
      (ingressChannel source assignment) rfl).valueAt ⟨owner, kind, slot⟩ =
      assignment.valueAt ⟨owner, kind, slot⟩ := by
  rw [attachElectronic_electronicAssignment]

/-- The recovered assignment remains injective in the supplied assignment: two distinct evidence
assignments attached to one state and source are distinct. -/
theorem attachElectronic_assignment_injective (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph) :
    Function.Injective fun assignment :
        IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence =>
      attachElectronic state source assignment := by
  intro first second equal
  have someEq : some (ingressChannel source first) = some (ingressChannel source second) := by
    simpa [attachElectronic] using
      congrArg (fun attached : WholeState V E B => attached.electronic?) equal
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

/-! ## Every one of the four evidence cases is preserved -/

/-- The evidence actually stored at every counted site is one of the four states of
`ReferenceGeometryEvidence`: absent, point only, direction only, or both.  The cases are inherited
from the supplied assignment, so attachment never collapses an incomplete geometry into a complete
one and never confuses absence with an explicit zero. -/
theorem attachElectronic_evidence_cases (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (identity : IndependentSiteIdentity source.siteCounts) :
    (electronicAssignment (attachElectronic state source assignment)
        (ingressChannel source assignment) rfl).valueAt identity = unspecified ∨
      (∃ point,
        (electronicAssignment (attachElectronic state source assignment)
          (ingressChannel source assignment) rfl).valueAt identity = pointOnly point) ∨
      (∃ direction,
        (electronicAssignment (attachElectronic state source assignment)
          (ingressChannel source assignment) rfl).valueAt identity = directionOnly direction) ∨
      (∃ point direction,
        (electronicAssignment (attachElectronic state source assignment)
            (ingressChannel source assignment) rfl).valueAt identity =
          pointAndDirection point direction) := by
  rw [attachElectronic_electronicAssignment]
  exact evidence_cases (assignment.valueAt identity)

/-! ## A present inventory, including an all-zero one, is distinct from absence

`electronic? = none` records that no inventory was supplied.  Attaching always stores `some`, even
when every supplied count is zero, so a present (possibly empty) inventory is never identified with
the absent inventory.  The original state's `none` is left intact on `state` itself; the attachment
does not claim to reconstruct it from the attached record. -/

/-- The attached state always has a present electronic channel. -/
theorem attachElectronic_electronic?_ne_none (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).electronic? ≠ none := by
  rw [attachElectronic_electronic?]
  simp

/-- If the original state had no inventory, the attached state's present channel — of whatever
multiplicities, including all zero — is distinct from that absence. -/
theorem attachElectronic_electronic?_ne_absent (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (absent : state.electronic? = none) :
    (attachElectronic state source assignment).electronic? ≠ state.electronic? := by
  rw [absent, attachElectronic_electronic?]
  simp

/-- In particular, attaching a present inventory to a state whose inventory was absent yields a
different whole state.  This is not a round-trip claim: the previous absent inventory is not
recovered from the attached record; it simply remains absent on the original `state`. -/
theorem attachElectronic_ne_of_electronic?_eq_none (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (absent : state.electronic? = none) :
    attachElectronic state source assignment ≠ state := by
  intro equal
  have presentEq :
      (attachElectronic state source assignment).electronic? = state.electronic? :=
    congrArg (fun attached : WholeState V E B => attached.electronic?) equal
  exact attachElectronic_electronic?_ne_absent state source assignment absent presentEq

/-- The only electronic data claimed by attachment is the supplied channel: the previous inventory
is replaced, never said to be recovered. -/
theorem attachElectronic_replaces_inventory (state : WholeState V E B)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (attachElectronic state source assignment).electronic? =
      some (ingressChannel source assignment) := rfl

end OrganicStereoElectronicStateAttachment

end TetraStereo.OneCenter
