import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription

set_option autoImplicit false

namespace TetraStereo.OneCenter

open OrganicStereoIndependentElectronicEncoding
open PhysicalPlaneEvidence
open PhysicalPlaneEvidence.ReferencePlane
open BlueBookP94
open BlueBookP93.Cyclic
















































/-! ## The ordered case bundle -/

/-- Independently supplied case records for one physical substrate.  Every field is a genuine
ordered list, so duplicates, repeated atoms and empty lists are meaningful and retained verbatim.
The four lists are exactly the existing Domain case channels; no new payload type is introduced. -/
structure CaseBundle (V : Type*) where
  /-- Ordered caller-supplied frame-reference annotations. -/
  frames : List (FrameAnnotation V) := []
  /-- Ordered residue/fragment metadata. -/
  fragments : List (FragmentAnnotation V) := []
  /-- Ordered drawing-convention channel. -/
  conventions : ConventionChannel V := []
  /-- Ordered numbered cage/face metadata. -/
  cages : List (NumberedCageAnnotation V) := []

namespace CaseBundle

/-- The empty bundle.  It is a genuine empty record, not an absent one. -/
def empty {V : Type*} : CaseBundle V where
  frames := []
  fragments := []
  conventions := []
  cages := []

/-- Extensionality for bundles, field by field. -/
theorem extEq {V : Type*} {first second : CaseBundle V}
    (frames : first.frames = second.frames)
    (fragments : first.fragments = second.fragments)
    (conventions : first.conventions = second.conventions)
    (cages : first.cages = second.cages) : first = second := by
  obtain ⟨firstFrames, firstFragments, firstConventions, firstCages⟩ := first
  obtain ⟨secondFrames, secondFragments, secondConventions, secondCages⟩ := second
  dsimp only at frames fragments conventions cages
  subst frames
  subst fragments
  subst conventions
  subst cages
  rfl

/-- Transport every case record by one common atom equivalence.  List order and multiplicity are
retained; frames use the green `relabelFrameAnnotation`, fragments the existing `relabel`,
conventions the ordered list encoder and cages the ordered list relabeller. -/
def relabel {V W : Type*} (e : V ≃ W) (bundle : CaseBundle V) : CaseBundle W where
  frames := bundle.frames.map (relabelFrameAnnotation e)
  fragments := bundle.fragments.map (fun annotation => annotation.relabel e)
  conventions := ConventionChannel.encode e bundle.conventions
  cages := NumberedCageAnnotation.relabelList e bundle.cages

@[simp] theorem relabel_frames {V W : Type*} (e : V ≃ W) (bundle : CaseBundle V) :
    (bundle.relabel e).frames = bundle.frames.map (relabelFrameAnnotation e) := rfl

@[simp] theorem relabel_fragments {V W : Type*} (e : V ≃ W) (bundle : CaseBundle V) :
    (bundle.relabel e).fragments =
      bundle.fragments.map (fun annotation => annotation.relabel e) := rfl

@[simp] theorem relabel_conventions {V W : Type*} (e : V ≃ W) (bundle : CaseBundle V) :
    (bundle.relabel e).conventions = ConventionChannel.encode e bundle.conventions := rfl

@[simp] theorem relabel_cages {V W : Type*} (e : V ≃ W) (bundle : CaseBundle V) :
    (bundle.relabel e).cages = NumberedCageAnnotation.relabelList e bundle.cages := rfl

/-- Relabelling a bundle and then relabelling back by the inverse equivalence is the identity on
every one of the four ordered channels. -/
theorem relabel_symm {V W : Type*} (e : V ≃ W) (bundle : CaseBundle V) :
    (bundle.relabel e).relabel e.symm = bundle := by
  apply CaseBundle.extEq
  · simp only [CaseBundle.relabel, List.map_map]
    have composition :
        (relabelFrameAnnotation (V := W) (W := V) e.symm) ∘
            (relabelFrameAnnotation (V := V) (W := W) e) = id := by
      funext annotation
      exact relabelFrameAnnotation_symm e annotation
    rw [composition, List.map_id]
  · simp only [CaseBundle.relabel, List.map_map]
    have composition :
        (FragmentAnnotation.relabel e.symm ∘ FragmentAnnotation.relabel e) = id := by
      funext annotation
      exact FragmentAnnotation.relabel_relabel_symm e annotation
    rw [composition, List.map_id]
  · simp only [CaseBundle.relabel, ConventionChannel.encode, List.map_map]
    have composition :
        (OrganicConventionSource.encode e.symm ∘ OrganicConventionSource.encode e) = id := by
      funext source
      exact OrganicConventionSource.decode_encode e source
    rw [composition, List.map_id]
  · simp only [CaseBundle.relabel]
    exact NumberedCageAnnotation.relabelList_symm_relabel e bundle.cages

/-- The bundle projection of a whole state.  This is the inverse map used by the later request
recovery; it reads only assembled fields and never an original request. -/
def extractCases {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (state : WholeState V E B) : CaseBundle V where
  frames := state.frames
  fragments := state.fragments
  conventions := state.conventions
  cages := state.cages

@[simp] theorem extractCases_frames {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (state : WholeState V E B) :
    (extractCases state).frames = state.frames := rfl

@[simp] theorem extractCases_fragments {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (state : WholeState V E B) :
    (extractCases state).fragments = state.fragments := rfl

@[simp] theorem extractCases_conventions {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (state : WholeState V E B) :
    (extractCases state).conventions = state.conventions := rfl

@[simp] theorem extractCases_cages {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (state : WholeState V E B) :
    (extractCases state).cages = state.cages := rfl

end CaseBundle

/-! ## Overwrite attachment and explicit-preservation attachment -/

variable {V W : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
variable {E E' B B' : Type*} [Fintype E] [Fintype E'] [Fintype B] [Fintype B']

/-- Attach an arbitrary ordered bundle to a physical state by overwriting the four case channels.
Every physical field is untouched.  Because the overwrite is total, recovering a *prior* nonempty
case list is not possible from the assembled state; use `CaseChannelsEmpty` (below) or
`appendCases` when the prior lists must be retained. -/
def attachCases (state : WholeState V E B) (bundle : CaseBundle V) : WholeState V E B :=
  { state with
    frames := bundle.frames
    fragments := bundle.fragments
    conventions := bundle.conventions
    cages := bundle.cages }

/-- Attach a bundle while explicitly preserving the prior case lists: each supplied list is
appended as the suffix of the corresponding existing channel.  Nothing is overwritten. -/
def appendCases (state : WholeState V E B) (bundle : CaseBundle V) : WholeState V E B :=
  { state with
    frames := state.frames ++ bundle.frames
    fragments := state.fragments ++ bundle.fragments
    conventions := state.conventions ++ bundle.conventions
    cages := state.cages ++ bundle.cages }

/-- Clear the four case channels while leaving every physical field intact. -/
def clearCases (state : WholeState V E B) : WholeState V E B :=
  { state with
    frames := []
    fragments := []
    conventions := []
    cages := [] }

/-- The explicit no-overwrite condition: a genuine physical ingress substrate supplies no case
metadata at all.  Under this condition `clearCases` is the exact inverse of `attachCases`. -/
structure CaseChannelsEmpty (state : WholeState V E B) : Prop where
  frames : state.frames = []
  fragments : state.fragments = []
  conventions : state.conventions = []
  cages : state.cages = []

/-! ### Exact recovery of the attached lists -/

@[simp] theorem attachCases_frames (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).frames = bundle.frames := rfl

@[simp] theorem attachCases_fragments (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).fragments = bundle.fragments := rfl

@[simp] theorem attachCases_conventions (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).conventions = bundle.conventions := rfl

@[simp] theorem attachCases_cages (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).cages = bundle.cages := rfl

/-- Every attached frame occurs at exactly the same position as in the supplied ordered list. -/
@[simp] theorem attachCases_frames_getElem? (state : WholeState V E B) (bundle : CaseBundle V)
    (index : ℕ) :
    (attachCases state bundle).frames[index]? = bundle.frames[index]? := rfl

/-- The fragment channel is recovered position by position. -/
@[simp] theorem attachCases_fragments_getElem? (state : WholeState V E B) (bundle : CaseBundle V)
    (index : ℕ) :
    (attachCases state bundle).fragments[index]? = bundle.fragments[index]? := rfl

/-- The convention channel is recovered position by position. -/
@[simp] theorem attachCases_conventions_getElem? (state : WholeState V E B) (bundle : CaseBundle V)
    (index : ℕ) :
    (attachCases state bundle).conventions[index]? = bundle.conventions[index]? := rfl

/-- The cage channel is recovered position by position. -/
@[simp] theorem attachCases_cages_getElem? (state : WholeState V E B) (bundle : CaseBundle V)
    (index : ℕ) :
    (attachCases state bundle).cages[index]? = bundle.cages[index]? := rfl

/-- `extractCases` inverts `attachCases` exactly: the assembled state's own fields recover the
supplied whole ordered bundle, including duplicates and list order. -/
@[simp] theorem extractCases_attachCases (state : WholeState V E B) (bundle : CaseBundle V) :
    CaseBundle.extractCases (attachCases state bundle) = bundle := by
  apply CaseBundle.extEq <;> simp [CaseBundle.extractCases, attachCases]

/-- `attachCases` is idempotent on the extracted bundle of a state. -/
@[simp] theorem attachCases_extractCases (state : WholeState V E B) :
    attachCases state (CaseBundle.extractCases state) = state := by
  apply WholeState.extEq <;> simp [attachCases, CaseBundle.extractCases]

/-- Attaching the empty bundle overwrites the case channels with genuine empty lists; it is the
same as clearing them. -/
@[simp] theorem attachCases_empty (state : WholeState V E B) :
    attachCases state CaseBundle.empty = clearCases state := by
  apply WholeState.extEq <;> simp [attachCases, clearCases, CaseBundle.empty]

/-! ### No physical field changes -/

@[simp] theorem attachCases_graph (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).graph = state.graph := rfl

@[simp] theorem attachCases_electronic? (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).electronic? = state.electronic? := rfl

@[simp] theorem attachCases_conformation (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).conformation = state.conformation := rfl

@[simp] theorem attachCases_rationalPositions? (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).rationalPositions? = state.rationalPositions? := rfl

@[simp] theorem attachCases_roles (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).roles = state.roles := rfl

@[simp] theorem attachCases_paths (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).paths = state.paths := rfl

@[simp] theorem attachCases_bandFamily (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).bandFamily = state.bandFamily := rfl

@[simp] theorem attachCases_diagram? (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).diagram? = state.diagram? := rfl

@[simp] theorem attachCases_diagramPartial? (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).diagramPartial? = state.diagramPartial? := rfl

@[simp] theorem attachCases_diagramIncidence (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).diagramIncidence = state.diagramIncidence := rfl

@[simp] theorem attachCases_residueLedger? (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).residueLedger? = state.residueLedger? := rfl

/-- Bundled statement of the physical-field invariance: attaching a case bundle changes none of
the graph, electronic, conformation, rational-provenance, role, path, band, drawing or
residue-ledger channels. -/
theorem attachCases_physical_fields (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).graph = state.graph ∧
      (attachCases state bundle).electronic? = state.electronic? ∧
      (attachCases state bundle).conformation = state.conformation ∧
      (attachCases state bundle).rationalPositions? = state.rationalPositions? ∧
      (attachCases state bundle).roles = state.roles ∧
      (attachCases state bundle).paths = state.paths ∧
      (attachCases state bundle).bandFamily = state.bandFamily ∧
      (attachCases state bundle).diagram? = state.diagram? ∧
      (attachCases state bundle).diagramPartial? = state.diagramPartial? ∧
      (attachCases state bundle).diagramIncidence = state.diagramIncidence ∧
      (attachCases state bundle).residueLedger? = state.residueLedger? :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Explicit prior-list preservation by appending -/

@[simp] theorem appendCases_frames (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).frames = state.frames ++ bundle.frames := rfl

@[simp] theorem appendCases_fragments (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).fragments = state.fragments ++ bundle.fragments := rfl

@[simp] theorem appendCases_conventions (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).conventions = state.conventions ++ bundle.conventions := rfl

@[simp] theorem appendCases_cages (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).cages = state.cages ++ bundle.cages := rfl

/-- The prior frame list is exactly the prefix of the appended channel. -/
@[simp] theorem appendCases_frames_take (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).frames.take state.frames.length = state.frames := by
  simp [appendCases]

/-- The newly supplied frame list is exactly the suffix of the appended channel. -/
@[simp] theorem appendCases_frames_drop (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).frames.drop state.frames.length = bundle.frames := by
  simp [appendCases]

/-- Every prior frame occurs at its original position. -/
theorem appendCases_frames_getElem?_prefix (state : WholeState V E B) (bundle : CaseBundle V)
    (index : ℕ) (bound : index < state.frames.length) :
    (appendCases state bundle).frames[index]? = state.frames[index]? := by
  rw [appendCases_frames, List.getElem?_append_left bound]

/-- Every newly supplied frame occurs at the original length plus its supplied position. -/
theorem appendCases_frames_getElem?_suffix (state : WholeState V E B) (bundle : CaseBundle V)
    (index : ℕ) :
    (appendCases state bundle).frames[state.frames.length + index]? = bundle.frames[index]? := by
  rw [appendCases_frames, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

/-- Appending an empty bundle changes nothing. -/
@[simp] theorem appendCases_empty (state : WholeState V E B) :
    appendCases state CaseBundle.empty = state := by
  apply WholeState.extEq <;> simp [appendCases, CaseBundle.empty]

/-- The four-channels split theorem: both the prior and supplied lists are retained exactly. -/
theorem appendCases_case_lists_split (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).frames.take state.frames.length = state.frames ∧
      (appendCases state bundle).frames.drop state.frames.length = bundle.frames ∧
      (appendCases state bundle).fragments.take state.fragments.length = state.fragments ∧
      (appendCases state bundle).fragments.drop state.fragments.length = bundle.fragments ∧
      (appendCases state bundle).conventions.take state.conventions.length = state.conventions ∧
      (appendCases state bundle).conventions.drop state.conventions.length = bundle.conventions ∧
      (appendCases state bundle).cages.take state.cages.length = state.cages ∧
      (appendCases state bundle).cages.drop state.cages.length = bundle.cages := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [appendCases]

@[simp] theorem appendCases_graph (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).graph = state.graph := rfl

@[simp] theorem appendCases_electronic? (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).electronic? = state.electronic? := rfl

@[simp] theorem appendCases_conformation (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).conformation = state.conformation := rfl

@[simp] theorem appendCases_roles (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).roles = state.roles := rfl

@[simp] theorem appendCases_paths (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).paths = state.paths := rfl

@[simp] theorem appendCases_bandFamily (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).bandFamily = state.bandFamily := rfl

@[simp] theorem appendCases_diagram? (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).diagram? = state.diagram? := rfl

@[simp] theorem appendCases_diagramPartial? (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).diagramPartial? = state.diagramPartial? := rfl

@[simp] theorem appendCases_diagramIncidence (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).diagramIncidence = state.diagramIncidence := rfl

@[simp] theorem appendCases_residueLedger? (state : WholeState V E B) (bundle : CaseBundle V) :
    (appendCases state bundle).residueLedger? = state.residueLedger? := rfl

/-! ### Clearing and the no-overwrite inverse -/

@[simp] theorem clearCases_frames (state : WholeState V E B) :
    (clearCases state).frames = [] := rfl

@[simp] theorem clearCases_fragments (state : WholeState V E B) :
    (clearCases state).fragments = [] := rfl

@[simp] theorem clearCases_conventions (state : WholeState V E B) :
    (clearCases state).conventions = [] := rfl

@[simp] theorem clearCases_cages (state : WholeState V E B) :
    (clearCases state).cages = [] := rfl

@[simp] theorem clearCases_graph (state : WholeState V E B) :
    (clearCases state).graph = state.graph := rfl

@[simp] theorem clearCases_electronic? (state : WholeState V E B) :
    (clearCases state).electronic? = state.electronic? := rfl

@[simp] theorem clearCases_conformation (state : WholeState V E B) :
    (clearCases state).conformation = state.conformation := rfl

@[simp] theorem clearCases_residueLedger? (state : WholeState V E B) :
    (clearCases state).residueLedger? = state.residueLedger? := rfl

/-- Clearing after attachment forgets only the four case channels; every physical field is the
same as in the base state. -/
@[simp] theorem clearCases_attachCases (state : WholeState V E B) (bundle : CaseBundle V) :
    clearCases (attachCases state bundle) = clearCases state := by
  apply WholeState.extEq <;> simp [clearCases, attachCases]

/-- Under the genuine-ingress condition the cleared state is the base state itself. -/
theorem clearCases_eq_self_of_empty {state : WholeState V E B}
    (empty : CaseChannelsEmpty state) : clearCases state = state := by
  rcases empty with ⟨frames, fragments, conventions, cages⟩
  apply WholeState.extEq <;> simp [clearCases, frames, fragments, conventions, cages]

/-- Attachment parameterised by the explicit no-overwrite certificate.  The certificate is a
genuine hypothesis about the base case channels, not a default. -/
def attachCasesOverEmpty (base : WholeState V E B) (bundle : CaseBundle V)
    (_empty : CaseChannelsEmpty base) : WholeState V E B :=
  attachCases base bundle

@[simp] theorem attachCasesOverEmpty_def (base : WholeState V E B) (bundle : CaseBundle V)
    (empty : CaseChannelsEmpty base) :
    attachCasesOverEmpty base bundle empty = attachCases base bundle := rfl

/-- With the no-overwrite certificate, clearing the assembled state recovers the base state
exactly.  This is the precise sense in which the whole `(base, bundle)` request is not lost. -/
theorem clearCases_attachCasesOverEmpty (base : WholeState V E B) (bundle : CaseBundle V)
    (empty : CaseChannelsEmpty base) :
    clearCases (attachCasesOverEmpty base bundle empty) = base := by
  rw [attachCasesOverEmpty_def, clearCases_attachCases, clearCases_eq_self_of_empty empty]

/-! ## Common-enumeration and encoding compatibility -/

/-- Attaching then relabelling is relabelling then attaching the elementwise-relabelled bundle. -/
@[simp] theorem relabelWholeState_attachCases (e : V ≃ W) (state : WholeState V E B)
    (bundle : CaseBundle V) :
    relabelWholeState e (attachCases state bundle) =
      attachCases (relabelWholeState e state) (bundle.relabel e) := by
  apply WholeState.extEq <;> simp [attachCases, CaseBundle.relabel, relabelWholeState]

/-- Appending then relabelling is relabelling then appending the elementwise-relabelled bundle. -/
@[simp] theorem relabelWholeState_appendCases (e : V ≃ W) (state : WholeState V E B)
    (bundle : CaseBundle V) :
    relabelWholeState e (appendCases state bundle) =
      appendCases (relabelWholeState e state) (bundle.relabel e) := by
  apply WholeState.extEq <;>
    simp [appendCases, CaseBundle.relabel, relabelWholeState,
      ConventionChannel.encode, NumberedCageAnnotation.relabelList]

/-- Encoding a description assembled from cases is exactly assembling the encoded description with
the bundle relabelled by the same atom enumeration.  No original request is retained. -/
@[simp] theorem encodeDescription_attachCases
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    encodeDescription eV eE eB (attachCases state bundle) =
      attachCases (encodeDescription eV eE eB state) (bundle.relabel eV) := by
  apply WholeState.extEq <;>
    simp [attachCases, CaseBundle.relabel, encodeDescription, relabelDescription,
      reindexEdges, reindexBands, relabelWholeState]

/-- The encoded frame channel is exactly the supplied ordered frame list, atom-references mapped
by the common enumeration. -/
@[simp] theorem encodeDescription_attachCases_frames
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    (encodeDescription eV eE eB (attachCases state bundle)).frames =
      bundle.frames.map (relabelFrameAnnotation eV) := by
  rw [encodeDescription_attachCases]
  rfl

/-- The encoded fragment channel is exactly the supplied ordered fragment list. -/
@[simp] theorem encodeDescription_attachCases_fragments
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    (encodeDescription eV eE eB (attachCases state bundle)).fragments =
      bundle.fragments.map (fun annotation => annotation.relabel eV) := by
  rw [encodeDescription_attachCases]
  rfl

/-- The encoded convention channel is exactly the supplied ordered convention list. -/
@[simp] theorem encodeDescription_attachCases_conventions
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    (encodeDescription eV eE eB (attachCases state bundle)).conventions =
      ConventionChannel.encode eV bundle.conventions := by
  rw [encodeDescription_attachCases]
  rfl

/-- The encoded cage channel is exactly the supplied ordered cage list. -/
@[simp] theorem encodeDescription_attachCases_cages
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    (encodeDescription eV eE eB (attachCases state bundle)).cages =
      NumberedCageAnnotation.relabelList eV bundle.cages := by
  rw [encodeDescription_attachCases]
  rfl

/-- The ordered atom references of the attached frame channel commute with the common encoding
enumeration.  This is the exact enumeration compatibility of the attached ordered occurrence list. -/
theorem encodeDescription_attachCases_frames_atomRefs
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    (encodeDescription eV eE eB (attachCases state bundle)).frames.map
        FrameAnnotation.atomRefs =
      (bundle.frames.map FrameAnnotation.atomRefs).map (List.map eV) := by
  rw [encodeDescription_attachCases_frames]
  simp [List.map_map, Function.comp_def]

/-- Decoding the same-schema encoding of an assembled description recovers the assembled
description itself; only encoded fields and the three equivalences are used. -/
theorem decodeDescription_encodeDescription_attachCases
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    decodeDescription eV eE eB (encodeDescription eV eE eB (attachCases state bundle)) =
      attachCases state bundle :=
  decodeDescription_encodeDescription eV eE eB (attachCases state bundle)

/-- Decoding the encoded assembled description returns exactly the supplied frame list. -/
theorem decodeDescription_encodeDescription_attachCases_frames
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (bundle : CaseBundle V) :
    (decodeDescription eV eE eB
      (encodeDescription eV eE eB (attachCases state bundle))).frames = bundle.frames := by
  rw [decodeDescription_encodeDescription_attachCases, attachCases_frames]

/-! ## Whole requests and the exact inverse set

A *whole request* is a base physical state together with the entire case bundle.  The assembled
state does not store the request.  The compatible requests are recovered as whole requests through
the actual maps `clearCases` and `extractCases`; the characterisation below is an equality of
requests, not a pair of independent marginal projections. -/

/-- A whole request: one physical base and one complete ordered case bundle. -/
structure CaseRequest (V E B : Type*) [DecidableEq V] [Fintype V] [Fintype E] [Fintype B] where
  base : WholeState V E B
  bundle : CaseBundle V

/-- Assemble one whole request. -/
def assemble (request : CaseRequest V E B) : WholeState V E B :=
  attachCases request.base request.bundle

@[simp] theorem assemble_mk (base : WholeState V E B) (bundle : CaseBundle V) :
    assemble ⟨base, bundle⟩ = attachCases base bundle := rfl

/-- The canonical whole request decoded from an assembled state: the cleared physical base
together with the case bundle read from the assembled fields.  This is the actual inverse, not a
marginal choice. -/
def wholeRequestOfState (state : WholeState V E B) : CaseRequest V E B :=
  ⟨clearCases state, CaseBundle.extractCases state⟩

@[simp] theorem wholeRequestOfState_base (state : WholeState V E B) :
    (wholeRequestOfState state).base = clearCases state := rfl

@[simp] theorem wholeRequestOfState_bundle (state : WholeState V E B) :
    (wholeRequestOfState state).bundle = CaseBundle.extractCases state := rfl

/-- The canonical request assembles back to the state it was read from. -/
@[simp] theorem assemble_wholeRequestOfState (state : WholeState V E B) :
    assemble (wholeRequestOfState state) = state := by
  apply WholeState.extEq <;>
    simp [assemble, wholeRequestOfState, attachCases, clearCases, CaseBundle.extractCases]

/-- Requests compatible with an assembled state: the base case channels must be genuine empty
ingress channels, and the whole request must assemble to the state. -/
def compatibleRequests (state : WholeState V E B) : Set (CaseRequest V E B) :=
  { request | CaseChannelsEmpty request.base ∧ assemble request = state }

/-- The compatible set is exactly the singleton of the canonical whole request. -/
theorem mem_compatibleRequests_iff (state : WholeState V E B) (request : CaseRequest V E B) :
    request ∈ compatibleRequests state ↔ request = wholeRequestOfState state := by
  constructor
  · rintro ⟨empty, assembled⟩
    obtain ⟨base, bundle⟩ := request
    have assembledCases : attachCases base bundle = state := by
      simpa using assembled
    have baseEq : base = clearCases state := by
      calc
        base = clearCases base := (clearCases_eq_self_of_empty empty).symm
        _ = clearCases (attachCases base bundle) :=
          (clearCases_attachCases base bundle).symm
        _ = clearCases state := by rw [assembledCases]
    have bundleEq : bundle = CaseBundle.extractCases state := by
      calc
        bundle = CaseBundle.extractCases (attachCases base bundle) :=
          (extractCases_attachCases base bundle).symm
        _ = CaseBundle.extractCases state := by rw [assembledCases]
    simp [wholeRequestOfState, baseEq, bundleEq]
  · intro equality
    rw [equality]
    exact ⟨⟨rfl, rfl, rfl, rfl⟩, assemble_wholeRequestOfState state⟩

/-- Set-level statement: the full compatible-request set is one point, not a product of
independently chosen marginals. -/
theorem compatibleRequests_eq_singleton (state : WholeState V E B) :
    compatibleRequests state = {wholeRequestOfState state} := by
  ext request
  rw [mem_compatibleRequests_iff]
  simp

/-- Any compatible request has both of its components recovered exactly by the canonical inverse. -/
theorem compatibleRequest_components (state : WholeState V E B) (request : CaseRequest V E B)
    (member : request ∈ compatibleRequests state) :
    request.base = clearCases state ∧
      request.bundle = CaseBundle.extractCases state := by
  rw [mem_compatibleRequests_iff] at member
  rw [member]
  exact ⟨rfl, rfl⟩

/-- Recovering a base state directly from `attachCases` requires the explicit no-overwrite
certificate: the assembled state's case channels are the bundle, so the genuine base is recovered
by clearing and using emptiness of the original lists. -/
theorem wholeRequest_base_of_attachCases (base : WholeState V E B) (bundle : CaseBundle V)
    (empty : CaseChannelsEmpty base) :
    (wholeRequestOfState (attachCases base bundle)).base = base := by
  show clearCases (attachCases base bundle) = base
  rw [clearCases_attachCases, clearCases_eq_self_of_empty empty]

/-- The bundle is recovered from the assembled fields without any emptiness hypothesis. -/
@[simp] theorem wholeRequest_bundle_of_attachCases (base : WholeState V E B)
    (bundle : CaseBundle V) :
    (wholeRequestOfState (attachCases base bundle)).bundle = bundle := by
  show CaseBundle.extractCases (attachCases base bundle) = bundle
  rw [extractCases_attachCases]

/-! ## Metadata scope of the non-frame adapters

The fragment, convention and cage channels are retained as supplied metadata.  This module does
not interpret them against the graph, does not derive any source certificate from them, and does
not touch the optional residue ledger (whose link binding is the separate responsibility of
`OrganicStereoSourceBoundResidueAssembly`). -/

/-- The three non-frame adapters are literal metadata transports: the assembled lists are exactly
the supplied lists, with no inferred binding or descriptor. -/
theorem attachCases_metadata_scope (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).fragments = bundle.fragments ∧
      (attachCases state bundle).conventions = bundle.conventions ∧
      (attachCases state bundle).cages = bundle.cages :=
  ⟨rfl, rfl, rfl⟩

/-- Case attachment neither reads nor rewrites the residue ledger. -/
@[simp] theorem attachCases_residueLedger_invariant (state : WholeState V E B)
    (bundle : CaseBundle V) :
    (attachCases state bundle).residueLedger? = state.residueLedger? := rfl

/-- Case attachment cannot create graph interactions: the interaction list is a physical field. -/
@[simp] theorem attachCases_graph_interactions (state : WholeState V E B) (bundle : CaseBundle V) :
    (attachCases state bundle).graph.interactions = state.graph.interactions := rfl

/-! ## The physical ring-plane bridge

The bridge is indexed by an observation whose molecule is *literally* the state's encoded graph
`state.graph.encode enumeration`.  The equivalence to the encoded atom indices is the same
enumeration followed only by the proved cardinality identification, so no second enumeration and
no count-only tie is introduced. -/

/-- The atom equivalence induced by the state's common encoding enumeration.  It is the chosen
enumeration followed by the proved identification of `Fintype.card V` with the encoded atom count. -/
def stateObservationEquiv (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    V ≃ Fin (state.graph.encode enumeration).atomCount :=
  enumeration.trans
    (finCastEquiv
      (FiniteAtomInteractionHypergraph.encode_atomCount state.graph enumeration).symm)

@[simp] theorem stateObservationEquiv_apply (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) (atom : V) :
    stateObservationEquiv state enumeration atom =
      finCastEquiv
        (FiniteAtomInteractionHypergraph.encode_atomCount state.graph enumeration).symm
        (enumeration atom) := rfl

/-- Agreement of the observation's real conformation with the single whole-state conformation
through the common encoding equivalence.  Every geometry statement below is evaluated under this
hypothesis, so both sides use the *same* conformation. -/
def ConformationAgrees (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration)) : Prop :=
  ∀ index, observation.conformation index =
    state.conformation ((stateObservationEquiv state enumeration).symm index)

/-- Agreement read at a source atom: the encoded observation point at the enumeration image is
the state conformation point at that atom. -/
theorem conformationAgrees_apply (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration))
    (agrees : ConformationAgrees state enumeration observation) (atom : V) :
    observation.conformation (stateObservationEquiv state enumeration atom) =
      state.conformation atom := by
  rw [agrees (stateObservationEquiv state enumeration atom), Equiv.symm_apply_apply]

/-- Construct the green real-ring-plane frame from an actual observation over the state's own
encoded graph.  The original observation is an input only; the output annotation carries the
plane, ordered support and two substituent references, never the observation or the request. -/
def ringPlaneObservationFrame (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration)) :
    FrameAnnotation V :=
  physicalRingPlaneObservationToFrame (stateObservationEquiv state enumeration) observation

/-- The frame retains the supplied real reference plane literally. -/
@[simp] theorem ringPlaneObservationFrame_realPlane? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration)) :
    (ringPlaneObservationFrame state enumeration observation).realPlane? =
      some observation.plane := by
  simp [ringPlaneObservationFrame]

/-- The frame retains the ordered ring support, mapped from actual source indices by the same
encoding equivalence. -/
@[simp] theorem ringPlaneObservationFrame_ringAtoms? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration)) :
    (ringPlaneObservationFrame state enumeration observation).ringAtoms? =
      some (observation.ringAtoms.map (stateObservationEquiv state enumeration).symm) := by
  simp [ringPlaneObservationFrame]

/-- Exact field recovery: the constructed frame is the real-ring-plane constructor applied to
exactly the supplied plane, ordered support and two substituent atoms. -/
theorem ringPlaneObservationFrame_fields (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration)) :
    ∃ frame : RealRingPlaneFrame V,
      ringPlaneObservationFrame state enumeration observation = .realRingPlane frame ∧
        frame.plane = observation.plane ∧
        frame.ringAtoms =
          observation.ringAtoms.map (stateObservationEquiv state enumeration).symm ∧
        frame.firstSubstituent =
          (stateObservationEquiv state enumeration).symm observation.firstSubstituent ∧
        frame.secondSubstituent =
          (stateObservationEquiv state enumeration).symm observation.secondSubstituent :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- Mapping the frame's recovered ordered support back through the same equivalence returns the
original source-indexed support, in order and with multiplicity. -/
theorem ringPlaneObservationFrame_ringAtoms_map (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration)) :
    (observation.ringAtoms.map (stateObservationEquiv state enumeration).symm).map
        (stateObservationEquiv state enumeration) = observation.ringAtoms :=
  map_physicalRingPlaneObservation_ringAtoms (stateObservationEquiv state enumeration) observation

/-- Occurrence position of the recovered support: at every index the frame's support contains
exactly the image of the source observation's atom at that same index. -/
@[simp] theorem ringPlaneObservationFrame_ringAtoms_getElem? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration)) (index : ℕ) :
    (ringPlaneObservationFrame state enumeration observation).ringAtoms?.bind
        (fun atoms => atoms[index]?) =
      (observation.ringAtoms[index]?).map (stateObservationEquiv state enumeration).symm := by
  simp [ringPlaneObservationFrame]

/-- The first signed displacement, evaluated against the same whole-state conformation. -/
theorem firstSignedDisplacement_eq_state (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration))
    (agrees : ConformationAgrees state enumeration observation) :
    observation.firstSignedDisplacement =
      signedDisplacement observation.plane
        (state.conformation
          ((stateObservationEquiv state enumeration).symm observation.firstSubstituent)) := by
  show signedDisplacement observation.plane
      (observation.conformation observation.firstSubstituent) = _
  rw [agrees observation.firstSubstituent]

/-- The second signed displacement, evaluated against the same whole-state conformation. -/
theorem secondSignedDisplacement_eq_state (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration))
    (agrees : ConformationAgrees state enumeration observation) :
    observation.secondSignedDisplacement =
      signedDisplacement observation.plane
        (state.conformation
          ((stateObservationEquiv state enumeration).symm observation.secondSubstituent)) := by
  show signedDisplacement observation.plane
      (observation.conformation observation.secondSubstituent) = _
  rw [agrees observation.secondSubstituent]

/-- The first side observation, evaluated against the same whole-state conformation. -/
theorem firstSide_eq_state (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration))
    (agrees : ConformationAgrees state enumeration observation) :
    observation.firstSide =
      RingSide.ofSigned
        (signedDisplacement observation.plane
          (state.conformation
            ((stateObservationEquiv state enumeration).symm observation.firstSubstituent))) := by
  show RingSide.ofSigned observation.firstSignedDisplacement = _
  rw [firstSignedDisplacement_eq_state state enumeration observation agrees]

/-- The second side observation, evaluated against the same whole-state conformation. -/
theorem secondSide_eq_state (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration))
    (agrees : ConformationAgrees state enumeration observation) :
    observation.secondSide =
      RingSide.ofSigned
        (signedDisplacement observation.plane
          (state.conformation
            ((stateObservationEquiv state enumeration).symm observation.secondSubstituent))) := by
  show RingSide.ofSigned observation.secondSignedDisplacement = _
  rw [secondSignedDisplacement_eq_state state enumeration observation agrees]

/-- The relative cis/trans observation, evaluated against the same whole-state conformation.
Absence (`none`) is preserved: a zero displacement still yields no fabricated descriptor. -/
theorem relativeCisTrans_eq_state (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration))
    (agrees : ConformationAgrees state enumeration observation) :
    observation.relativeCisTrans =
      BlueBookP93.Cyclic.relativeCisTransOfSigned
        (signedDisplacement observation.plane
          (state.conformation
            ((stateObservationEquiv state enumeration).symm observation.firstSubstituent)))
        (signedDisplacement observation.plane
          (state.conformation
            ((stateObservationEquiv state enumeration).symm observation.secondSubstituent))) := by
  show BlueBookP93.Cyclic.relativeCisTransOfSigned
      observation.firstSignedDisplacement observation.secondSignedDisplacement = _
  rw [firstSignedDisplacement_eq_state state enumeration observation agrees,
    secondSignedDisplacement_eq_state state enumeration observation agrees]

/-- Supplied coplanarity evidence transports to the same whole-state conformation: every chosen
support atom has vanishing signed displacement at the state's own conformation.  The evidence is
used as supplied; coplanarity is never inferred from the frame metadata. -/
theorem coplanarRingEvidence_state_displacements_zero (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observation : PhysicalRingPlaneObservation (state.graph.encode enumeration))
    (agrees : ConformationAgrees state enumeration observation)
    (evidence : CoplanarRingEvidence observation) :
    ∀ index, index ∈ observation.ringAtoms →
      signedDisplacement observation.plane
        (state.conformation ((stateObservationEquiv state enumeration).symm index)) = 0 := by
  intro index member
  have zero :=
    (PhysicalRingPlaneObservation.ringSupportInPlane_iff_all_displacements_zero observation).mp
      evidence.inPlane index member
  rw [← agrees index]
  simpa [PhysicalRingPlaneObservation.signedDisplacementOf,
    PhysicalRingPlaneObservation.atomPosition] using zero

/-! ### Supplied closed-ring and attachment evidence

The generic physical observation records a chosen support, not a closed ring.  The closed-ring
carrier and the two attachments are separate supplied data.  In particular `ringPosition` and
`interaction` are data of the attachment records, while `SourceClosedRing.bond` is a propositional
existence statement with no chosen occurrence.  The raw `RealRingPlaneFrame` does not record the
attachment choices, so the theorems below retain those choices only in statements about the
original closed-ring record; they do not claim that the frame payload recovers them.
-/

/-- The closed ring's own ordered carrier is exactly the generic observation's support. -/
theorem closedRing_support_eq (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    closed.ring.ringAtoms = closed.observation.ringAtoms :=
  closed.ring_matches

/-- The constructed frame's ordered support, read through the closed-ring carrier. -/
theorem closedRing_frame_ringAtoms? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    (ringPlaneObservationFrame state enumeration closed.observation).ringAtoms? =
      some (closed.ring.ringAtoms.map (stateObservationEquiv state enumeration).symm) := by
  simp [ringPlaneObservationFrame_ringAtoms?, closed.ring_matches]

/-- The supplied closed ring has at least three distinct source atoms. -/
theorem closedRing_length_ge_three (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    3 ≤ closed.ring.ringAtoms.length :=
  closed.ring.length_ge_three

/-- The supplied closed ring has no repeated source atom. -/
theorem closedRing_nodup (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    closed.ring.ringAtoms.Nodup :=
  closed.ring.nodup

/-- Every cyclic consecutive source ring pair has an actual binary source ring-bond interaction in
the state's encoded graph.  The chosen ring carrier is the supplied one. -/
theorem closedRing_bond_exists (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration))
    (position : Fin closed.ring.ringAtoms.length) :
    ∃ interaction : SemanticInteraction,
      interaction ∈ (state.graph.encode enumeration).interactions ∧
        IsRingBond interaction.kind ∧
          HasBinaryParticipants (closed.ring.ringAtoms.get position).val
            (closed.ring.ringAtoms.get
              (PhysicalPlaneEvidence.cycleSucc closed.ring.length_positive position)).val
            interaction :=
  SourceClosedRing.bond_exists closed.ring position

/-- The first supplied attachment's chosen ring position belongs to the frame's recovered support. -/
theorem closedRing_firstAttachment_ringPosition_frame_mem (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    (stateObservationEquiv state enumeration).symm closed.firstAttachment.ringPosition ∈
      closed.ring.ringAtoms.map (stateObservationEquiv state enumeration).symm :=
  List.mem_map.mpr
    ⟨closed.firstAttachment.ringPosition, closed.firstAttachment.ringPosition_mem, rfl⟩

/-- The second supplied attachment's chosen ring position belongs to the frame's recovered
support. -/
theorem closedRing_secondAttachment_ringPosition_frame_mem (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    (stateObservationEquiv state enumeration).symm closed.secondAttachment.ringPosition ∈
      closed.ring.ringAtoms.map (stateObservationEquiv state enumeration).symm :=
  List.mem_map.mpr
    ⟨closed.secondAttachment.ringPosition, closed.secondAttachment.ringPosition_mem, rfl⟩

/-- The first attachment retains its actual source interaction: it is an interaction of the
state's own encoded graph, its kind is a ring bond, and its binary participant list contains the
chosen ring position and the first substituent. -/
theorem closedRing_firstAttachment_evidence (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    closed.firstAttachment.interaction ∈ (state.graph.encode enumeration).interactions ∧
      IsRingBond closed.firstAttachment.interaction.kind ∧
        HasBinaryParticipants closed.firstAttachment.ringPosition.val
          closed.observation.firstSubstituent.val closed.firstAttachment.interaction :=
  ⟨PhysicalClosedRingObservation.firstAttachment_interaction_mem closed,
    PhysicalClosedRingObservation.firstAttachment_interaction_isRingBond closed,
    PhysicalClosedRingObservation.firstAttachment_binaryParticipants closed⟩

/-- The second attachment retains its actual source interaction in the same sense. -/
theorem closedRing_secondAttachment_evidence (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    closed.secondAttachment.interaction ∈ (state.graph.encode enumeration).interactions ∧
      IsRingBond closed.secondAttachment.interaction.kind ∧
        HasBinaryParticipants closed.secondAttachment.ringPosition.val
          closed.observation.secondSubstituent.val closed.secondAttachment.interaction :=
  ⟨PhysicalClosedRingObservation.secondAttachment_interaction_mem closed,
    PhysicalClosedRingObservation.secondAttachment_interaction_isRingBond closed,
    PhysicalClosedRingObservation.secondAttachment_binaryParticipants closed⟩

/-- The first attachment's binary participant list, read at the frame's recovered substituent
atom: the source index is exactly the encoding image of that atom, so the source interaction and
the recovered annotation refer to the same physical occurrence. -/
theorem closedRing_firstAttachment_participants_frame_atom (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (closed : PhysicalClosedRingObservation (state.graph.encode enumeration)) :
    HasBinaryParticipants closed.firstAttachment.ringPosition.val
      ((stateObservationEquiv state enumeration)
        ((stateObservationEquiv state enumeration).symm
          closed.observation.firstSubstituent)).val
      closed.firstAttachment.interaction := by
  simpa using PhysicalClosedRingObservation.firstAttachment_binaryParticipants closed

/-! ### One case, then arbitrary lists of cases -/

/-- Attach a whole list of physical ring-plane observations, each over the same encoded graph, by
mapping the one-case frame construction. -/
def ringPlaneObservationFrames (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observations : List (PhysicalRingPlaneObservation (state.graph.encode enumeration))) :
    List (FrameAnnotation V) :=
  observations.map (ringPlaneObservationFrame state enumeration)

@[simp] theorem ringPlaneObservationFrames_length (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observations : List (PhysicalRingPlaneObservation (state.graph.encode enumeration))) :
    (ringPlaneObservationFrames state enumeration observations).length =
      observations.length := by
  simp [ringPlaneObservationFrames]

/-- The occurrence at every position is the one-case frame of the observation at that position. -/
@[simp] theorem ringPlaneObservationFrames_getElem? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observations : List (PhysicalRingPlaneObservation (state.graph.encode enumeration)))
    (index : ℕ) :
    (ringPlaneObservationFrames state enumeration observations)[index]? =
      (observations[index]?).map (ringPlaneObservationFrame state enumeration) := by
  simp only [ringPlaneObservationFrames]
  rw [List.getElem?_map]

/-- The ordered supports of the whole list are recovered case-by-case, at the same positions. -/
@[simp] theorem ringPlaneObservationFrames_ringAtoms? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observations : List (PhysicalRingPlaneObservation (state.graph.encode enumeration))) :
    (ringPlaneObservationFrames state enumeration observations).map
        FrameAnnotation.ringAtoms? =
      observations.map (fun observation =>
        some (observation.ringAtoms.map (stateObservationEquiv state enumeration).symm)) := by
  simp only [ringPlaneObservationFrames]
  rw [List.map_map]
  apply List.map_congr_left
  intro observation _
  simp [ringPlaneObservationFrame_ringAtoms?]

/-- The list-level support statement at an individual occurrence position. -/
theorem ringPlaneObservationFrames_ringAtoms?_getElem? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V))
    (observations : List (PhysicalRingPlaneObservation (state.graph.encode enumeration)))
    (index : ℕ) :
    ((ringPlaneObservationFrames state enumeration observations).map
        FrameAnnotation.ringAtoms?)[index]? =
      (observations[index]?).map (fun observation =>
        some (observation.ringAtoms.map (stateObservationEquiv state enumeration).symm)) := by
  rw [ringPlaneObservationFrames_ringAtoms?]
  simp

/-! ## Selected electronic sites from a present channel

The selected site is built from an actual `IndependentSiteIdentity` of the *present* channel's
supplied counts.  An absent channel produces no site at all (the presence proof is a parameter),
and no slot is defaulted: the numeric slot is the identity's `Fin` value.  The explicit
`MatchesInventory` predicate is kept distinct from `CompatibleWith`, which concerns owner and
site kind of a torsion participant. -/

/-- Build a selected site from an actual independent identity of the state's present electronic
channel.  The `present` argument is a genuine hypothesis, so no site is built for `none`. -/
def stateSelectedSite (state : WholeState V E B) (channel : ElectronicChannel V)
    (_present : state.electronic? = some channel)
    (identity : IndependentSiteIdentity channel.counts) : SelectedElectronicSite V :=
  selectedSiteOfIndependent channel.counts identity

/-- The selected site's inventory is exactly the present channel's supplied counts. -/
@[simp] theorem stateSelectedSite_inventory (state : WholeState V E B) (channel : ElectronicChannel V)
    (present : state.electronic? = some channel)
    (identity : IndependentSiteIdentity channel.counts) :
    (stateSelectedSite state channel present identity).inventory = channel.counts := rfl

/-- The inventory binding is the green API's explicit `MatchesInventory`, derived from the
constructor. -/
@[simp] theorem stateSelectedSite_matchesInventory (state : WholeState V E B)
    (channel : ElectronicChannel V) (present : state.electronic? = some channel)
    (identity : IndependentSiteIdentity channel.counts) :
    (stateSelectedSite state channel present identity).MatchesInventory channel.counts := by
  show (selectedSiteOfIndependent channel.counts identity).MatchesInventory channel.counts
  exact selectedSiteOfIndependent_matchesInventory channel.counts identity

/-- The exact owner is retained. -/
@[simp] theorem stateSelectedSite_owner (state : WholeState V E B) (channel : ElectronicChannel V)
    (present : state.electronic? = some channel)
    (identity : IndependentSiteIdentity channel.counts) :
    (stateSelectedSite state channel present identity).owner = identity.owner := rfl

/-- The exact site kind is retained. -/
@[simp] theorem stateSelectedSite_kind (state : WholeState V E B) (channel : ElectronicChannel V)
    (present : state.electronic? = some channel)
    (identity : IndependentSiteIdentity channel.counts) :
    (stateSelectedSite state channel present identity).kind = identity.kind := rfl

/-- The exact numeric slot is retained; no default slot is chosen. -/
@[simp] theorem stateSelectedSite_slot (state : WholeState V E B) (channel : ElectronicChannel V)
    (present : state.electronic? = some channel)
    (identity : IndependentSiteIdentity channel.counts) :
    (stateSelectedSite state channel present identity).slot = identity.slot.val := rfl

/-- Distinct independent identities yield distinct selected sites, so two lone pairs at one owner
are never collapsed. -/
theorem stateSelectedSite_injective (state : WholeState V E B) (channel : ElectronicChannel V)
    (present : state.electronic? = some channel) :
    Function.Injective (stateSelectedSite state channel present) := by
  show Function.Injective (selectedSiteOfIndependent channel.counts)
  exact selectedSiteOfIndependent_injective channel.counts

/-- A torsion reference frame whose two optional site slots are filled from actual independent
identities of the supplied counts. -/
def torsionFrameWithSelectedSites (counts : IndependentSiteCounts V) (axisPath : List V)
    (front rear : TorsionParticipant V)
    (frontIdentity rearIdentity : IndependentSiteIdentity counts) :
    TorsionReferenceFrame V where
  axisPath := axisPath
  front := front
  rear := rear
  frontSite? := some (selectedSiteOfIndependent counts frontIdentity)
  rearSite? := some (selectedSiteOfIndependent counts rearIdentity)

/-- Actual participant owner/kind facts make the assembled torsion frame valid.  The owner and
kind conditions are exactly the `CompatibleWith` content, not a default or an assumed inverse. -/
theorem torsionFrameWithSelectedSites_valid (counts : IndependentSiteCounts V)
    (axisPath : List V) (front rear : TorsionParticipant V)
    (frontIdentity rearIdentity : IndependentSiteIdentity counts)
    (frontOwner : frontIdentity.owner = SelectedElectronicSite.participantOwner front)
    (frontKind : ∀ kind, SelectedElectronicSite.participantSiteKind? front = some kind →
      frontIdentity.kind = kind)
    (rearOwner : rearIdentity.owner = SelectedElectronicSite.participantOwner rear)
    (rearKind : ∀ kind, SelectedElectronicSite.participantSiteKind? rear = some kind →
      rearIdentity.kind = kind) :
    (torsionFrameWithSelectedSites counts axisPath front rear
      frontIdentity rearIdentity).Valid := by
  unfold TorsionReferenceFrame.Valid torsionFrameWithSelectedSites
  constructor
  · intro site member
    simp only [Option.some.injEq] at member
    subst member
    exact ⟨by simpa using frontOwner, by simpa using frontKind⟩
  · intro site member
    simp only [Option.some.injEq] at member
    subst member
    exact ⟨by simpa using rearOwner, by simpa using rearKind⟩

/-- The channel's staged evidence assignment at an identity is one of the supplied evidence
entries for that exact owner and kind.  In particular this module never manufactures a point or
direction: an `unspecified` entry is not replaced by any default geometry. -/
theorem toSiteAssignment_valueAt_mem (channel : ElectronicChannel V)
    (identity : IndependentSiteIdentity channel.counts) :
    channel.toSiteAssignment.valueAt identity ∈
      channel.evidence identity.owner identity.kind := by
  unfold ElectronicChannel.toSiteAssignment
  exact List.get_mem _ _

/-! ## Arbitrary joint request sets and exact image recovery

The singleton characterisation of the preceding section concerns one *fixed* assembled state.  The
joint-uncertainty statement required here is different: an arbitrary family of whole requests, each
with its own physical base and its own entire ordered bundle, must be recoverable as a set from its
joint assembly image.  The empty-base-fields restriction is carried explicitly, and the recovery is
an equality of whole requests, so every base/bundle correlation is retained. -/

/-- A whole request whose physical base is a genuine empty-case-channel ingress state.  This is the
explicit empty-base-fields restriction, packaged as a subtype of whole requests. -/
abbrev EmptyBaseRequest (V E B : Type*) [DecidableEq V] [Fintype V] [Fintype E] [Fintype B] :
    Type _ :=
  { request : CaseRequest V E B // CaseChannelsEmpty request.base }

namespace EmptyBaseRequest

/-- The underlying whole request of an empty-base request. -/
def toRequest {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (request : EmptyBaseRequest V E B) : CaseRequest V E B :=
  request.val

/-- The subtype genuinely carries the empty-base-fields certificate. -/
theorem toRequest_emptyBase {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (request : EmptyBaseRequest V E B) :
    CaseChannelsEmpty (toRequest request).base :=
  request.property

/-- Every whole request with empty base case channels is represented in the subtype. -/
theorem exists_of_emptyBase {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (request : CaseRequest V E B) (empty : CaseChannelsEmpty request.base) :
    ∃ emptyBase : EmptyBaseRequest V E B, toRequest emptyBase = request :=
  ⟨⟨request, empty⟩, rfl⟩

end EmptyBaseRequest

/-- The actual request inverse is two-sided on every request with empty base case channels.  This
is an equality of whole requests, not a pair of independent component facts. -/
theorem wholeRequestOfState_assemble_of_emptyBase {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (request : CaseRequest V E B)
    (empty : CaseChannelsEmpty request.base) :
    wholeRequestOfState (assemble request) = request := by
  obtain ⟨base, bundle⟩ := request
  have baseEq : clearCases base = base := clearCases_eq_self_of_empty empty
  simp [wholeRequestOfState, assemble, baseEq]

/-- The assembly image of an arbitrary set of whole requests. -/
def assembleSet {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (requests : Set (CaseRequest V E B)) : Set (WholeState V E B) :=
  assemble '' requests

/-- The whole-request image of an arbitrary set of assembled states, using the actual inverse. -/
def wholeRequestSet {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (states : Set (WholeState V E B)) : Set (CaseRequest V E B) :=
  wholeRequestOfState '' states

/-- Arbitrary joint-set recovery.  For *every* set of whole requests whose bases genuinely have
empty case channels, the actual inverse applied to the assembly image returns exactly that set.
The equality is an equality of whole requests, so the base and the entire ordered bundle of each
request stay correlated; there is no product of channel marginals. -/
theorem wholeRequestSet_assembleSet {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (requests : Set (CaseRequest V E B))
    (emptyBase : ∀ request ∈ requests, CaseChannelsEmpty request.base) :
    wholeRequestSet (assembleSet requests) = requests := by
  ext request
  constructor
  · intro member
    unfold wholeRequestSet at member
    rw [Set.mem_image] at member
    obtain ⟨state, stateMember, rfl⟩ := member
    unfold assembleSet at stateMember
    rw [Set.mem_image] at stateMember
    obtain ⟨source, sourceMember, rfl⟩ := stateMember
    simpa [wholeRequestOfState_assemble_of_emptyBase source (emptyBase source sourceMember)]
      using sourceMember
  · intro member
    unfold wholeRequestSet
    rw [Set.mem_image]
    refine ⟨assemble request, ?_, ?_⟩
    · unfold assembleSet
      rw [Set.mem_image]
      exact ⟨request, member, rfl⟩
    · exact wholeRequestOfState_assemble_of_emptyBase request (emptyBase request member)

/-- The arbitrary-joint-set theorem specialised to the explicit subtype of empty-base requests. -/
theorem wholeRequestSet_assembleSet_emptyBaseRequest {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (requests : Set (EmptyBaseRequest V E B)) :
    wholeRequestSet (assembleSet (EmptyBaseRequest.toRequest '' requests)) =
      EmptyBaseRequest.toRequest '' requests := by
  apply wholeRequestSet_assembleSet
  intro request member
  rw [Set.mem_image] at member
  obtain ⟨source, _, rfl⟩ := member
  simpa [EmptyBaseRequest.toRequest] using source.property

/-! ### Whole-request encoding and decoding -/

/-- Encode a whole request.  The base description and the whole ordered bundle are encoded by the
same atom enumeration and then re-paired; the request is never split into independent channels. -/
noncomputable def encodeRequest {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (request : CaseRequest V E B) :
    CaseRequest (Fin (Fintype.card V)) (Fin (Fintype.card E)) (Fin (Fintype.card B)) :=
  ⟨encodeDescription eV eE eB request.base, request.bundle.relabel eV⟩

/-- Decode a whole encoded request using only the encoded payload and the three equivalences. -/
noncomputable def decodeRequest {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (request : CaseRequest (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    CaseRequest V E B :=
  ⟨decodeDescription eV eE eB request.base, request.bundle.relabel eV.symm⟩

/-- The encoded base is exactly the encoded description of the original base. -/
@[simp] theorem encodeRequest_base {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (request : CaseRequest V E B) :
    (encodeRequest eV eE eB request).base = encodeDescription eV eE eB request.base := rfl

/-- The encoded bundle is exactly the whole bundle relabelled by the same enumeration. -/
@[simp] theorem encodeRequest_bundle {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (request : CaseRequest V E B) :
    (encodeRequest eV eE eB request).bundle = request.bundle.relabel eV := rfl

/-- The decoded base is exactly the decoded description of the encoded base. -/
@[simp] theorem decodeRequest_base {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (request : CaseRequest (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeRequest eV eE eB request).base = decodeDescription eV eE eB request.base := rfl

/-- The decoded bundle is exactly the whole encoded bundle relabelled back. -/
@[simp] theorem decodeRequest_bundle {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (request : CaseRequest (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    (decodeRequest eV eE eB request).bundle = request.bundle.relabel eV.symm := rfl

/-- The actual decoder inverts the actual encoder on whole requests. -/
theorem decodeRequest_encodeRequest {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (request : CaseRequest V E B) :
    decodeRequest eV eE eB (encodeRequest eV eE eB request) = request := by
  obtain ⟨base, bundle⟩ := request
  have bundleEq : (bundle.relabel eV).relabel eV.symm = bundle :=
    CaseBundle.relabel_symm eV bundle
  simp only [decodeRequest, encodeRequest, decodeDescription_encodeDescription, bundleEq]

/-- The actual encoder inverts the actual decoder on whole encoded requests. -/
theorem encodeRequest_decodeRequest {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (request : CaseRequest (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :
    encodeRequest eV eE eB (decodeRequest eV eE eB request) = request := by
  obtain ⟨base, bundle⟩ := request
  have bundleEq : (bundle.relabel eV.symm).relabel eV = bundle := by
    simpa using CaseBundle.relabel_symm eV.symm bundle
  simp only [decodeRequest, encodeRequest, encodeDescription_decodeDescription, bundleEq]

/-! ### Encoding preserves the empty-base restriction -/

/-- Encoding exposes exactly the source fragment list, atom-relabelled by the common
enumeration. -/
@[simp] theorem encodeDescription_fragments {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (description : WholeState V E B) :
    (encodeDescription eV eE eB description).fragments =
      description.fragments.map (fun annotation => annotation.relabel eV) := by
  unfold encodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- Encoding exposes exactly the source convention channel under the common enumeration. -/
@[simp] theorem encodeDescription_conventions {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (description : WholeState V E B) :
    (encodeDescription eV eE eB description).conventions =
      ConventionChannel.encode eV description.conventions := by
  unfold encodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- Encoding exposes exactly the source cage list under the common enumeration. -/
@[simp] theorem encodeDescription_cages {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (description : WholeState V E B) :
    (encodeDescription eV eE eB description).cages =
      NumberedCageAnnotation.relabelList eV description.cages := by
  unfold encodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- Encoding preserves the explicit empty-base-fields property: empty ordered channels stay
empty. -/
theorem encodeDescription_caseChannelsEmpty {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    {base : WholeState V E B} (empty : CaseChannelsEmpty base) :
    CaseChannelsEmpty (encodeDescription eV eE eB base) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [encodeDescription_frames, empty.frames]
    simp
  · rw [encodeDescription_fragments, empty.fragments]
    simp
  · rw [encodeDescription_conventions, empty.conventions]
    simp [ConventionChannel.encode]
  · rw [encodeDescription_cages, empty.cages]
    simp

/-- The encoded whole request has the empty-base property whenever the source request does. -/
theorem encodeRequest_emptyBase {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (request : CaseRequest V E B)
    (empty : CaseChannelsEmpty request.base) :
    CaseChannelsEmpty (encodeRequest eV eE eB request).base := by
  simpa only [encodeRequest_base] using encodeDescription_caseChannelsEmpty eV eE eB empty

/-- Encoding an assembled whole request and reading it back with the actual inverse returns the
encoded whole request.  This is the pointwise bridge used for the arbitrary-set recovery; the
empty-base certificate is needed exactly because the inverse clears the base case channels. -/
theorem wholeRequestOfState_encodeDescription_assemble {V E B : Type*} [DecidableEq V]
    [Fintype V] [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (request : CaseRequest V E B) (empty : CaseChannelsEmpty request.base) :
    wholeRequestOfState (encodeDescription eV eE eB (assemble request)) =
      encodeRequest eV eE eB request := by
  obtain ⟨base, bundle⟩ := request
  have encodedEmpty : CaseChannelsEmpty (encodeDescription eV eE eB base) :=
    encodeDescription_caseChannelsEmpty eV eE eB empty
  have clearEq : clearCases (encodeDescription eV eE eB base) =
      encodeDescription eV eE eB base :=
    clearCases_eq_self_of_empty encodedEmpty
  rw [assemble_mk, encodeDescription_attachCases]
  unfold wholeRequestOfState encodeRequest
  simp only [clearCases_attachCases, extractCases_attachCases, clearEq]

/-! ### Encoded descriptions of arbitrary request sets -/

/-- Encoding an assembled whole request is assembling the encoded whole request. -/
theorem encodeDescription_assemble {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (request : CaseRequest V E B) :
    encodeDescription eV eE eB (assemble request) =
      assemble (encodeRequest eV eE eB request) := by
  obtain ⟨base, bundle⟩ := request
  simp [assemble, encodeRequest, encodeDescription_attachCases]

/-- The encoded image of an arbitrary set of whole requests. -/
noncomputable def encodeRequestSet {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (requests : Set (CaseRequest V E B)) :
    Set (CaseRequest (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B))) :=
  encodeRequest eV eE eB '' requests

/-- The decoded image of an arbitrary set of encoded whole requests. -/
noncomputable def decodeRequestSet {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (requests : Set (CaseRequest (Fin (Fintype.card V)) (Fin (Fintype.card E))
      (Fin (Fintype.card B)))) :
    Set (CaseRequest V E B) :=
  decodeRequest eV eE eB '' requests

/-- Encoding commutes with assembly on arbitrary sets of whole requests. -/
theorem encodeDescription_image_assembleSet {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (requests : Set (CaseRequest V E B)) :
    encodeDescription eV eE eB '' assembleSet requests =
      assembleSet (encodeRequestSet eV eE eB requests) := by
  unfold assembleSet encodeRequestSet
  simp only [Set.image_image]
  change (encodeDescription eV eE eB ∘ assemble) '' requests =
    (assemble ∘ encodeRequest eV eE eB) '' requests
  have functionEq : (encodeDescription eV eE eB ∘ assemble) =
      (assemble ∘ encodeRequest eV eE eB) := by
    funext request
    exact encodeDescription_assemble eV eE eB request
  rw [functionEq]

/-- Reading whole requests back from encoded assembled descriptions is exact on arbitrary sets
with the empty-base restriction.  The encoded descriptions are whole descriptions, so every
base/bundle correlation is retained. -/
theorem wholeRequestSet_encodeDescription_assembleSet {V E B : Type*} [DecidableEq V]
    [Fintype V] [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (requests : Set (CaseRequest V E B))
    (emptyBase : ∀ request ∈ requests, CaseChannelsEmpty request.base) :
    wholeRequestSet (encodeDescription eV eE eB '' assembleSet requests) =
      encodeRequestSet eV eE eB requests := by
  ext request
  constructor
  · intro member
    unfold wholeRequestSet at member
    rw [Set.mem_image] at member
    obtain ⟨state, stateMember, hstate⟩ := member
    rw [Set.mem_image] at stateMember
    obtain ⟨assembled, assembledMember, rfl⟩ := stateMember
    unfold assembleSet at assembledMember
    rw [Set.mem_image] at assembledMember
    obtain ⟨source, sourceMember, rfl⟩ := assembledMember
    rw [wholeRequestOfState_encodeDescription_assemble eV eE eB source
      (emptyBase source sourceMember)] at hstate
    unfold encodeRequestSet
    rw [Set.mem_image]
    exact ⟨source, sourceMember, hstate⟩
  · intro member
    unfold encodeRequestSet at member
    rw [Set.mem_image] at member
    obtain ⟨source, sourceMember, rfl⟩ := member
    unfold wholeRequestSet
    rw [Set.mem_image]
    refine ⟨encodeDescription eV eE eB (assemble source), ?_, ?_⟩
    · rw [Set.mem_image]
      refine ⟨assemble source, ?_, rfl⟩
      unfold assembleSet
      rw [Set.mem_image]
      exact ⟨source, sourceMember, rfl⟩
    · exact wholeRequestOfState_encodeDescription_assemble eV eE eB source
        (emptyBase source sourceMember)

/-- The actual whole-request decoder inverts the encoded request image on every set. -/
theorem decodeRequestSet_encodeRequestSet {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (requests : Set (CaseRequest V E B)) :
    decodeRequestSet eV eE eB (encodeRequestSet eV eE eB requests) = requests := by
  unfold decodeRequestSet encodeRequestSet
  rw [Set.image_image]
  change (decodeRequest eV eE eB ∘ encodeRequest eV eE eB) '' requests = requests
  have composition : (decodeRequest eV eE eB ∘ encodeRequest eV eE eB) = id := by
    funext request
    exact decodeRequest_encodeRequest eV eE eB request
  rw [composition, Set.image_id]

/-- Arbitrary correlated request-set recovery through encoded descriptions.  For every set of
whole requests satisfying the empty-base-fields restriction, encoding the assembled descriptions,
reading them back with the actual whole-request inverse, and decoding the whole encoded request
gives back exactly the original set.  No per-channel marginal and no singleton is used. -/
theorem decodeRequestSet_wholeRequestSet_encodeDescription_assembleSet {V E B : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (requests : Set (CaseRequest V E B))
    (emptyBase : ∀ request ∈ requests, CaseChannelsEmpty request.base) :
    decodeRequestSet eV eE eB
        (wholeRequestSet (encodeDescription eV eE eB '' assembleSet requests)) = requests := by
  rw [wholeRequestSet_encodeDescription_assembleSet eV eE eB requests emptyBase]
  exact decodeRequestSet_encodeRequestSet eV eE eB requests

/-- The same arbitrary-set recovery stated with the explicit composite map: decode each encoded
assembled description with the actual inverse, then decode the whole encoded request. -/
theorem decodeRequest_image_encodeDescription_assembleSet {V E B : Type*} [DecidableEq V]
    [Fintype V] [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (requests : Set (CaseRequest V E B))
    (emptyBase : ∀ request ∈ requests, CaseChannelsEmpty request.base) :
    (fun state => decodeRequest eV eE eB (wholeRequestOfState state)) ''
        (encodeDescription eV eE eB '' assembleSet requests) = requests := by
  have composite :
      (fun state => decodeRequest eV eE eB (wholeRequestOfState state)) ''
          (encodeDescription eV eE eB '' assembleSet requests) =
        decodeRequestSet eV eE eB
          (wholeRequestSet (encodeDescription eV eE eB '' assembleSet requests)) := by
    unfold decodeRequestSet wholeRequestSet
    rw [← Set.image_image]
  rw [composite]
  exact decodeRequestSet_wholeRequestSet_encodeDescription_assembleSet eV eE eB requests emptyBase

/-- Encoded arbitrary-set recovery specialised to the explicit empty-base subtype. -/
theorem decodeRequestSet_wholeRequestSet_encodeDescription_assembleSet_emptyBaseRequest
    {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (requests : Set (EmptyBaseRequest V E B)) :
    decodeRequestSet eV eE eB
        (wholeRequestSet (encodeDescription eV eE eB ''
          assembleSet (EmptyBaseRequest.toRequest '' requests))) =
      EmptyBaseRequest.toRequest '' requests := by
  apply decodeRequestSet_wholeRequestSet_encodeDescription_assembleSet
  intro request member
  rw [Set.mem_image] at member
  obtain ⟨source, _, rfl⟩ := member
  simpa [EmptyBaseRequest.toRequest] using source.property

end TetraStereo.OneCenter
