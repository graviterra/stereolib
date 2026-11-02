import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoFragmentSourceData
import TetraStereo.OneCenter.OrganicStereoSpecialistAnnotations
import TetraStereo.OneCenter.OrganicStereoResidueIncidence
import TetraStereo.OneCenter.OrganicStereoResidueLinkAnnotations
import TetraStereo.OneCenter.OrganicStereoDrawingConventions

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Carbohydrate annotation ingress into the fragment source-data channel

This module is the carbohydrate-specific ingress layer for the shared
`FragmentSourceDatum` / `FragmentAnnotation.sourceData` channel.  It is a *retention* layer:

* the four source-level carbohydrate items are exactly the existing
  `Carbohydrate1996Foundation` carriers (`DLSeries`, `SeriesAndRotation`, `AnomerKnowledge`,
  `AnomerDescriptor`);
* an anomer item additionally carries the two *supplied* natural-number source locants and the
  two atoms those locants actually resolve to in a real `ResidueFragment Nat n`.  The anchors are
  therefore obtained from residue incidence, never from raw drawing geometry;
* the series, optical-rotation sign, anomer-knowledge state and anomer descriptor are supplied
  payloads.  Nothing here derives one from another or from three-dimensional geometry;
* the ordered list channel retains order, duplicates and multiplicity exactly;
* recovery functions on `FragmentSourceDatum` return the original supplied payload and the two
  supplied locants.  Their outputs contain no atom label, so they are independent of the
  `V ≃ W` relabelling.

The existing Fischer and Haworth `ConventionCue` adapters are reused for locant binding.  This
module does not define a second projection-convention channel and does not recompute the Haworth
numbering sense: the source function `haworthNumberingSense` remains the only route.

The annotation builder composes the existing `encodeFragment` constructor with the shared
`FragmentAnnotation.withSourceData` append operation, so every atom anchor in `sourceData` is a
support atom of the encoded residue fragment.  No source input, original request or
figure-approval predicate is stored.

Ring-closure descriptor routing follows the repaired source semantics of 2-Carb-6.4: the router
emits the alpha/beta alphabet only in the lower-anomeric-locant branch and emits nothing in the
reverse branch.  No `R`/`S` assignment is fabricated here; the reverse-closure `R`/`S` value is
consumed from the checked CIP engine in `CarbohydrateRingClosureFidelity`.
-/

/-! ## Supplied anomeric/reference locants -/

/-- The two supplied natural-number source locants of an anomeric annotation.  They are ordered
data; no chemical meaning is computed from the ordering here. -/
structure AnomerLocants where
  /-- The supplied locant of the anomeric centre. -/
  anomeric : Nat
  /-- The supplied locant of the reference centre. -/
  reference : Nat
  deriving DecidableEq, Repr

/-! ## Actual residue-incidence binding -/

/-- One supplied anomeric annotation bound to an actual residue fragment.

The binding records the supplied descriptor and locants, the two atoms that those locants
resolve to in `fragment`, and the exact `incidence` certificates.  There is no field asserting
that the descriptor or the locants are chemically correct, and no value is derived from the
atoms. -/
structure AnomerIngress {n : ℕ} (fragment : ResidueFragment Nat n) where
  /-- The supplied anomeric descriptor. -/
  descriptor : Carbohydrate1996Foundation.AnomerDescriptor
  /-- The supplied anomeric locant. -/
  anomericLocant : Nat
  /-- The supplied reference locant. -/
  referenceLocant : Nat
  /-- The atom to which the anomeric locant actually resolves. -/
  anomericAtom : Fin n
  /-- The atom to which the reference locant actually resolves. -/
  referenceAtom : Fin n
  /-- Exact residue-incidence certificate for the anomeric locant. -/
  anomeric_eq : fragment.incidence anomericLocant = some anomericAtom
  /-- Exact residue-incidence certificate for the reference locant. -/
  reference_eq : fragment.incidence referenceLocant = some referenceAtom

namespace AnomerIngress

variable {n : ℕ} {fragment : ResidueFragment Nat n}

/-- The supplied locant pair, retained verbatim. -/
def locants (ingress : AnomerIngress fragment) : AnomerLocants :=
  ⟨ingress.anomericLocant, ingress.referenceLocant⟩

@[simp] theorem locants_anomeric (ingress : AnomerIngress fragment) :
    ingress.locants.anomeric = ingress.anomericLocant := rfl

@[simp] theorem locants_reference (ingress : AnomerIngress fragment) :
    ingress.locants.reference = ingress.referenceLocant := rfl

/-- The anomeric anchor is an actual support atom of the bound residue. -/
theorem anomeric_mem_support (ingress : AnomerIngress fragment) :
    ingress.anomericAtom ∈ fragment.support :=
  fragment.incidence_mem_support ingress.anomericLocant ingress.anomericAtom ingress.anomeric_eq

/-- The reference anchor is an actual support atom of the bound residue. -/
theorem reference_mem_support (ingress : AnomerIngress fragment) :
    ingress.referenceAtom ∈ fragment.support :=
  fragment.incidence_mem_support ingress.referenceLocant ingress.referenceAtom ingress.reference_eq

/-- Both supplied locants resolve in the actual residue fragment, to the recorded atoms. -/
theorem locants_resolve (ingress : AnomerIngress fragment) :
    fragment.incidence ingress.anomericLocant = some ingress.anomericAtom ∧
      fragment.incidence ingress.referenceLocant = some ingress.referenceAtom :=
  ⟨ingress.anomeric_eq, ingress.reference_eq⟩

end AnomerIngress

/-! ## Atom-free extraction from the shared datum

These extractors are local to this module.  They read exactly the supplied payload and the two
supplied natural-number locants; their result types contain no atom parameter. -/

/-- The two atom anchors of an anomeric datum. -/
def datumAnchors? {V : Type*} : FragmentSourceDatum V → Option (V × V)
  | .carbohydrateAnomer anomeric reference _ _ _ => some (anomeric, reference)
  | _ => none

/-- The two supplied source locants of an anomeric datum. -/
def datumAnomerLocants? {V : Type*} : FragmentSourceDatum V → Option (Nat × Nat)
  | .carbohydrateAnomer _ _ anomericLocant referenceLocant _ =>
      some (anomericLocant, referenceLocant)
  | _ => none

/-- The supplied anomeric descriptor of an anomeric datum. -/
def datumAnomerDescriptor? {V : Type*} : FragmentSourceDatum V →
    Option Carbohydrate1996Foundation.AnomerDescriptor
  | .carbohydrateAnomer _ _ _ _ descriptor => some descriptor
  | _ => none

/-! ### Exact extractor equations

These are the source-specific ties: an anomeric datum's two anchors and two supplied locants are
recovered exactly, in constructor order, with no atom relabelling involved. -/

@[simp] theorem datumAnchors?_anomer {V : Type*} (anomeric reference : V)
    (anomericLocant referenceLocant : Nat)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor) :
    datumAnchors? (.carbohydrateAnomer anomeric reference anomericLocant referenceLocant
      descriptor) = some (anomeric, reference) := rfl

@[simp] theorem datumAnomerLocants?_anomer {V : Type*} (anomeric reference : V)
    (anomericLocant referenceLocant : Nat)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor) :
    datumAnomerLocants? (.carbohydrateAnomer anomeric reference anomericLocant referenceLocant
      descriptor) = some (anomericLocant, referenceLocant) := rfl

@[simp] theorem datumAnomerDescriptor?_anomer {V : Type*} (anomeric reference : V)
    (anomericLocant referenceLocant : Nat)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor) :
    datumAnomerDescriptor? (.carbohydrateAnomer anomeric reference anomericLocant referenceLocant
      descriptor) = some descriptor := rfl

/-- The atom-free view of a carbohydrate datum. -/
inductive DatumView where
  /-- A supplied D/L series. -/
  | series (series : Carbohydrate1996Foundation.DLSeries)
  /-- A supplied series-plus-rotation reading. -/
  | rotation (reading : Carbohydrate1996Foundation.SeriesAndRotation)
  /-- A supplied anomer knowledge state. -/
  | knowledge (knowledge : Carbohydrate1996Foundation.AnomerKnowledge)
  /-- A supplied descriptor with its two supplied locants. -/
  | anomer (anomericLocant referenceLocant : Nat)
      (descriptor : Carbohydrate1996Foundation.AnomerDescriptor)
  deriving DecidableEq, Repr

/-- Read the atom-free carbohydrate view of a datum.  Atomic anchors are deliberately excluded,
so the view is source-independent. -/
def datumView? {V : Type*} : FragmentSourceDatum V → Option DatumView
  | .carbohydrateSeries series => some (.series series)
  | .carbohydrateRotation reading => some (.rotation reading)
  | .carbohydrateAnomerKnowledge knowledge => some (.knowledge knowledge)
  | .carbohydrateAnomer _ _ anomericLocant referenceLocant descriptor =>
      some (.anomer anomericLocant referenceLocant descriptor)
  | _ => none

/-! ## The ordered carbohydrate entry channel -/

/-- One supplied carbohydrate annotation item.  The atom-bearing `anomer` constructor binds to an
actual residue fragment through `AnomerIngress`; the remaining three constructors are literal
source-level payloads with no atom reference. -/
inductive Entry {n : ℕ} (fragment : ResidueFragment Nat n) where
  /-- A supplied D/L series. -/
  | series (series : Carbohydrate1996Foundation.DLSeries)
  /-- A supplied series-plus-optical-rotation reading. -/
  | rotation (reading : Carbohydrate1996Foundation.SeriesAndRotation)
  /-- A supplied anomer knowledge state. -/
  | knowledge (knowledge : Carbohydrate1996Foundation.AnomerKnowledge)
  /-- A supplied anomeric descriptor with actual residue-incidence anchors. -/
  | anomer (ingress : AnomerIngress fragment)

namespace Entry

variable {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}

/-- Map one entry to the shared closed datum.  Order and multiplicity are preserved by list
mapping at the call site. -/
def datum (enumeration : Fin n ≃ V) : Entry fragment → FragmentSourceDatum V
  | .series value => .carbohydrateSeries value
  | .rotation reading => .carbohydrateRotation reading
  | .knowledge state => .carbohydrateAnomerKnowledge state
  | .anomer ingress =>
      .carbohydrateAnomer (enumeration ingress.anomericAtom)
        (enumeration ingress.referenceAtom) ingress.anomericLocant ingress.referenceLocant
        ingress.descriptor

/-- The supplied atom-free view of an entry. -/
def view : Entry fragment → DatumView
  | .series value => .series value
  | .rotation reading => .rotation reading
  | .knowledge state => .knowledge state
  | .anomer ingress =>
      .anomer ingress.anomericLocant ingress.referenceLocant ingress.descriptor

/-- The shared datum maps to exactly the entry's supplied view. -/
@[simp] theorem datum_view (enumeration : Fin n ≃ V) (entry : Entry fragment) :
    datumView? (entry.datum enumeration) = some entry.view := by
  cases entry with
  | series value => rfl
  | rotation reading => rfl
  | knowledge state => rfl
  | anomer ingress => rfl

end Entry

/-- The ordered datum list of an entry list.  The map is literally `List.map`, so order,
duplicates and length are retained. -/
def entriesData {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    (enumeration : Fin n ≃ V) (entries : List (Entry fragment)) : List (FragmentSourceDatum V) :=
  entries.map (Entry.datum enumeration)

@[simp] theorem entriesData_length {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    (enumeration : Fin n ≃ V) (entries : List (Entry fragment)) :
    (entriesData enumeration entries).length = entries.length := by
  simp [entriesData]

/-- Ordered lookup into the datum channel is the datum of the entry at the same position. -/
theorem entriesData_get? {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    (enumeration : Fin n ≃ V) (entries : List (Entry fragment)) (index : Nat)
    (bound : index < entries.length) :
    (entriesData enumeration entries)[index]? =
      some (Entry.datum enumeration (entries[index]'bound)) := by
  unfold entriesData
  rw [List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- The view channel is source-independent: it is the view of the original entries, in order. -/
theorem entriesData_view {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    (enumeration : Fin n ≃ V) (entries : List (Entry fragment)) :
    (entriesData enumeration entries).filterMap datumView? = entries.map Entry.view := by
  induction entries with
  | nil => rfl
  | cons head tail hypothesis =>
      unfold entriesData at hypothesis ⊢
      rw [List.map_cons, List.filterMap_cons, Entry.datum_view]
      exact congrArg (List.cons head.view) hypothesis

/-! ## Support containment for the source-data channel -/

/-- Every atom reference of an entry's datum lies in the transported residue support. -/
theorem Entry.datum_atomReferences_subset {V : Type*} {n : ℕ}
    {fragment : ResidueFragment Nat n} (enumeration : Fin n ≃ V) (entry : Entry fragment) :
    ∀ atom, atom ∈ (entry.datum enumeration).atomReferences →
      atom ∈ fragment.support.map enumeration.toEmbedding := by
  cases entry with
  | series series =>
      intro atom member
      have empty : (Entry.datum enumeration (Entry.series series : Entry fragment)).atomReferences =
          [] := rfl
      rw [empty] at member
      exact absurd member (by simp)
  | rotation reading =>
      intro atom member
      have empty :
          (Entry.datum enumeration (Entry.rotation reading : Entry fragment)).atomReferences = [] :=
        rfl
      rw [empty] at member
      exact absurd member (by simp)
  | knowledge knowledge =>
      intro atom member
      have empty :
          (Entry.datum enumeration (Entry.knowledge knowledge : Entry fragment)).atomReferences = [] :=
        rfl
      rw [empty] at member
      exact absurd member (by simp)
  | anomer ingress =>
      intro atom member
      have anchors :
          (Entry.datum enumeration (Entry.anomer ingress : Entry fragment)).atomReferences =
            [enumeration ingress.anomericAtom, enumeration ingress.referenceAtom] := rfl
      rw [anchors] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with equality | equality
      · rw [equality]
        exact Finset.mem_map.mpr ⟨ingress.anomericAtom, ingress.anomeric_mem_support, rfl⟩
      · rw [equality]
        exact Finset.mem_map.mpr ⟨ingress.referenceAtom, ingress.reference_mem_support, rfl⟩

/-- Every datum in the ordered channel has atom references inside the transported support. -/
theorem entriesData_supported {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    (enumeration : Fin n ≃ V) (entries : List (Entry fragment)) :
    ∀ datum ∈ entriesData enumeration entries, ∀ atom,
      atom ∈ datum.atomReferences → atom ∈ fragment.support.map enumeration.toEmbedding := by
  intro datum member atom inReferences
  obtain ⟨entry, _entryMember, equality⟩ := List.mem_map.mp member
  rw [← equality] at inReferences
  exact Entry.datum_atomReferences_subset enumeration entry atom inReferences

/-! ## Building the extended fragment annotation -/

/-- Build the shared extended fragment annotation from an actual residue fragment and an
arbitrary ordered carbohydrate entry list.

The support is exactly the residue support transported through the caller's enumeration, the
scoped locant bindings are the existing `encodeFragment` bindings, and `sourceData` is the
ordered datum list appended by the shared `withSourceData` operation.  The support-containment
argument is proved from actual residue incidence via `entriesData_supported`. -/
def annotationOfEntries {V : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat)
    (entries : List (Entry fragment)) : FragmentAnnotation V :=
  (encodeFragment LocantCodec.nat enumeration.symm fragment cover).withSourceData
    (entriesData enumeration entries)
    (by
      intro datum member atom inReferences
      have supported := entriesData_supported enumeration entries datum member atom inReferences
      simpa [encodeFragment_support] using supported)

@[simp] theorem annotationOfEntries_support {V : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment)) :
    (annotationOfEntries enumeration fragment cover entries).support =
      fragment.support.map enumeration.toEmbedding := by
  simp [annotationOfEntries, encodeFragment_support]

@[simp] theorem annotationOfEntries_sourceData {V : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment)) :
    (annotationOfEntries enumeration fragment cover entries).sourceData =
      entriesData enumeration entries := by
  simp [annotationOfEntries, encodeFragment_sourceData]

@[simp] theorem annotationOfEntries_bindings {V : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment)) :
    (annotationOfEntries enumeration fragment cover entries).bindings =
      cover.map fun locant => (LocantCodec.nat.code locant,
        (fragment.incidence locant).map enumeration.toEmbedding) := by
  simp [annotationOfEntries, encodeFragment_bindings]

/-- Every anomer entry's two anchors are support atoms of the built annotation. -/
theorem annotationOfEntries_anomer_anchors {V : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment))
    {ingress : AnomerIngress fragment} (_member : Entry.anomer ingress ∈ entries) :
    enumeration ingress.anomericAtom ∈
        (annotationOfEntries enumeration fragment cover entries).support ∧
      enumeration ingress.referenceAtom ∈
        (annotationOfEntries enumeration fragment cover entries).support := by
  rw [annotationOfEntries_support]
  exact ⟨Finset.mem_map.mpr ⟨ingress.anomericAtom, ingress.anomeric_mem_support, rfl⟩,
    Finset.mem_map.mpr ⟨ingress.referenceAtom, ingress.reference_mem_support, rfl⟩⟩

/-- Exact source-independent recovery of the ordered view channel from the built annotation. -/
theorem annotationOfEntries_view {V : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment)) :
    (annotationOfEntries enumeration fragment cover entries).sourceData.filterMap datumView? =
      entries.map Entry.view := by
  rw [annotationOfEntries_sourceData]
  exact entriesData_view enumeration entries

/-- Exact ordered lookup into the built annotation's source-data channel. -/
theorem annotationOfEntries_sourceData_get? {V : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment))
    (index : Nat) (bound : index < entries.length) :
    (annotationOfEntries enumeration fragment cover entries).sourceData[index]? =
      some (Entry.datum enumeration (entries[index]'bound)) := by
  rw [annotationOfEntries_sourceData]
  exact entriesData_get? enumeration entries index bound

/-! ## Relabelling compatibility -/

/-- Relabelling the built annotation by an external atom equivalence relabels exactly the atom
anchors: support and source-data atoms move, while every supplied value and locant is unchanged. -/
theorem annotationOfEntries_relabel {V W : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment))
    (relabelling : V ≃ W) :
    (annotationOfEntries enumeration fragment cover entries).relabel relabelling =
      annotationOfEntries (enumeration.trans relabelling) fragment cover entries := by
  apply FragmentAnnotation.ext
  · simp [annotationOfEntries, FragmentAnnotation.relabel, Finset.map_map,
      Equiv.trans_toEmbedding]
  · simp [annotationOfEntries, FragmentAnnotation.relabel, Option.map_map]
  · rw [annotationOfEntries, annotationOfEntries, FragmentAnnotation.relabel_withSourceData]
    simp only [FragmentAnnotation.withSourceData_sourceData, encodeFragment_sourceData,
      List.nil_append, entriesData, List.map_map]
    apply List.map_congr_left
    intro entry _member
    cases entry with
    | series series =>
        simp only [Function.comp_apply, Entry.datum, FragmentSourceDatum.relabel]
    | rotation reading =>
        simp only [Function.comp_apply, Entry.datum, FragmentSourceDatum.relabel]
    | knowledge knowledge =>
        simp only [Function.comp_apply, Entry.datum, FragmentSourceDatum.relabel]
    | anomer ingress =>
        simp only [Function.comp_apply, Entry.datum, FragmentSourceDatum.relabel,
          Equiv.trans_apply]

/-- The atom-free view channel is invariant under relabelling the built annotation. -/
theorem annotationOfEntries_relabel_view {V W : Type*} {n : ℕ} (enumeration : Fin n ≃ V)
    (fragment : ResidueFragment Nat n) (cover : List Nat) (entries : List (Entry fragment))
    (relabelling : V ≃ W) :
    ((annotationOfEntries enumeration fragment cover entries).relabel relabelling).sourceData.filterMap
        datumView? = entries.map Entry.view := by
  rw [annotationOfEntries_relabel]
  exact annotationOfEntries_view (enumeration.trans relabelling) fragment cover entries

/-! ## Series and optical rotation are independent supplied data -/

/-- The supplied series payload of a datum, if the datum is a series item. -/
def seriesPayload? {V : Type*} : FragmentSourceDatum V →
    Option Carbohydrate1996Foundation.DLSeries
  | .carbohydrateSeries series => some series
  | _ => none

/-- The supplied series-plus-rotation payload of a datum, if the datum is a rotation item. -/
def rotationPayload? {V : Type*} : FragmentSourceDatum V →
    Option Carbohydrate1996Foundation.SeriesAndRotation
  | .carbohydrateRotation reading => some reading
  | _ => none

/-- The series component of a supplied rotation reading. -/
def rotationSeries? {V : Type*} (datum : FragmentSourceDatum V) :
    Option Carbohydrate1996Foundation.DLSeries :=
  (rotationPayload? datum).map Carbohydrate1996Foundation.SeriesAndRotation.series

/-- The optical-rotation sign of a supplied rotation reading. -/
def rotationSign? {V : Type*} (datum : FragmentSourceDatum V) :
    Option Carbohydrate1996Foundation.OpticalRotationSign :=
  (rotationPayload? datum).map Carbohydrate1996Foundation.SeriesAndRotation.rotation

/-- Literal series retention. -/
@[simp] theorem seriesPayload?_seriesDatum {V : Type*}
    (series : Carbohydrate1996Foundation.DLSeries) :
    seriesPayload? (V := V) (.carbohydrateSeries series) = some series := rfl

/-- Literal rotation-reading retention. -/
@[simp] theorem rotationPayload?_rotationDatum {V : Type*}
    (reading : Carbohydrate1996Foundation.SeriesAndRotation) :
    rotationPayload? (V := V) (.carbohydrateRotation reading) = some reading := rfl

/-- The source theorem that the D series does not determine the optical-rotation sign is
preserved through the datum channel.  Series and rotation are recovered independently. -/
theorem rotation_series_sign_independent {V : Type*} :
    rotationSeries? (V := V)
        (.carbohydrateRotation Carbohydrate1996Foundation.dGlucoseReading) =
      rotationSeries? (V := V)
        (.carbohydrateRotation Carbohydrate1996Foundation.dFructoseReading) ∧
    rotationSign? (V := V)
        (.carbohydrateRotation Carbohydrate1996Foundation.dGlucoseReading) ≠
      rotationSign? (V := V)
        (.carbohydrateRotation Carbohydrate1996Foundation.dFructoseReading) := by
  obtain ⟨sameSeries, differentRotation⟩ :=
    Carbohydrate1996Foundation.D_does_not_determine_optical_rotation_sign
  constructor
  · simp only [rotationSeries?, rotationPayload?, Option.map_some]
    rw [sameSeries]
  · intro equal
    apply differentRotation
    simpa [rotationSign?, rotationPayload?] using equal

/-! ## Anomer knowledge states are preserved exactly -/

/-- The supplied anomer-knowledge payload of a datum. -/
def knowledgePayload? {V : Type*} : FragmentSourceDatum V →
    Option Carbohydrate1996Foundation.AnomerKnowledge
  | .carbohydrateAnomerKnowledge knowledge => some knowledge
  | _ => none

/-- Literal knowledge-state retention. -/
@[simp] theorem knowledgePayload?_knowledgeDatum {V : Type*}
    (knowledge : Carbohydrate1996Foundation.AnomerKnowledge) :
    knowledgePayload? (V := V) (.carbohydrateAnomerKnowledge knowledge) = some knowledge := rfl

/-- Recovered knowledge states carry exactly the source name symbols. -/
@[simp] theorem knowledgePayload?_symbols {V : Type*}
    (knowledge : Carbohydrate1996Foundation.AnomerKnowledge) :
    (knowledgePayload? (V := V) (.carbohydrateAnomerKnowledge knowledge)).map
        Carbohydrate1996Foundation.anomerNameSymbols =
      some (Carbohydrate1996Foundation.anomerNameSymbols knowledge) := rfl

/-- The three source knowledge states are pairwise distinct, so an alpha-only, beta-only or
equilibrium/mixture annotation cannot be confused after recovery. -/
theorem knowledge_states_pairwise_distinct :
    Carbohydrate1996Foundation.AnomerKnowledge.alphaOnly ≠
        Carbohydrate1996Foundation.AnomerKnowledge.betaOnly ∧
      Carbohydrate1996Foundation.AnomerKnowledge.alphaOnly ≠
        Carbohydrate1996Foundation.AnomerKnowledge.equilibriumAlphaBeta ∧
      Carbohydrate1996Foundation.AnomerKnowledge.betaOnly ≠
        Carbohydrate1996Foundation.AnomerKnowledge.equilibriumAlphaBeta := by
  decide

/-! ## Anomeric descriptor routing and supplied locants

The source router is now a *family* decision.  The Greek letters `alpha` and `beta` are emitted
only in the lower-anomeric-locant branch.  In the reverse-closure branch the router returns no
descriptor at all; the configuration there is an `R`/`S` symbol produced by the actual checked CIP
consumer in `CarbohydrateRingClosureFidelity`, which takes a molecular graph, resolved CIP
priorities and a physical realization as explicit inputs.  The supplied `AnomerDescriptor` is
still retained losslessly by `datumAnomerDescriptor?`. -/

/-- Exact restatement of the repaired source family decision. -/
theorem anomerDescriptorFamily_eq (anomericLocant referenceLocant : Nat) :
    Carbohydrate1996Foundation.anomerDescriptorFamily anomericLocant referenceLocant =
      if anomericLocant < referenceLocant then
        Carbohydrate1996Foundation.AnomerDescriptorFamily.alphaBetaPermitted
      else Carbohydrate1996Foundation.AnomerDescriptorFamily.requiresCIP := rfl

/-- Exact case restatement of the repaired source router: a lower supplied anomeric locant yields
exactly `some (alphaBeta anomer)` and the reverse branch yields `none`.  No `R`/`S` value is
fabricated at this layer. -/
theorem descriptorForRingClosure?_eq (anomericLocant referenceLocant : Nat)
    (anomer : Carbohydrate1996Foundation.Anomer) :
    Carbohydrate1996Foundation.descriptorForRingClosure?
        anomericLocant referenceLocant anomer =
      if anomericLocant < referenceLocant then
        some (Carbohydrate1996Foundation.AnomerDescriptor.alphaBeta anomer)
      else none := rfl

/-- A lower supplied anomeric locant is exactly the source condition for the alpha/beta
descriptor family. -/
theorem descriptorForRingClosure?_alphaBeta_iff (anomericLocant referenceLocant : Nat)
    (anomer : Carbohydrate1996Foundation.Anomer) :
    Carbohydrate1996Foundation.descriptorForRingClosure?
        anomericLocant referenceLocant anomer =
      some (Carbohydrate1996Foundation.AnomerDescriptor.alphaBeta anomer) ↔
    anomericLocant < referenceLocant := by
  by_cases lower : anomericLocant < referenceLocant
  · simp [Carbohydrate1996Foundation.descriptorForRingClosure?, lower]
  · simp [Carbohydrate1996Foundation.descriptorForRingClosure?, lower]

/-- The router emits a descriptor exactly when the family decision permits the Greek letters. -/
theorem descriptorForRingClosure?_isSome_iff (anomericLocant referenceLocant : Nat)
    (anomer : Carbohydrate1996Foundation.Anomer) :
    (Carbohydrate1996Foundation.descriptorForRingClosure?
        anomericLocant referenceLocant anomer).isSome ↔
      Carbohydrate1996Foundation.anomerDescriptorFamily anomericLocant referenceLocant =
        Carbohydrate1996Foundation.AnomerDescriptorFamily.alphaBetaPermitted :=
  Carbohydrate1996Foundation.descriptorForRingClosure?_isSome_iff_family
    anomericLocant referenceLocant anomer

/-- When the supplied anomeric locant is not lower than the supplied reference locant, the source
router never produces an alpha/beta descriptor.  This is the reverse-ring-closure rule
generalised beyond the fixed witness locants in the source module. -/
theorem descriptorForRingClosure?_not_alphaBeta (anomericLocant referenceLocant : Nat)
    (notLower : ¬ anomericLocant < referenceLocant)
    (anomer : Carbohydrate1996Foundation.Anomer) :
    Carbohydrate1996Foundation.descriptorForRingClosure?
        anomericLocant referenceLocant anomer ≠
      some (Carbohydrate1996Foundation.AnomerDescriptor.alphaBeta anomer) := by
  simp [Carbohydrate1996Foundation.descriptorForRingClosure?, notLower]

/-- In the reverse-closure branch the source router yields no descriptor whatsoever, so the
anomer letter cannot be converted into an `R` or `S` value at the ingress layer. -/
theorem descriptorForRingClosure?_reverse_none (anomericLocant referenceLocant : Nat)
    (notLower : ¬ anomericLocant < referenceLocant)
    (anomer : Carbohydrate1996Foundation.Anomer)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor) :
    Carbohydrate1996Foundation.descriptorForRingClosure?
        anomericLocant referenceLocant anomer ≠ some descriptor := by
  simp [Carbohydrate1996Foundation.descriptorForRingClosure?, notLower]

/-- The supplied descriptor is retained losslessly: recovery followed by the family label is the
family label of the original supplied descriptor.  This is a statement about the codec, not a
claim that the supplied descriptor agrees with any molecular configuration. -/
@[simp] theorem datumAnomerDescriptor?_family {V : Type*} (anomeric reference : V)
    (anomericLocant referenceLocant : Nat)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor) :
    (datumAnomerDescriptor? (.carbohydrateAnomer anomeric reference anomericLocant
        referenceLocant descriptor)).map
        Carbohydrate1996Foundation.AnomerDescriptor.family =
      some descriptor.family := rfl

/-- The codec and the family router are independent channels: recovering the supplied descriptor
never consults the locant router. -/
theorem datumAnomerDescriptor?_eq_of_supplied {V : Type*} (anomeric reference : V)
    (anomericLocant referenceLocant : Nat)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor)
    (anomer : Carbohydrate1996Foundation.Anomer) :
    datumAnomerDescriptor? (.carbohydrateAnomer anomeric reference anomericLocant
        referenceLocant descriptor) = some descriptor ∧
      (Carbohydrate1996Foundation.descriptorForRingClosure?
          anomericLocant referenceLocant anomer =
        some (Carbohydrate1996Foundation.AnomerDescriptor.alphaBeta anomer) ↔
          anomericLocant < referenceLocant) :=
  ⟨rfl, descriptorForRingClosure?_alphaBeta_iff anomericLocant referenceLocant anomer⟩

/-! ## Reuse of the existing Fischer and Haworth convention cues -/

/-- A supplied anomer binding agrees with the existing Haworth convention carrier when the
carrier's ring-closure locants are the supplied anomeric/reference locants.  The equalities are
explicit binding data; this structure does not derive them. -/
structure HaworthAgreement {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    (ingress : AnomerIngress fragment) (carrier : HaworthCarrier V) : Prop where
  /-- The Haworth carbonyl locant is the supplied anomeric locant. -/
  anomeric_locant : carrier.closure.carbonylLocant = ingress.anomericLocant
  /-- The Haworth ring-hydroxy locant is the supplied reference locant. -/
  reference_locant : carrier.closure.hydroxyLocant = ingress.referenceLocant

/-- Reusing the existing Haworth cue path, the cue's non-atom indexes are exactly the supplied
anomeric and reference locants. -/
theorem haworthCue_locants {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    {ingress : AnomerIngress fragment} {carrier : HaworthCarrier V}
    (agreement : HaworthAgreement ingress carrier) :
    (HaworthCarrier.toCue carrier).locants =
      [ingress.anomericLocant, ingress.referenceLocant] := by
  rw [HaworthCarrier.toCue_locants, agreement.anomeric_locant, agreement.reference_locant]

/-- The existing relabelling theorem for Haworth cues leaves those locants unchanged. -/
theorem haworthCue_locants_relabel {V W : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    {ingress : AnomerIngress fragment} {carrier : HaworthCarrier V}
    (agreement : HaworthAgreement ingress carrier) (relabelling : V ≃ W) :
    (ConventionCue.mapAtom relabelling (HaworthCarrier.toCue carrier)).locants =
      [ingress.anomericLocant, ingress.referenceLocant] := by
  rw [ConventionCue.locants_mapAtom]
  exact haworthCue_locants agreement

/-- A supplied reference locant agrees with the existing Fischer convention carrier when the
carrier's chiral-centre locant is that reference locant. -/
structure FischerAgreement {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    (ingress : AnomerIngress fragment) (carrier : FischerCarrier V) : Prop where
  /-- The Fischer centre locant is the supplied reference locant. -/
  reference_locant : carrier.chiralCenter.locant = ingress.referenceLocant

/-- Reusing the existing Fischer cue path, the cue's non-atom index is exactly the supplied
reference locant. -/
theorem fischerCue_locants {V : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    {ingress : AnomerIngress fragment} {carrier : FischerCarrier V}
    (agreement : FischerAgreement ingress carrier) :
    (FischerCarrier.toCue carrier).locants = [ingress.referenceLocant] := by
  rw [FischerCarrier.toCue_locants, agreement.reference_locant]

/-- The existing relabelling theorem for Fischer cues leaves the reference locant unchanged. -/
theorem fischerCue_locants_relabel {V W : Type*} {n : ℕ} {fragment : ResidueFragment Nat n}
    {ingress : AnomerIngress fragment} {carrier : FischerCarrier V}
    (agreement : FischerAgreement ingress carrier) (relabelling : V ≃ W) :
    (ConventionCue.mapAtom relabelling (FischerCarrier.toCue carrier)).locants =
      [ingress.referenceLocant] := by
  rw [ConventionCue.locants_mapAtom]
  exact fischerCue_locants agreement

/-! ## Adapter from an actual certified source ledger -/

/-- Build the carbohydrate annotation for one residue of an actual residue-incidence ledger over
a certified authoritative chemical input.  The atom type is `Fin input...atomCount`, transported
to `V` by the supplied equivalence; each entry's anchors are the atoms resolved by the ledger's
actual residue incidence. -/
def annotationOfLedger {V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat)
    (entries : List (Entry (ledger.residue residueIndex))) : FragmentAnnotation V :=
  annotationOfEntries enumeration (ledger.residue residueIndex) cover entries

@[simp] theorem annotationOfLedger_support {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat) (entries : List (Entry (ledger.residue residueIndex))) :
    (annotationOfLedger enumeration ledger residueIndex cover entries).support =
      (ledger.residue residueIndex).support.map enumeration.toEmbedding := by
  simp [annotationOfLedger]

/-- Ledger anchors resolve through the actual ledger incidence function. -/
theorem annotationOfLedger_anomer_anchors {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (cover : List Nat) (entries : List (Entry (ledger.residue residueIndex)))
    {ingress : AnomerIngress (ledger.residue residueIndex)}
    (member : Entry.anomer ingress ∈ entries) :
    enumeration ingress.anomericAtom ∈
        (annotationOfLedger enumeration ledger residueIndex cover entries).support ∧
      enumeration ingress.referenceAtom ∈
        (annotationOfLedger enumeration ledger residueIndex cover entries).support ∧
      ledger.resolve? residueIndex ingress.anomericLocant = some ingress.anomericAtom ∧
      ledger.resolve? residueIndex ingress.referenceLocant = some ingress.referenceAtom := by
  have anchors := annotationOfEntries_anomer_anchors enumeration
    (ledger.residue residueIndex) cover entries member
  exact ⟨anchors.1, anchors.2, ingress.anomeric_eq, ingress.reference_eq⟩

/-- The same ledger binding expressed through the shared `resolveAnchor?` helper: the two
supplied locants resolve to exactly the two transported graph anchors.  This is the explicit
source-specific graph tie requested of the leaf, stated without assuming any inverse. -/
theorem annotationOfLedger_resolveAnchor?_anomer {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (_cover : List Nat) (entries : List (Entry (ledger.residue residueIndex)))
    {ingress : AnomerIngress (ledger.residue residueIndex)}
    (_member : Entry.anomer ingress ∈ entries) :
    resolveAnchor? enumeration.symm ledger residueIndex ingress.anomericLocant =
        some (enumeration ingress.anomericAtom) ∧
      resolveAnchor? enumeration.symm ledger residueIndex ingress.referenceLocant =
        some (enumeration ingress.referenceAtom) := by
  constructor
  · unfold resolveAnchor?
    rw [ResidueFragment.locate?_eq_incidence, ingress.anomeric_eq]
    simp [Equiv.symm_symm]
  · unfold resolveAnchor?
    rw [ResidueFragment.locate?_eq_incidence, ingress.reference_eq]
    simp [Equiv.symm_symm]

/-! ## Full canonical ledger channel with carbohydrate source data -/

/-- Bind supplied anomeric locants to a residue of an actual residue-incidence ledger.

The two witness equations are exact `ledger.resolve?` results.  Therefore the anchors are the
atoms that the ledger's actual residue incidence resolves, and the support obligations are
discharged by the shared incidence certificates; no atom is derived from raw geometry or from a
printed locant alone. -/
def ledgerAnomerIngress {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor)
    (anomericLocant referenceLocant : Nat)
    {anomericAtom referenceAtom : Fin input.input.molecule.atomCount}
    (anomeric_eq : ledger.resolve? residueIndex anomericLocant = some anomericAtom)
    (reference_eq : ledger.resolve? residueIndex referenceLocant = some referenceAtom) :
    AnomerIngress (ledger.residue residueIndex) where
  descriptor := descriptor
  anomericLocant := anomericLocant
  referenceLocant := referenceLocant
  anomericAtom := anomericAtom
  referenceAtom := referenceAtom
  anomeric_eq := anomeric_eq
  reference_eq := reference_eq

/-- The supplied locants of a ledger-derived binding are retained verbatim. -/
@[simp] theorem ledgerAnomerIngress_locants {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor)
    (anomericLocant referenceLocant : Nat)
    {anomericAtom referenceAtom : Fin input.input.molecule.atomCount}
    (anomeric_eq : ledger.resolve? residueIndex anomericLocant = some anomericAtom)
    (reference_eq : ledger.resolve? residueIndex referenceLocant = some referenceAtom) :
    (ledgerAnomerIngress ledger residueIndex descriptor anomericLocant referenceLocant
        anomeric_eq reference_eq).locants = ⟨anomericLocant, referenceLocant⟩ := rfl

/-- The ledger-derived binding resolves its two supplied locants exactly to the recorded atoms:
this is the actual source-to-graph tie. -/
theorem ledgerAnomerIngress_resolves {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (_descriptor : Carbohydrate1996Foundation.AnomerDescriptor)
    (anomericLocant referenceLocant : Nat)
    {anomericAtom referenceAtom : Fin input.input.molecule.atomCount}
    (anomeric_eq : ledger.resolve? residueIndex anomericLocant = some anomericAtom)
    (reference_eq : ledger.resolve? residueIndex referenceLocant = some referenceAtom) :
    ledger.resolve? residueIndex anomericLocant = some anomericAtom ∧
      ledger.resolve? residueIndex referenceLocant = some referenceAtom :=
  ⟨anomeric_eq, reference_eq⟩

/-- The shared datum of a ledger-derived anomeric entry carries exactly the resolved graph anchors
and the supplied locants; the atom relabelling is the only transformation. -/
theorem ledger_entry_datum_ties {V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input) (residueIndex : Fin ledger.residueCount)
    (descriptor : Carbohydrate1996Foundation.AnomerDescriptor)
    (anomericLocant referenceLocant : Nat)
    {anomericAtom referenceAtom : Fin input.input.molecule.atomCount}
    (anomeric_eq : ledger.resolve? residueIndex anomericLocant = some anomericAtom)
    (reference_eq : ledger.resolve? residueIndex referenceLocant = some referenceAtom) :
    datumAnchors? (Entry.datum enumeration
        (Entry.anomer (ledgerAnomerIngress ledger residueIndex descriptor anomericLocant
          referenceLocant anomeric_eq reference_eq))) =
      some (enumeration anomericAtom, enumeration referenceAtom) ∧
    datumAnomerLocants? (Entry.datum enumeration
        (Entry.anomer (ledgerAnomerIngress ledger residueIndex descriptor anomericLocant
          referenceLocant anomeric_eq reference_eq))) =
      some (anomericLocant, referenceLocant) ∧
    datumAnomerDescriptor? (Entry.datum enumeration
        (Entry.anomer (ledgerAnomerIngress ledger residueIndex descriptor anomericLocant
          referenceLocant anomeric_eq reference_eq))) = some descriptor :=
  ⟨rfl, rfl, rfl⟩

/-- Encode an actual residue-incidence ledger into the full canonical
`ResidueLedgerAnnotation`, attaching each residue's ordered carbohydrate source data through the
shared append operation.  The encoded fragment channel, links and hierarchy are exactly the
original ones; the source data ride alongside them. -/
def annotationWithCarbohydrate {V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (entries : ∀ index : Fin ledger.residueCount, List (Entry (ledger.residue index))) :
    ResidueLedgerAnnotation V ledger.residueCount
      input.input.molecule.interactions.length :=
  encodeWithSourceData LocantCodec.nat enumeration.symm ledger cover
    (fun index => entriesData enumeration (entries index))
    (by
      intro index datum member atom inReferences
      have supported :=
        entriesData_supported enumeration (entries index) datum member atom inReferences
      simpa [Equiv.symm_symm] using supported)

/-- The source-data list of every encoded residue is exactly the ordered entry datum list of that
residue: order, duplicates and multiplicity are retained by the full canonical channel. -/
@[simp] theorem annotationWithCarbohydrate_residue_sourceData {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (entries : ∀ index : Fin ledger.residueCount, List (Entry (ledger.residue index)))
    (index : Fin ledger.residueCount) :
    ((annotationWithCarbohydrate enumeration ledger cover entries).residue index).sourceData =
      entriesData enumeration (entries index) := by
  simp [annotationWithCarbohydrate]

/-- The full canonical channel recovers the atom-free ordered view of every residue, so the
original supplied values and locants are source-independent and recoverable after encoding. -/
theorem annotationWithCarbohydrate_view {V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (entries : ∀ index : Fin ledger.residueCount, List (Entry (ledger.residue index)))
    (index : Fin ledger.residueCount) :
    (((annotationWithCarbohydrate enumeration ledger cover entries).residue index).sourceData.filterMap
        datumView?) = (entries index).map Entry.view := by
  rw [annotationWithCarbohydrate_residue_sourceData]
  exact entriesData_view enumeration (entries index)

/-- The full canonical channel's encoded support is exactly the ledger residue support transported
by the supplied atom equivalence. -/
@[simp] theorem annotationWithCarbohydrate_residue_support {V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (enumeration : Fin input.input.molecule.atomCount ≃ V)
    (ledger : ResidueIncidenceLedger Nat input)
    (cover : Fin ledger.residueCount → List Nat)
    (entries : ∀ index : Fin ledger.residueCount, List (Entry (ledger.residue index)))
    (index : Fin ledger.residueCount) :
    ((annotationWithCarbohydrate enumeration ledger cover entries).residue index).support =
      (ledger.residue index).support.map enumeration.toEmbedding := by
  simp [annotationWithCarbohydrate, encodeFragment_support, Equiv.symm_symm]

end TetraStereo.OneCenter

/-! ## Kernel receipts -/

assert_kernel_only TetraStereo.OneCenter.AnomerIngress.anomeric_mem_support
assert_kernel_only TetraStereo.OneCenter.AnomerIngress.reference_mem_support
assert_kernel_only TetraStereo.OneCenter.Entry.datum_atomReferences_subset
assert_kernel_only TetraStereo.OneCenter.entriesData_supported
assert_kernel_only TetraStereo.OneCenter.annotationOfEntries_anomer_anchors
assert_kernel_only TetraStereo.OneCenter.annotationOfEntries_view
assert_kernel_only TetraStereo.OneCenter.annotationOfEntries_sourceData_get?
assert_kernel_only TetraStereo.OneCenter.annotationOfEntries_relabel
assert_kernel_only TetraStereo.OneCenter.annotationOfEntries_relabel_view
assert_kernel_only TetraStereo.OneCenter.rotation_series_sign_independent
assert_kernel_only TetraStereo.OneCenter.knowledge_states_pairwise_distinct
assert_kernel_only TetraStereo.OneCenter.anomerDescriptorFamily_eq
assert_kernel_only TetraStereo.OneCenter.descriptorForRingClosure?_eq
assert_kernel_only TetraStereo.OneCenter.descriptorForRingClosure?_alphaBeta_iff
assert_kernel_only TetraStereo.OneCenter.descriptorForRingClosure?_isSome_iff
assert_kernel_only TetraStereo.OneCenter.descriptorForRingClosure?_not_alphaBeta
assert_kernel_only TetraStereo.OneCenter.descriptorForRingClosure?_reverse_none
assert_kernel_only TetraStereo.OneCenter.datumAnomerDescriptor?_family
assert_kernel_only TetraStereo.OneCenter.datumAnomerDescriptor?_eq_of_supplied
assert_kernel_only TetraStereo.OneCenter.haworthCue_locants
assert_kernel_only TetraStereo.OneCenter.haworthCue_locants_relabel
assert_kernel_only TetraStereo.OneCenter.fischerCue_locants
assert_kernel_only TetraStereo.OneCenter.fischerCue_locants_relabel
assert_kernel_only TetraStereo.OneCenter.annotationOfLedger_anomer_anchors
assert_kernel_only TetraStereo.OneCenter.datumAnchors?_anomer
assert_kernel_only TetraStereo.OneCenter.datumAnomerLocants?_anomer
assert_kernel_only TetraStereo.OneCenter.datumAnomerDescriptor?_anomer
assert_kernel_only TetraStereo.OneCenter.annotationOfLedger_resolveAnchor?_anomer
assert_kernel_only TetraStereo.OneCenter.ledgerAnomerIngress_locants
assert_kernel_only TetraStereo.OneCenter.ledgerAnomerIngress_resolves
assert_kernel_only TetraStereo.OneCenter.ledger_entry_datum_ties
assert_kernel_only TetraStereo.OneCenter.annotationWithCarbohydrate_residue_sourceData
assert_kernel_only TetraStereo.OneCenter.annotationWithCarbohydrate_view
assert_kernel_only TetraStereo.OneCenter.annotationWithCarbohydrate_residue_support
