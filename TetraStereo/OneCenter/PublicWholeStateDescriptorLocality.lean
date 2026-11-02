import TetraStereo.OneCenter.PublicOutwardWholeStateKeyAgreement
import TetraStereo.OneCenter.PublicParametricRule3Through5Descriptor
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Whole-state read locality for the public Rule-3--5 descriptor

The public source-canonical Rule-3--5 descriptor is computed from the restricted dependency view
`aromaticCanonicalDependencyView state target`, which returns `none` at every occurrence that is not
a strict depth dependency of `target`.  The public *whole-state* reader
`aromaticCanonicalWholeStateReader state` returns `state` at every cursor with no restriction.

`PublicOutwardWholeStateKeyAgreement` proves, from the actual executable reroot geometry, that the
two readers agree on every cursor reachable outward from a strictly deeper child of the target and
that the whole parametric compound Rules-4a--5 builder therefore returns the *same whole `Option`
key* under both readers.  This module lifts that per-cursor key equality to the complete four-ligand
key frame and then to the complete descriptor, and instantiates the existing public unique-model
theorem.

## Main results

* `aromaticCanonicalOccurrenceFourLigandFrame?_roots_eq_rerootChildren` — the four-ligand frame
  actually produced by `aromaticCanonicalOccurrenceFourLigandFrame?` is exactly the executable
  child list of the target-start cursor.  This is what lets the outward geometry apply to every
  ligand root without any extra hypothesis about the frame.
* `buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot`
  and its `List.mapM` lift — at every ligand root whose address is strictly deeper than the target,
  the whole-state and restricted compound builds are equal as whole `Option`s, at every evaluation
  fuel, including the fail-closed `none` outcome.
* `buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_dependencyLabel_of_ligandRoots`
  — the two complete key frames are equal as whole `Option`s.  The Rule-3 half is the shipped
  reader-free canonical frame, so it is literally shared.
* `aromaticCanonicalFinalOccurrence_outward_ligandRoots` — at the final occurrence
  `aromaticCanonicalFinalOccurrence carrierFuel center` (address `[]`) every actual ligand root is
  strictly outward, so the strict-depth premise is automatic and no parent insulation is needed.
* `aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_wholeState_eq_spatialEvidence?_of_finalOccurrence`
  and
  `aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_finalOccurrence`
  — **full `Option` equality** of the spatial evidence and of the descriptor between the whole-state
  reader and the shipped restricted dependency-view production descriptor, at every evaluation fuel.
* `aromaticCanonicalOccurrenceRule3Through5Model_finalOccurrence_eq_descriptorWithRead?_of_finalOccurrence`
  — in the unique public Rule-3--5 model, the label stored at the final occurrence is exactly the
  whole-state descriptor computed there.
* `AromaticCanonicalOccurrenceRule3Through5FrameTieSeam` and
  `aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?_of_keyFrameTieSeam`
  — the weaker interface for the general internal target: a shared Rule-3 frame plus compound
  comparison equality **only on Rule-3 ties** already transports the complete descriptor as a whole
  `Option`.  No compound equality is demanded where Rule 3 decides, so a parent-side key may differ
  freely.

## Scope

Structural mathematics only.  The equalities are between the exact existing builders; no descriptor
value, ordering, chemical correctness or solver behaviour is assumed.  The public Rule-3 half is the
original-root total Rule-1b-profile construction with exact fresh `rootFromEdge` constitutional
endpoints and tie refusal; it is not the localized extended Rule-3 algorithm and no localized Rule-3
recursion is transported here.  The general internal-target case (a ligand frame containing the
parent root) is *not* claimed unconditionally: the module provides the exact weaker transport
`..._of_internalTarget_ties`, whose only remaining premise is the tied-pair compound comparison
condition, i.e. the parent/outward Rule-3 constitutional separation; discharging it is explicit
residual work.  Equality and locality of the reader are not a statement of complete chemistry.
-/

/-! ## The four-ligand frame is the executable child list -/

/-- The ordered list returned by `aromaticCanonicalOccurrenceLigandFrame?` is exactly the executable
zipper expansion of the target-start cursor.  The underlying computation is the same total function;
this records the orientation needed below. -/
theorem aromaticCanonicalOccurrenceLigandFrame?_eq_rerootChildren
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (occurrence : source.AromaticCanonicalOccurrence carrierFuel)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (computed : source.aromaticCanonicalOccurrenceLigandFrame? occurrence = some roots) :
    roots = source.aromaticCanonicalRerootChildren
      { occurrence := occurrence, previous? := none } := by
  have exactChildren : source.aromaticCanonicalRerootChildren
      { occurrence := occurrence, previous? := none } = roots := by
    simpa [aromaticCanonicalOccurrenceLigandFrame?, aromaticCanonicalRerootChildren?]
      using computed
  exact exactChildren.symm

/-- The roots stored in a four-ligand frame are exactly the executable children of the
target-start cursor.  Consequently every geometric fact proved for executable children applies to
every ligand root with no additional frame hypothesis. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame?_roots_eq_rerootChildren
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base) :
    base.roots = source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } := by
  have derived : source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } base.roots :=
    (source.aromaticCanonicalOccurrenceFourLigandFrame?_sound target base computed).1
  have someComputed : source.aromaticCanonicalRerootChildren?
      { occurrence := target, previous? := none } = some base.roots :=
    (source.aromaticCanonicalRerootChildren?_eq_some_iff
      { occurrence := target, previous? := none } base.roots).mpr derived
  have childrenEq : source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } = base.roots := by
    simpa [aromaticCanonicalRerootChildren?] using someComputed
  exact childrenEq.symm

/-- Membership form of the frame/children identification. -/
theorem aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel) (present : cursor ∈ base.roots) :
    cursor ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } := by
  rw [← source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_eq_rerootChildren
    target base computed]
  exact present

/-! ## Reader equality on the ligand roots -/

/-- Pointwise lift of the per-cursor outward whole-state equality through `List.mapM`.  Membership
is enough because `mapM` only applies the builder to list members. -/
private theorem list_mapM_congr_on
    {α β : Type*} (first second : α → Option β) :
    ∀ values : List α,
      (∀ value, value ∈ values → first value = second value) →
      values.mapM first = values.mapM second
  | [], _ => rfl
  | value :: values, agrees => by
      simp [List.mapM_cons, agrees value (by simp),
        list_mapM_congr_on first second values
          (fun member memberPresent => agrees member (by simp [memberPresent]))]

/-- At one ligand root that is an actual child of the target-start cursor and strictly deeper than
the target, the whole-state compound Rules-4a--5 build equals the restricted dependency-label build
as a **whole `Option`**, at every evaluation fuel. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (cursorChild : cursor ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (deeper : target.1.address.length < cursor.occurrence.1.address.length) :
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        (source.aromaticCanonicalWholeStateReader state) fuel cursor =
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        (fun next => source.aromaticCanonicalDependencyLabel target
          (source.aromaticCanonicalDependencyView state target) next) fuel cursor := by
  calc
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        (source.aromaticCanonicalWholeStateReader state) fuel cursor =
        source.buildAromaticCanonicalRerootCompoundRule45Key? target
          (source.aromaticCanonicalDependencyView state target) fuel cursor :=
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
        target state cursor cursor cursorChild deeper Relation.ReflTransGen.refl fuel
    _ = source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
          (fun next => source.aromaticCanonicalDependencyLabel target
            (source.aromaticCanonicalDependencyView state target) next) fuel cursor :=
      (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
        target (source.aromaticCanonicalDependencyView state target) fuel cursor).symm

/-- The complete Rule-3--5 key frame is equal as a whole `Option` under the whole-state reader and
the restricted dependency-label reader, provided every cursor of the list is an actual child of the
target-start cursor and strictly deeper than the target.  The Rule-3 component is the shipped
reader-free canonical frame, so it is literally shared. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_dependencyLabel_of_ligandRoots
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (children : ∀ cursor, cursor ∈ cursors → cursor ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (deeper : ∀ cursor, cursor ∈ cursors →
      target.1.address.length < cursor.occurrence.1.address.length) :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (source.aromaticCanonicalWholeStateReader state) ruleFuel cursors =
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (fun next => source.aromaticCanonicalDependencyLabel target
          (source.aromaticCanonicalDependencyView state target) next) ruleFuel cursors := by
  unfold buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
  have mapEq : cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
          (source.aromaticCanonicalWholeStateReader state) ruleFuel) =
      cursors.mapM
        (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
          (fun next => source.aromaticCanonicalDependencyLabel target
            (source.aromaticCanonicalDependencyView state target) next) ruleFuel) :=
    list_mapM_congr_on _ _ cursors fun cursor present =>
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
        target state ruleFuel cursor (children cursor present) (deeper cursor present)
  simp only [mapEq]

/-- The whole-state frame equals the shipped restricted production frame at the same fuel and
cursors, under the same strict-depth premise. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_rule3Through5KeyFrame?_of_ligandRoots
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (children : ∀ cursor, cursor ∈ cursors → cursor ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (deeper : ∀ cursor, cursor ∈ cursors →
      target.1.address.length < cursor.occurrence.1.address.length) :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (source.aromaticCanonicalWholeStateReader state) ruleFuel cursors =
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target (source.aromaticCanonicalDependencyView state target) ruleFuel cursors := by
  rw [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_dependencyLabel_of_ligandRoots
    target state ruleFuel cursors children deeper]
  exact source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
    target (source.aromaticCanonicalDependencyView state target) ruleFuel cursors

/-! ## The final root occurrence: every ligand root is outward -/

/-- At the final occurrence the target address is `[]`, so no parent coordinate exists in the
four-ligand frame: every actual ligand root is a strictly deeper child of the target-start cursor. -/
theorem aromaticCanonicalFinalOccurrence_ligandRoot_deeper
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some base) :
    ∀ cursor, cursor ∈ base.roots →
      (source.aromaticCanonicalFinalOccurrence carrierFuel center).1.address.length <
        cursor.occurrence.1.address.length := by
  intro cursor present
  have inChildren : cursor ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none } :=
    source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) base computed cursor present
  exact (source.aromaticCanonicalFinalOccurrence_outward_first center cursor inChildren).2.1.2

/-- **Final-root key-frame equality.**  For the four-ligand frame of the final occurrence
`aromaticCanonicalFinalOccurrence carrierFuel center` the whole-state frame and the shipped
restricted production frame are equal as whole `Option`s at every evaluation fuel, with no
parent-insulation or availability hypothesis. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_rule3Through5KeyFrame?_of_finalOccurrence
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (computed : source.aromaticCanonicalOccurrenceFourLigandFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some base) :
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (source.aromaticCanonicalWholeStateReader state) ruleFuel base.roots =
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel base.roots :=
  source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_rule3Through5KeyFrame?_of_ligandRoots
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) state ruleFuel base.roots
    (fun cursor present =>
      source.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) base computed cursor present)
    (source.aromaticCanonicalFinalOccurrence_ligandRoot_deeper center base computed)

/-! ## Full `Option` evidence and descriptor equality -/

/-- **Final-root spatial-evidence equality.**  The spatial evidence produced under the whole-state
reader and under the shipped restricted dependency-view builder are equal as whole `Option`s at
every evaluation fuel.  Center and base perception, the tracked sorter, the pseudo-comparison count
and the exact point read are reader-independent; only the inner key frame differs, and it is
transported by the previous theorem. -/
theorem aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_wholeState_eq_spatialEvidence?_of_finalOccurrence
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat) :
    source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
        (source.aromaticCanonicalWholeStateReader state)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) ruleFuel =
      source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel := by
  unfold aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
    aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
  cases centerComputed :
      source.aromaticCanonicalOccurrenceTetrahedralCenter?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) with
  | none => simp
  | some perceivedCenter =>
      simp
      cases baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame?
          (source.aromaticCanonicalFinalOccurrence carrierFuel center) with
      | none => simp
      | some base =>
          simp
          rw [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_rule3Through5KeyFrame?_of_finalOccurrence
            center state ruleFuel base baseComputed]

/-- **Final-root descriptor equality.**  The whole-state Rule-3--5 descriptor at the final
occurrence equals the shipped restricted dependency-view descriptor as a **whole `Option`**, at
every evaluation fuel.  In particular the fail-closed `none` outcomes coincide and, on success, the
two classified labels are identical. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_finalOccurrence
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) ruleFuel =
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel := by
  unfold aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
    aromaticCanonicalOccurrenceRule3Through5Descriptor?
  rw [source.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_wholeState_eq_spatialEvidence?_of_finalOccurrence
    center state ruleFuel]

/-- Outcome form: the whole-state and restricted final-occurrence descriptors accept exactly the
same labels. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_some_iff_of_finalOccurrence
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat) (descriptor : AromaticCanonicalAuxiliaryLabel) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) ruleFuel =
        some descriptor ↔
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel =
        some descriptor := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_finalOccurrence
    center state ruleFuel]

/-- Success/failure form: both descriptors are defined exactly together. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_isSome_eq_of_finalOccurrence
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat) :
    (source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) ruleFuel).isSome =
      (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel).isSome := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_finalOccurrence
    center state ruleFuel]

/-! ## Instantiation in the unique public Rule-3--5 model -/

/-- **Model locality at the final root.**  In the unique public Rule-3--5 model the stored label at
the final occurrence is exactly the whole-state descriptor computed there.  This composes the
descriptor equality with the existing canonical model characterization; it introduces no second
model wrapper and no additional semantics. -/
theorem aromaticCanonicalOccurrenceRule3Through5Model_finalOccurrence_eq_descriptorWithRead?_of_finalOccurrence
    (source : AuthoritativeChemicalInput) {carrierFuel ruleFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).CIPModel state) :
    state (source.aromaticCanonicalFinalOccurrence carrierFuel center) =
      source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) ruleFuel := by
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let view := source.aromaticCanonicalDependencyView state target
  have locality :=
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_finalOccurrence
      center state ruleFuel
  have modelIff : ∀ descriptor,
      state target = some descriptor ↔
        source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target view ruleFuel =
          some descriptor := by
    intro descriptor
    rw [source.aromaticCanonicalOccurrenceRule3Through5Model_eq_some_iff_canonical
      state model target descriptor]
    exact (source.aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
      target view ruleFuel descriptor).symm
  rw [locality]
  cases restricted : source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
      target view ruleFuel with
  | none =>
      cases stored : state target with
      | none => rfl
      | some descriptor =>
          have accepted := (modelIff descriptor).mp stored
          rw [restricted] at accepted
          cases accepted
  | some descriptor =>
      exact (modelIff descriptor).mpr restricted

/-- Outcome form of the model corollary: the model stores exactly the whole-state descriptor's
label, with the same success/failure behaviour. -/
theorem aromaticCanonicalOccurrenceRule3Through5Model_finalOccurrence_eq_some_iff_of_finalOccurrence
    (source : AuthoritativeChemicalInput) {carrierFuel ruleFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (model : (source.aromaticCanonicalOccurrenceSystem
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)).CIPModel state)
    (descriptor : AromaticCanonicalAuxiliaryLabel) :
    state (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some descriptor ↔
      source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state)
        (source.aromaticCanonicalFinalOccurrence carrierFuel center) ruleFuel =
        some descriptor := by
  rw [source.aromaticCanonicalOccurrenceRule3Through5Model_finalOccurrence_eq_descriptorWithRead?_of_finalOccurrence
    center state model]

/-! ## Weaker transport: compound equality only on Rule-3 ties

The final-root results above transport the complete compound keys.  For a general internal target
the parent ligand is not a strict dependency, so its compound key may differ between the whole-state
and restricted readers.  That difference is nevertheless invisible to the comparator whenever the
reader-free Rule-3 comparison of the pair is already decisive: `compareAromaticCanonicalOccurrence
Rule3Through5At` then ignores the compound records entirely.  The interface below records exactly
that weaker premise.  It is a genuine hypothesis on actual comparison records; no descriptor
equality is assumed.
-/

/-- Two actual frames whose Rule-3 half is literally shared and whose compound through-Rule-5
comparison records agree **only on pairs that the shared Rule-3 comparison leaves tied**.  This is
strictly weaker than `AromaticCanonicalOccurrenceRule3Through5FrameSeam`. -/
structure AromaticCanonicalOccurrenceRule3Through5FrameTieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel) :
    Prop where
  /-- The actual Rule-3 canonical frame is literally shared. -/
  sharedRule3Frame : left.rule3Frame = right.rule3Frame
  /-- The direct compound comparison records agree on every pair whose shared Rule-3 comparison is
  a tie.  No condition is imposed where Rule 3 already decides the order. -/
  rule45PairComparisonsOnTies : ∀ (leftIndex rightIndex : Fin 4),
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (left.keyAt leftIndex).rule3 (left.keyAt rightIndex).rule3 = Ordering.eq →
    source.compareAromaticCanonicalRerootCompoundThroughRule5
        (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45 =
      source.compareAromaticCanonicalRerootCompoundThroughRule5
        (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45

/-- A strong frame seam is a tie seam: pairwise compound equality implies equality on the tied
pairs.  This is the only direction needed; the converse does not hold. -/
theorem AromaticCanonicalOccurrenceRule3Through5FrameTieSeam.of_frameSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameSeam left right) :
    source.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam left right :=
  ⟨seam.sharedRule3Frame, fun leftIndex rightIndex _ =>
    seam.rule45PairComparisons leftIndex rightIndex⟩

/-- The two builders consume the same reader-free Rule-3 computation, so any two successful frames
built at the same fuel on the same cursor list have literally the same Rule-3 canonical frame. -/
theorem buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_eq_of_both_some
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (leftComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some left)
    (rightComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel cursors = some right) :
    left.rule3Frame = right.rule3Frame := by
  have rightWithRead :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
        fuel cursors = some right := by
    rw [source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_eq_rule3Through5KeyFrame?
      target view fuel cursors]
    exact rightComputed
  have leftRule3 :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame
      read fuel cursors left leftComputed
  have rightRule3 :=
    source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame
      (fun cursor => source.aromaticCanonicalDependencyLabel target view cursor)
      fuel cursors right rightWithRead
  exact Option.some.inj (leftRule3.symm.trans rightRule3)

/-- Build the tie seam from the two actual successful builds.  The shared Rule-3 frame is derived
from determinism of the reader-free pass; only the tied-pair compound comparison condition has to
be supplied.  This is the constructor a general internal-target proof should target: it removes the
shared-Rule-3 obligation and leaves exactly the parent/outward Rule-3 separation. -/
theorem AromaticCanonicalOccurrenceRule3Through5FrameTieSeam.of_computations
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (cursors : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (leftComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
      read fuel cursors = some left)
    (rightComputed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel cursors = some right)
    (ties : ∀ (leftIndex rightIndex : Fin 4),
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (left.keyAt leftIndex).rule3 (left.keyAt rightIndex).rule3 = Ordering.eq →
      source.compareAromaticCanonicalRerootCompoundThroughRule5
          (left.keyAt leftIndex).rule45 (left.keyAt rightIndex).rule45 =
        source.compareAromaticCanonicalRerootCompoundThroughRule5
          (right.keyAt leftIndex).rule45 (right.keyAt rightIndex).rule45) :
    source.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam left right :=
  ⟨source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_eq_of_both_some
      read target view fuel cursors left right leftComputed rightComputed, ties⟩

/-- Actual frame comparison transport from the tie seam.  Where Rule 3 decides, both sides return
the same strict record; where it ties, the hypothesis supplies the compound record equality. -/
theorem compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_tieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam left right)
    (leftIndex rightIndex : Fin 4) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At left leftIndex rightIndex =
      source.compareAromaticCanonicalOccurrenceRule3Through5At right
        leftIndex rightIndex := by
  unfold compareAromaticCanonicalOccurrenceRule3Through5At
  dsimp only
  rw [← AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      seam.sharedRule3Frame leftIndex,
    ← AromaticCanonicalOccurrenceRule3Through5KeyFrame.keyAt_rule3_eq_of_rule3Frame_eq
      seam.sharedRule3Frame rightIndex]
  generalize rule3Comparison :
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (left.keyAt leftIndex).rule3 (left.keyAt rightIndex).rule3 = outcome
  cases outcome
  · simp [rule3Comparison]
  · simp [rule3Comparison,
      seam.rule45PairComparisonsOnTies leftIndex rightIndex rule3Comparison]
  · simp [rule3Comparison]

/-- The exact tracked sorter, including the pseudo-comparison count, transports along the tie
seam. -/
theorem safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam left right) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? left =
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? right :=
  source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_compare right left
    (fun leftIndex rightIndex =>
      source.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_tieSeam
        seam leftIndex rightIndex)

/-- Descriptor transport on the same four-ligand base from the tie seam.  The priority-ordered
coordinates are read from the shared base, so only the tracked order has to transport. -/
theorem aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_of_tieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {left right : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel}
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam left right)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel) :
    source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? left base =
      source.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor? right base := by
  unfold aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?
  rw [source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam seam]

/-- **Conditional descriptor transport for an arbitrary reader.**  If the whole arbitrary-reader
descriptor build and the shipped restricted build succeed on the same four-ligand base and their
key frames are related by the tie seam, then the two descriptors are equal as **whole `Option`s**.
This is the weak transport interface requested for the general internal-target route: no compound
equality is required on pairs that Rule 3 decides, and no descriptor value is assumed. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?_of_keyFrameTieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (view : source.AromaticCanonicalDependencyView target)
    (ruleFuel : Nat)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (wholeFrame restrictedFrame :
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (wholeComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        read ruleFuel base.roots = some wholeFrame)
    (restrictedComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target view ruleFuel base.roots = some restrictedFrame)
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam
      wholeFrame restrictedFrame) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        read target ruleFuel =
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor? target view ruleFuel := by
  unfold aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
    aromaticCanonicalOccurrenceRule3Through5Descriptor?
    aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?
    aromaticCanonicalOccurrenceRule3Through5SpatialEvidence?
  rw [baseComputed]
  simp
  rw [wholeComputed, restrictedComputed]
  simp
  rw [source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam seam]
  -- The two evidence records now differ only in their `keys` field, which the descriptor
  -- routine never reads: it projects `points` and `tracked.pseudoComparisons` only.
  cases centerC : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp
  | some perceivedCenter =>
      simp
      cases trackedC :
          source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? restrictedFrame with
      | none => simp
      | some tracked =>
          simp
          repeat rw [Option.bind_assoc]
          rfl

/-- Whole-state specialization of the conditional transport: the only remaining premise for a
general internal target is the tie seam between the two actual key frames. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (wholeFrame restrictedFrame :
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (wholeComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (source.aromaticCanonicalWholeStateReader state) ruleFuel base.roots =
          some wholeFrame)
    (restrictedComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target (source.aromaticCanonicalDependencyView state target) ruleFuel base.roots =
          some restrictedFrame)
    (seam : source.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam
      wholeFrame restrictedFrame) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target ruleFuel =
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView state target) ruleFuel :=
  source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?_of_keyFrameTieSeam
    target (source.aromaticCanonicalWholeStateReader state)
    (source.aromaticCanonicalDependencyView state target) ruleFuel base baseComputed
    wholeFrame restrictedFrame wholeComputed restrictedComputed seam

/-- **Internal-target endpoint, conditional on the Rule-3 tie classification.**  For an arbitrary
target (in particular a non-root internal target with a parent ligand in its four-ligand frame),
the whole-state and restricted descriptors are equal as whole `Option`s once the compound
comparison records agree on the pairs that the reader-free Rule-3 comparison leaves tied.  The
shared Rule-3 frame is derived, not assumed.  At a general internal target the only remaining
obligation is the geometric fact that every parent/outward ligand pair is already decided by
Rule 3; the outward/outward pairs are covered by the shipped whole-state agreement. -/
theorem aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_internalTarget_ties
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (ruleFuel : Nat)
    (base : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (baseComputed : source.aromaticCanonicalOccurrenceFourLigandFrame? target = some base)
    (wholeFrame restrictedFrame :
      source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (wholeComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?
        (source.aromaticCanonicalWholeStateReader state) ruleFuel base.roots =
          some wholeFrame)
    (restrictedComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
        target (source.aromaticCanonicalDependencyView state target) ruleFuel base.roots =
          some restrictedFrame)
    (ties : ∀ (leftIndex rightIndex : Fin 4),
      source.compareAromaticCanonicalUncancelledRule3SpatialKeys
          (wholeFrame.keyAt leftIndex).rule3 (wholeFrame.keyAt rightIndex).rule3 =
            Ordering.eq →
      source.compareAromaticCanonicalRerootCompoundThroughRule5
          (wholeFrame.keyAt leftIndex).rule45 (wholeFrame.keyAt rightIndex).rule45 =
        source.compareAromaticCanonicalRerootCompoundThroughRule5
          (restrictedFrame.keyAt leftIndex).rule45
          (restrictedFrame.keyAt rightIndex).rule45) :
    source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?
        (source.aromaticCanonicalWholeStateReader state) target ruleFuel =
      source.aromaticCanonicalOccurrenceRule3Through5Descriptor?
        target (source.aromaticCanonicalDependencyView state target) ruleFuel :=
  source.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
    target state ruleFuel base baseComputed wholeFrame restrictedFrame
    wholeComputed restrictedComputed
    (AromaticCanonicalOccurrenceRule3Through5FrameTieSeam.of_computations
      source (source.aromaticCanonicalWholeStateReader state) target
      (source.aromaticCanonicalDependencyView state target) ruleFuel base.roots
      wholeFrame restrictedFrame wholeComputed restrictedComputed ties)

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

Every public declaration introduced by this module is guarded.  `assert_kernel_only` permits
exactly `propext`, `Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and
native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceLigandFrame?_eq_rerootChildren
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame?_roots_eq_rerootChildren
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceFourLigandFrame?_roots_mem_rerootChildren
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_dependencyLabel_of_ligandRoot
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_dependencyLabel_of_ligandRoots
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_rule3Through5KeyFrame?_of_ligandRoots
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalFinalOccurrence_ligandRoot_deeper
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_wholeState_eq_rule3Through5KeyFrame?_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5SpatialEvidenceWithRead?_wholeState_eq_spatialEvidence?_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_some_iff_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_isSome_eq_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5Model_finalOccurrence_eq_descriptorWithRead?_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5Model_finalOccurrence_eq_some_iff_of_finalOccurrence
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam.of_frameSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalOccurrenceRule3Through5At_eq_of_tieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?_eq_of_tieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5FrameDescriptor?_eq_of_tieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_eq_descriptor?_of_keyFrameTieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_keyFrameTieSeam
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalOccurrenceRule3Through5KeyFrameWithRead?_rule3Frame_eq_of_both_some
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOccurrenceRule3Through5FrameTieSeam.of_computations
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOccurrenceRule3Through5DescriptorWithRead?_wholeState_eq_descriptor?_of_internalTarget_ties
