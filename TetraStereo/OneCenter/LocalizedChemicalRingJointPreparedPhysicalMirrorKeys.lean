import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorBranchExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent
import TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus
import TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingRelabel
import TetraStereo.OneCenter.LocalizedRetainedCoherentSymmetry
import TetraStereo.OneCenter.DeclarativeCIPBoundaryComponentReconstruction
import TetraStereo.OneCenter.LocalizedMarkedReachedFrameNeighbors
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
# Actual prepared-label covariance from an independent physical mirror transport

The exclusive gap of this module is the original-root arm direction: an independently supplied
`RootedTetrahedralBranchSymmetry.MirrorTransport` at the root slots is converted into exact
optional prepared-label equality for every actual queried occurrence in the source ligand branch
and its `e`-image under the mirrored geometry.  The labels are read from the concrete
`LocalizedChemicalRingJointPreparedExecution.generated` prepared states.  No reader/fact
correspondence, sorted-order success, acyclicity, reference-count, desired-label, or label
correctness assumption is made.  Refusal is included: both sides may be `none`.

The physical descriptor core is supplied by
`LocalizedChemicalRingJointPreparedMirrorBranchExecution.descriptor_map_mirror_eq`; this module
derives the actual query from a residual observation path, feeds the label-execution bridge on
both sides, and therefore does not duplicate that core.  The remaining retained-key comparison
is stated separately in the report as a common-layout consumer obligation.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointPreparedLabelExecution (generated_label_eq_descriptor)
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedChemicalRingJointPreparedRootWitness (root_slot_data)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedChemicalRingRelabel (mapNode mapNode_canonicalCenterRoot mapNode_history
  mem_children_map)
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedChemicalRingSemanticSymmetry (structuralSymmetry_of_aut)
open LocalizedChemicalRingJointPreparedMirrorBranchExecution (descriptor_map_mirror_eq)
open RootedTetrahedralBranchSymmetry (MirrorTransport BranchTransport LigandBranchReaches
  centerPerm_eq_iff ligandAtomAt_ne_center)
open LocalizedMarkedReachableConfigurations (Reached reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends StrictDescendant descendant_reached)
open LocalizedMarkedReachedFrameNeighbors (SingleBonded reached_atom_valid)
open LocalizedGenericMarkedRecalculation (Geometry structuralDepth mirror frameAtoms?)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap factLabel)
open LocalizedChemicalRingJointMarkerRanking (frames)
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open RetainedCoherentSymmetry (ResidualObsPath InComponent)
open TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution
open TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedLabelExecution
open TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootInput
open TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport
open TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness
open TetraStereo.OneCenter.LocalizedChemicalRingWitnessRawDescent
open TetraStereo.OneCenter.LocalizedChemicalRingBoundaryWitnessFactMatch
open TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch
open TetraStereo.OneCenter.LocalizedChemicalRingRelabel
open TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
open TetraStereo.OneCenter.LocalizedChemicalRingSemanticSymmetry
open TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedMirrorBranchExecution
open TetraStereo.OneCenter.BoundaryComponentReconstruction

noncomputable section
open scoped Classical

abbrev Node := RawMolecule.CanonicalBranchNode

/-! ## Generic prepared-state and relabelling facts -/

/-- The actual prepared descriptor refuses before inspecting child facts when the query has no
four-ligand frame.  This is the `preparedDescriptor?` form of the concrete step's no-frame
refusal. -/
theorem preparedDescriptor?_none_of_frame (mol : RawMolecule)
    (ops : LocalizedChemicalRingMultiMarkRecursion.MultiOperations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (M : MarkContext) (node : Node)
    (frame : frameAtoms? mol node = none) :
    preparedDescriptor? mol ops depth geom state M node = none := by
  unfold preparedDescriptor? descriptorOfStep
  exact descriptorWithPrepared_none_of_frame (rawStepPrepared? ops) mol
    (rawStepPrepared?_noFrame ops) geom state M node
    (factsOfStep (rawStepPrepared? ops) mol depth) frame

/-- Relabelling preserves an actual canonical descent. -/
theorem descends_map {mol : RawMolecule} {σ : Nat → Nat}
    (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    {source target : Node} (path : Descends mol source target) :
    Descends mol (mapNode σ source) (mapNode σ target) := by
  induction path with
  | refl => exact .refl
  | tail path edge ih =>
      exact ih.tail (mem_children_map sym wellFormed unique single _ _ edge)

/-- Relabelling preserves the strict-descendant relation. -/
theorem strictDescendant_map {mol : RawMolecule} {σ : Nat → Nat}
    (sym : StructuralSymmetry mol σ) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (single : SingleBonded mol)
    {source target : Node} (path : StrictDescendant mol source target) :
    StrictDescendant mol (mapNode σ source) (mapNode σ target) := by
  obtain ⟨child, edge, rest⟩ := path
  exact ⟨mapNode σ child, mem_children_map sym wellFormed unique single source child edge,
    descends_map sym wellFormed unique single rest⟩

/-- A strict descendant is a reached occurrence. -/
theorem strictDescendant_reached {mol : RawMolecule} {source target : Node}
    (reached : Reached mol source) (path : StrictDescendant mol source target) :
    Reached mol target := by
  obtain ⟨child, edge, rest⟩ := path
  exact descendant_reached (reached_child mol source child reached edge) rest

/-- The endpoint atom of a nonempty residual witness is exactly the atom of its complete
root-history query. -/
theorem rawPathNode_boundaryPath_atom {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (p : List input.Atom)
    (d : input.Atom) (last : p.getLast? = some d) :
    (rawPathNode target.1.root (boundaryPath target p)).atom = d.val := by
  have nonempty : p ≠ [] := by
    intro empty
    rw [empty] at last
    cases last
  have appended : (boundaryPath target p).getLast? = some d := by
    unfold boundaryPath
    rw [List.getLast?_append_of_ne_nil _ nonempty, last]
  unfold rawPathNode
  simp only
  rw [appended]
  rfl

/-- The nat MarkContext generated by the `e`-image references is the relabelled original
MarkContext. -/
theorem map_references_relabel (input : CertifiedLocalizedCIPInput)
    (e : input.detectedMultiCenterMolecule.Aut) (references : List input.Atom) :
    (references.map (e : Equiv.Perm input.Atom)).map Fin.val =
      (references.map Fin.val).map (relabelOf input (e : Equiv.Perm input.Atom)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro a _
  exact (relabelOf_val input (e : Equiv.Perm input.Atom) a).symm

/-- A last element returned by `getLast?` is a member. -/
theorem mem_of_getLast?_eq_some {α : Type*} {l : List α} {a : α}
    (last : l.getLast? = some a) : a ∈ l := by
  induction l with
  | nil => cases last
  | cons head tail ih =>
      cases tail with
      | nil =>
          have same : head = a := Option.some.inj (by simpa using last)
          rw [← same]
          simp
      | cons second rest =>
          have restLast : (second :: rest).getLast? = some a := by
            simpa using last
          exact List.mem_cons_of_mem head (ih restLast)

/-! ## Actual prepared-label covariance at every residual root-branch query -/

/-- **Actual generated-label covariance from an independent physical mirror transport.**

At an actual root occurrence (`address = []`, node `canonicalCenterRoot c`) of an admitted,
intake-agreeing, simple-bonded molecule, suppose the actual ligand slots `left` and `right`
are related by a `MirrorTransport` of the independent physical branch symmetry.  Let `p` be an
actual residual observation path in the component of the `left` ligand after deleting `[c.1]`,
and let `d` be its last atom, a detected center.  Then the exact optional prepared label read
at the complete raw query `rawPathNode target.root (boundaryPath target p)` on the original
geometry equals the exact optional prepared label read at its `e`-image on the mirrored
geometry, with the image reference list transported by `e`.  Both sides may refuse (`none`).

No reader/fact correspondence, sorting success, acyclicity, reference-count, desired-label or
label-correctness premise is used.  The only cross-side premise is the supplied physical
`MirrorTransport`; the only source-side branch premise is the actual residual path `p` and its
terminal detected center `d`. -/
theorem generated_label_eq_of_physicalMirror
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
    (rootAddress : data.target.1.address = [])
    (left : Fin 4) (e : input.detectedMultiCenterMolecule.Aut)
    (centerFixed : input.detectedMultiCenterMolecule.centerPerm e c = c)
    (physical : ∀ other : input.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.detectedMultiCenterMolecule c (data.ligandOf left) other.1 →
        input.detectedMultiCenterMolecule.configurationSign cfg other *
          permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e other) =
        (-1 : ℝ) * input.detectedMultiCenterMolecule.configurationSign cfg
          (input.detectedMultiCenterMolecule.centerPerm e other))
    (references : List input.Atom)
    (p : List input.Atom) (d : input.detectedMultiCenterMolecule.Center)
    (valid : ResidualObsPath input.moleculeGraph [c.1]
      (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) p)
    (last : p.getLast? = some d.1) :
    ((generated input mol (structuralDepth mol (canonicalCenterRoot c.1.val))
          (inputGeometry input) (canonicalCenterRoot c.1.val) references).factAt?
          (rawPathNode data.target.1.root (boundaryPath data.target p))).map factLabel =
        ((generated input mol (structuralDepth mol (canonicalCenterRoot c.1.val))
          (mirror (inputGeometry input)) (canonicalCenterRoot c.1.val)
          (references.map (e : Equiv.Perm input.Atom))).factAt?
          (mapNode (relabelOf input (e : Equiv.Perm input.Atom))
            (rawPathNode data.target.1.root (boundaryPath data.target p)))).map factLabel := by
  let σ : Nat → Nat := relabelOf input (e : Equiv.Perm input.Atom)
  let q : Node := rawPathNode data.target.1.root (boundaryPath data.target p)
  have wf : mol.WellFormed := admissible.1.1
  have unique : mol.BondRecordsUnique := admissible.1.2
  have rawSingle : SingleBonded mol :=
    raw_single mol input agreement wf unique supported single
  have history : data.target.1.node.history = [c.1] :=
    root_history input mol c (canonicalCenterRoot c.1.val) data rootAddress rfl
  have validHistory : ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse
      (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) p := by
    rw [history]
    simpa using valid
  have dmem : d.1 ∈ p := mem_of_getLast?_eq_some last
  have fresh : referenceAt input mol c (canonicalCenterRoot c.1.val) data left ∉
      data.target.1.node.history := by
    rw [history]
    intro member
    exact ligandAtomAt_ne_center input.detectedMultiCenterMolecule c (data.ligandOf left)
      (by simpa only [referenceAt] using List.mem_singleton.mp member)
  have currentL := slot_current input mol single c (canonicalCenterRoot c.1.val) data
    ([] : OccurrenceAuxState) left
  obtain ⟨realL, _rootL, _slotL, _addressL⟩ := root_slot_data input single
    (rawStateDescriptorMap input ([] : OccurrenceAuxState)) data.target
    (frames input single ([] : OccurrenceAuxState) data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl)
    rootAddress left (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) currentL
  obtain ⟨child, edge, _atomEq, childReal, descent⟩ :=
    actual_fresh_boundary_path_descent input mol agreement admissible supported single
      (canonicalCenterRoot c.1.val) (root_reached input mol agreement c)
      ([] : OccurrenceAuxState) data.target data.found data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left
      (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) currentL realL
      fresh p validHistory
  have sourceStrict : StrictDescendant mol (canonicalCenterRoot c.1.val) q :=
    ⟨child, edge, descent⟩
  have rootReached : Reached mol (canonicalCenterRoot c.1.val) :=
    root_reached input mol agreement c
  have qReached : Reached mol q := strictDescendant_reached rootReached sourceStrict
  have qValid : q.atom < mol.atomCount := reached_atom_valid mol wf q qReached
  have qHistory : q.history = (p.reverse ++ [c.1]).map Fin.val := by
    dsimp only [q]
    rw [boundaryPath_raw_history single data.target p, history]
  have qAtom : q.atom = d.1.val := rawPathNode_boundaryPath_atom data.target p d.1 last
  have qCarried : ∀ atom ∈ ([c.1] : List input.Atom), atom.val ∈ q.history := by
    intro atom member
    have same : atom = c.1 := List.mem_singleton.mp member
    rw [same, qHistory]
    exact List.mem_map_of_mem (by simp)
  have outside : d.1 ∉ ([c.1] : List input.Atom) := valid.outside d.1 dmem
  have component : InComponent input.moleculeGraph [c.1]
      (input.detectedMultiCenterMolecule.ligandAtomAt c (data.ligandOf left)) d.1 := by
    simpa only [referenceAt] using obsPath_mem_inComponent valid dmem
  have sym : StructuralSymmetry mol σ := by
    dsimp only [σ]
    exact structuralSymmetry_of_aut input mol agreement admissible supported e
  have centerFixedPerm : (e : Equiv.Perm input.Atom) c.1 = c.1 :=
    (centerPerm_eq_iff input.detectedMultiCenterMolecule e c).mp centerFixed
  have rootMap : mapNode σ (canonicalCenterRoot c.1.val) = canonicalCenterRoot c.1.val := by
    dsimp only [σ]
    rw [mapNode_canonicalCenterRoot, relabelOf_val, centerFixedPerm]
  let D : Nat := structuralDepth mol (canonicalCenterRoot c.1.val)
  have adequate : q.history.length ≤ D + (canonicalCenterRoot c.1.val).history.length :=
    boundary_query_adequate input mol agreement single data.target data.real
      (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) p validHistory
      (canonicalCenterRoot c.1.val)
  have sourceEq := generated_label_eq_descriptor input mol D (inputGeometry input)
    (canonicalCenterRoot c.1.val) q references rootReached sourceStrict adequate
  have imageAdequate : (mapNode σ q).history.length ≤
      D + (mapNode σ (canonicalCenterRoot c.1.val)).history.length := by
    simpa only [mapNode_history, List.length_map] using adequate
  have imageReached : Reached mol (mapNode σ (canonicalCenterRoot c.1.val)) :=
    reached_map sym wf unique rawSingle (canonicalCenterRoot c.1.val) rootReached
  have imageStrict : StrictDescendant mol (mapNode σ (canonicalCenterRoot c.1.val))
      (mapNode σ q) :=
    strictDescendant_map sym wf unique rawSingle sourceStrict
  have imageEqRaw := generated_label_eq_descriptor input mol D (mirror (inputGeometry input))
    (mapNode σ (canonicalCenterRoot c.1.val)) (mapNode σ q)
    (references.map (e : Equiv.Perm input.Atom)) imageReached imageStrict imageAdequate
  have imageEq : ((generated input mol D (mirror (inputGeometry input))
        (canonicalCenterRoot c.1.val) (references.map (e : Equiv.Perm input.Atom))).factAt?
        (mapNode σ q)).map factLabel =
      preparedDescriptor? mol (jointOperations input mol)
        (D + (canonicalCenterRoot c.1.val).history.length - q.history.length)
        (mirror (inputGeometry input)) [] ((references.map Fin.val).map σ) (mapNode σ q) := by
    simp only [rootMap, mapNode_history, List.length_map, map_references_relabel] at imageEqRaw
    exact imageEqRaw
  have physical' : ∀ other : input.detectedMultiCenterMolecule.Center,
      LigandBranchReaches input.detectedMultiCenterMolecule c (data.ligandOf left) other.1 →
        input.detectedMultiCenterMolecule.configurationSign cfg other *
          permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e other) =
        (-1 : ℝ) * input.detectedMultiCenterMolecule.configurationSign cfg
          (input.detectedMultiCenterMolecule.centerPerm e other) := by
    intro other member
    simpa using physical other member
  cases frameQ : frameAtoms? mol q with
  | none =>
      have sourceNone := preparedDescriptor?_none_of_frame mol (jointOperations input mol)
        (D + (canonicalCenterRoot c.1.val).history.length - q.history.length)
        (inputGeometry input) [] (references.map Fin.val) q frameQ
      have imageFrameNone : frameAtoms? mol (mapNode σ q) = none :=
        frameAtoms_map_none sym wf unique rawSingle q frameQ qValid
      have imageNone := preparedDescriptor?_none_of_frame mol (jointOperations input mol)
        (D + (canonicalCenterRoot c.1.val).history.length - q.history.length)
        (mirror (inputGeometry input)) [] ((references.map Fin.val).map σ) (mapNode σ q) imageFrameNone
      rw [sourceEq, imageEq, sourceNone, imageNone]
  | some atoms =>
      have core := descriptor_map_mirror_eq input mol agreement admissible supported single
        cfg e calibrated c (data.ligandOf left) physical' [c.1] (by simp) q qReached d qAtom
        outside qCarried component atoms frameQ
        (D + (canonicalCenterRoot c.1.val).history.length - q.history.length)
        (references.map Fin.val)
      exact sourceEq.trans (core.symm.trans imageEq.symm)

/-- Pointwise consequence of one physical branch symmetry. -/
theorem generated_label_eq_of_mirrorTransport
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
    (rootAddress : data.target.1.address = [])
    (left right : Fin 4)
    (mirrorT : MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right))
    (references : List input.Atom)
    (p : List input.Atom) (d : input.detectedMultiCenterMolecule.Center)
    (valid : ResidualObsPath input.moleculeGraph [c.1]
      (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) p)
    (last : p.getLast? = some d.1) :
    ∃ e : input.detectedMultiCenterMolecule.Aut,
      input.detectedMultiCenterMolecule.centerPerm e c = c ∧
      input.detectedMultiCenterMolecule.ligandPermAt e c (data.ligandOf left) =
        data.ligandOf right ∧
      ((generated input mol (structuralDepth mol (canonicalCenterRoot c.1.val))
          (inputGeometry input) (canonicalCenterRoot c.1.val) references).factAt?
          (rawPathNode data.target.1.root (boundaryPath data.target p))).map factLabel =
        ((generated input mol (structuralDepth mol (canonicalCenterRoot c.1.val))
          (mirror (inputGeometry input)) (canonicalCenterRoot c.1.val)
          (references.map (e : Equiv.Perm input.Atom))).factAt?
          (mapNode (relabelOf input (e : Equiv.Perm input.Atom))
            (rawPathNode data.target.1.root (boundaryPath data.target p)))).map factLabel := by
  obtain ⟨e, centerFixed, ligandFixed, physical⟩ := mirrorT
  exact ⟨e, centerFixed, ligandFixed, generated_label_eq_of_physicalMirror input mol agreement admissible supported single cfg c
      calibrated data rootAddress left e centerFixed (by simpa using physical) references p d valid last⟩

/-- One molecular symmetry transports every generated branch label at every reference list. -/
theorem generated_labels_eq_of_mirrorTransport
    (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (c : input.detectedMultiCenterMolecule.Center)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (data : OccurrenceData input mol c (canonicalCenterRoot c.1.val))
    (rootAddress : data.target.1.address = [])
    (left right : Fin 4)
    (mirrorT : MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right))
 :
    ∃ e : input.detectedMultiCenterMolecule.Aut,
      input.detectedMultiCenterMolecule.centerPerm e c = c ∧
      input.detectedMultiCenterMolecule.ligandPermAt e c (data.ligandOf left) =
        data.ligandOf right ∧
      ∀ (references : List input.Atom) (p : List input.Atom)
        (d : input.detectedMultiCenterMolecule.Center),
        ResidualObsPath input.moleculeGraph [c.1]
          (referenceAt input mol c (canonicalCenterRoot c.1.val) data left) p →
        p.getLast? = some d.1 →
        ((generated input mol (structuralDepth mol (canonicalCenterRoot c.1.val))
          (inputGeometry input) (canonicalCenterRoot c.1.val) references).factAt?
          (rawPathNode data.target.1.root (boundaryPath data.target p))).map factLabel =
        ((generated input mol (structuralDepth mol (canonicalCenterRoot c.1.val))
          (mirror (inputGeometry input)) (canonicalCenterRoot c.1.val)
          (references.map (e : Equiv.Perm input.Atom))).factAt?
          (mapNode (relabelOf input (e : Equiv.Perm input.Atom))
            (rawPathNode data.target.1.root (boundaryPath data.target p)))).map factLabel := by
  obtain ⟨e, centerFixed, ligandFixed, physical⟩ := mirrorT
  refine ⟨e, centerFixed, ligandFixed, ?_⟩
  intro references p d valid last
  exact generated_label_eq_of_physicalMirror input mol agreement admissible supported single cfg c
      calibrated data rootAddress left e centerFixed (by simpa using physical) references p d valid last

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.preparedDescriptor?_none_of_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.descends_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.strictDescendant_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.strictDescendant_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.rawPathNode_boundaryPath_atom
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.map_references_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.mem_of_getLast?_eq_some
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.generated_label_eq_of_mirrorTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.generated_label_eq_of_physicalMirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPhysicalMirrorKeys.generated_labels_eq_of_mirrorTransport
