import TetraStereo.OneCenter.OfficialSystemBranchPerception
import TetraStereo.OneCenter.OfficialHierarchicalDigraph

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Production-oriented registration of non-center stereochemical units.

  The core system layer works over an arbitrary finite unit type.  Production perception, however,
  naturally discovers a finite *list* of stereochemical units: double bonds, cumulenes,
  unassigned axial/planar/conformational candidates, assigned axes, planes, helices,
  conformational states, ensemble states, auxiliary CIP nodes, phantom nodes, and lone-pair nodes.
  This module packages such detector output as a finite `Fin n` unit universe, seeds the official
  descriptor environment when a descriptor is safe, and supplies branch policies that map atoms and
  official virtual/duplicate digraph nodes to descriptor-bearing units.
-/

namespace OfficialDescriptorValue

/-- Rule-3 projection of a descriptor value. -/
def rule3Geometry? : OfficialDescriptorValue → Option OfficialRule3Geometry
  | rule3Geometry geometry => some geometry
  | _ => none

/-- Rule-4a projection of a descriptor value. -/
def rule4aKind? : OfficialDescriptorValue → Option OfficialStereogenicUnitKind
  | rule4aKind kind => some kind
  | _ => none

/-- Rule-4b projection of a descriptor value. -/
def rule4bPair? : OfficialDescriptorValue → Option OfficialDescriptorPairKind
  | rule4bPair pair => some pair
  | _ => none

/-- Rule-4c projection of a descriptor value. -/
def rule4cDescriptor? : OfficialDescriptorValue → Option OfficialPseudoasymmetricDescriptor
  | rule4cDescriptor descriptor => some descriptor
  | _ => none

/-- Rule-5 projection of a descriptor value. -/
def rule5Descriptor? : OfficialDescriptorValue → Option OfficialRule5Descriptor
  | rule5Descriptor descriptor => some descriptor
  | _ => none

end OfficialDescriptorValue

/-- Find the first projected value in a list of official descriptor values. -/
def firstDescriptorProjection? {α : Type*}
    (project : OfficialDescriptorValue → Option α) :
    List OfficialDescriptorValue → Option α
  | [] => none
  | value :: rest =>
      match project value with
      | some projected => some projected
      | none => firstDescriptorProjection? project rest

/-- A detected stereochemical unit together with enough metadata for the official system layer.

`support` is the atom set used by branch-frontier mapping.  `initialValues` are descriptor facts
that can be seeded immediately, before dependency tasks run. -/
structure OfficialDetectedUnit (V : Type*) where
  kind : OfficialStereochemicalUnitKind
  support : Finset V
  anchor? : Option V := none
  nodeKind? : Option OfficialPhantomNodeKind := none
  nodeRootDistance? : Option ℕ := none
  initialValues : List OfficialDescriptorValue := []

namespace OfficialDetectedUnit

variable {V : Type*} [DecidableEq V]

/-- Number of immediately seeded official descriptor facts for this unit. -/
def descriptorValueCount (unit : OfficialDetectedUnit V) : ℕ :=
  unit.initialValues.length

/-- Whether this unit starts with at least one official descriptor fact. -/
def hasInitialValue (unit : OfficialDetectedUnit V) : Bool :=
  !unit.initialValues.isEmpty

/-- Support generated from a list of atoms. -/
def supportOfList (atoms : List V) : Finset V :=
  atoms.toFinset

/-- Register a double-bond or alkene/cumulene unit from endpoints and optional perceived stereo. -/
def ofDoubleBond (left right : V) (stereo? : Option DoubleBondStereo) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.alkeneOrCumulene
  support := [left, right].toFinset
  anchor? := some left
  initialValues :=
    match stereo?.bind DoubleBondStereo.toRule3Geometry? with
    | some geometry => [OfficialDescriptorValue.rule3Geometry geometry]
    | none => []

/-- Register a cumulene-like unit from its atom path and optional perceived terminal geometry. -/
def ofCumulenePath (path : List V) (stereo? : Option DoubleBondStereo) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.alkeneOrCumulene
  support := path.toFinset
  anchor? := path.head?
  initialValues :=
    match stereo?.bind DoubleBondStereo.toRule3Geometry? with
    | some geometry => [OfficialDescriptorValue.rule3Geometry geometry]
    | none => []

/-- Register an unassigned axial stereogenic candidate. -/
def ofAxialCandidate (axisStart axisEnd : V) (support : Finset V) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.axis
  support := insert axisStart (insert axisEnd support)
  anchor? := some axisStart

/-- Register an unassigned planar stereogenic candidate. -/
def ofPlanarCandidate (planeAtoms : List V) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.plane
  support := planeAtoms.toFinset
  anchor? := planeAtoms.head?

/-- Register an alkene/cumulene assignment as a Rule-3 descriptor source. -/
def ofAlkeneAssignment (assignment : AlkeneAssignment V) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.alkeneOrCumulene
  support :=
    [ assignment.unit.leftAtom, assignment.unit.rightAtom
    , assignment.unit.leftHigh, assignment.unit.leftLow
    , assignment.unit.rightHigh, assignment.unit.rightLow
    ].toFinset
  anchor? := some assignment.unit.leftAtom
  initialValues :=
    [OfficialDescriptorValue.rule3Geometry assignment.descriptor.toRule3Geometry]

/-- Register an axial stereogenic unit.  The descriptor marks the unit as chiral at Rule 4a; a
future official axis-specific descriptor mapping can add further Rule-5 data. -/
def ofAxialAssignment (assignment : AxialAssignment V) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.axis
  support :=
    [ assignment.unit.axisStart, assignment.unit.axisEnd
    , assignment.unit.startHigh, assignment.unit.startLow
    , assignment.unit.endHigh, assignment.unit.endLow
    ].toFinset
  anchor? := some assignment.unit.axisStart
  initialValues := [OfficialDescriptorValue.rule4aKind OfficialStereogenicUnitKind.chiral]

/-- Register a planar stereogenic unit. -/
def ofPlanarAssignment (assignment : PlanarAssignment V) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.plane
  support :=
    (assignment.unit.planeAtoms ++
      [assignment.unit.pilotAtom, assignment.unit.highReference, assignment.unit.lowReference]).toFinset
  anchor? := some assignment.unit.pilotAtom
  initialValues := [OfficialDescriptorValue.rule4aKind OfficialStereogenicUnitKind.chiral]

/-- Register a helical stereogenic unit with official Rule-5 `M/P` data. -/
def ofHelicalAssignment (assignment : HelicalAssignment V) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.helix
  support :=
    (assignment.unit.helixPath ++
      [assignment.unit.frontReference, assignment.unit.backReference]).toFinset
  anchor? := assignment.unit.helixPath.head?
  initialValues :=
    [ OfficialDescriptorValue.rule4aKind OfficialStereogenicUnitKind.chiral
    , OfficialDescriptorValue.rule5Descriptor assignment.descriptor.toRule5Descriptor
    ]

/-- Register a conformational stereochemical state over an atom support. -/
def ofConformationalState (support : Finset V)
    (kind? : Option OfficialStereogenicUnitKind := none) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.conformation
  support := support
  anchor? := support.toList.head?
  initialValues :=
    match kind? with
    | some kind => [OfficialDescriptorValue.rule4aKind kind]
    | none => []

/-- Register an ensemble stereochemical state over an atom support. -/
def ofEnsembleState (support : Finset V)
    (kind? : Option OfficialStereogenicUnitKind := none) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.ensemble
  support := support
  anchor? := support.toList.head?
  initialValues :=
    match kind? with
    | some kind => [OfficialDescriptorValue.rule4aKind kind]
    | none => []

/-- Register an auxiliary CIP descriptor source. -/
def ofAuxiliaryRule5 (anchor : V) (support : Finset V)
    (descriptor : OfficialRule5Descriptor) (rootDistance? : Option ℕ := some 0) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.auxiliary
  support := insert anchor support
  anchor? := some anchor
  nodeKind? := some OfficialPhantomNodeKind.auxiliary
  nodeRootDistance? := rootDistance?
  initialValues :=
    [ OfficialDescriptorValue.rule4aKind OfficialStereogenicUnitKind.chiral
    , OfficialDescriptorValue.rule5Descriptor descriptor.asAuxiliary
    ]

/-- Register a phantom node used by the official hierarchical digraph. -/
def ofPhantomNode (anchor : V) (support : Finset V) (rootDistance? : Option ℕ := some 0) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.phantom
  support := insert anchor support
  anchor? := some anchor
  nodeKind? := some OfficialPhantomNodeKind.phantom
  nodeRootDistance? := rootDistance?

/-- Register a lone-pair node used by the official hierarchical digraph. -/
def ofLonePairNode (anchor : V) (support : Finset V) (rootDistance? : Option ℕ := some 0) :
    OfficialDetectedUnit V where
  kind := OfficialStereochemicalUnitKind.lonePair
  support := insert anchor support
  anchor? := some anchor
  nodeKind? := some OfficialPhantomNodeKind.lonePair
  nodeRootDistance? := rootDistance?

@[simp] theorem ofDoubleBond_rule3_E (left right : V) :
    (ofDoubleBond left right (some DoubleBondStereo.E)).initialValues =
      [OfficialDescriptorValue.rule3Geometry OfficialRule3Geometry.seqtrans] :=
  rfl

@[simp] theorem ofDoubleBond_rule3_Z (left right : V) :
    (ofDoubleBond left right (some DoubleBondStereo.Z)).initialValues =
      [OfficialDescriptorValue.rule3Geometry OfficialRule3Geometry.seqcis] :=
  rfl

@[simp] theorem ofDoubleBond_unspecified_initialValues (left right : V) :
    (ofDoubleBond left right (some DoubleBondStereo.unspecified)).initialValues = [] :=
  rfl

@[simp] theorem ofHelicalAssignment_descriptorValueCount (assignment : HelicalAssignment V) :
    (ofHelicalAssignment assignment).descriptorValueCount = 2 :=
  rfl

@[simp] theorem ofAuxiliaryRule5_descriptorValueCount (anchor : V) (support : Finset V)
    (descriptor : OfficialRule5Descriptor) (rootDistance? : Option ℕ) :
    (ofAuxiliaryRule5 anchor support descriptor rootDistance?).descriptorValueCount = 2 :=
  rfl

end OfficialDetectedUnit

/-- Production detector output: a finite list of stereochemical units discovered in one molecule. -/
structure OfficialUnitDetectionResult (V : Type*) [DecidableEq V] where
  units : List (OfficialDetectedUnit V)

/-- Detector record for a double-bond unit. -/
structure DetectedDoubleBondUnit (V : Type*) where
  left : V
  right : V
  stereo? : Option DoubleBondStereo := none

/-- Detector record for a cumulene-like unit. -/
structure DetectedCumuleneUnit (V : Type*) where
  path : List V
  stereo? : Option DoubleBondStereo := none

/-- Detector record for a graph-visible but descriptor-unassigned axial candidate. -/
structure DetectedAxialCandidateUnit (V : Type*) [DecidableEq V] where
  axisStart : V
  axisEnd : V
  support : Finset V

/-- Detector record for a graph-visible but descriptor-unassigned planar candidate. -/
structure DetectedPlanarCandidateUnit (V : Type*) where
  planeAtoms : List V

/-- Detector record for a conformational state. -/
structure DetectedConformationalState (V : Type*) [DecidableEq V] where
  support : Finset V
  kind? : Option OfficialStereogenicUnitKind := none

/-- Detector record for an ensemble stereochemical state. -/
structure DetectedEnsembleState (V : Type*) [DecidableEq V] where
  support : Finset V
  kind? : Option OfficialStereogenicUnitKind := none

/-- Detector record for an auxiliary Rule-5 descriptor node. -/
structure DetectedAuxiliaryRule5Node (V : Type*) [DecidableEq V] where
  anchor : V
  support : Finset V
  descriptor : OfficialRule5Descriptor
  rootDistance? : Option ℕ := some 0

/-- Detector record for a phantom node. -/
structure DetectedPhantomNode (V : Type*) [DecidableEq V] where
  anchor : V
  support : Finset V
  rootDistance? : Option ℕ := some 0

/-- Detector record for a lone-pair node. -/
structure DetectedLonePairNode (V : Type*) [DecidableEq V] where
  anchor : V
  support : Finset V
  rootDistance? : Option ℕ := some 0

/-- Count summary for a production detector bundle. -/
structure OfficialDetectorCoverage where
  doubleBonds : ℕ := 0
  cumulenes : ℕ := 0
  axes : ℕ := 0
  planes : ℕ := 0
  helices : ℕ := 0
  conformations : ℕ := 0
  ensembles : ℕ := 0
  auxiliaryRule5Nodes : ℕ := 0
  phantomNodes : ℕ := 0
  lonePairNodes : ℕ := 0
  total : ℕ := 0
  deriving DecidableEq, Repr

namespace OfficialDetectorCoverage

/-- Whether no stereochemical units were registered. -/
def empty (coverage : OfficialDetectorCoverage) : Bool :=
  coverage.total = 0

/-- Whether every broad non-center family has at least one registered unit. -/
def coversBroadStereochemicalSurface (coverage : OfficialDetectorCoverage) : Bool :=
  coverage.doubleBonds > 0 && coverage.cumulenes > 0 && coverage.axes > 0 &&
    coverage.planes > 0 && coverage.helices > 0 && coverage.conformations > 0 &&
    coverage.ensembles > 0

end OfficialDetectorCoverage

/-- Production-facing bundle of non-center stereochemical detectors.

This is deliberately list-based: external chemistry software can populate these lists, and Lean
turns the finite list into a proof-facing `Fin n` unit universe. -/
structure OfficialNoncenterDetectorBundle (V : Type*) [DecidableEq V] where
  doubleBonds : List (DetectedDoubleBondUnit V) := []
  cumulenes : List (DetectedCumuleneUnit V) := []
  axisCandidates : List (DetectedAxialCandidateUnit V) := []
  axes : List (AxialAssignment V) := []
  planeCandidates : List (DetectedPlanarCandidateUnit V) := []
  planes : List (PlanarAssignment V) := []
  helices : List (HelicalAssignment V) := []
  conformationCandidates : List (DetectedConformationalState V) := []
  conformations : List (DetectedConformationalState V) := []
  ensembles : List (DetectedEnsembleState V) := []
  auxiliaryRule5Nodes : List (DetectedAuxiliaryRule5Node V) := []
  phantomNodes : List (DetectedPhantomNode V) := []
  lonePairNodes : List (DetectedLonePairNode V) := []

namespace OfficialNoncenterDetectorBundle

variable {V : Type*} [DecidableEq V]

/-- Convert all non-center detector records into official detected units. -/
def detectedUnits (bundle : OfficialNoncenterDetectorBundle V) :
    List (OfficialDetectedUnit V) :=
  (bundle.doubleBonds.map fun unit =>
      OfficialDetectedUnit.ofDoubleBond unit.left unit.right unit.stereo?) ++
  (bundle.cumulenes.map fun unit =>
      OfficialDetectedUnit.ofCumulenePath unit.path unit.stereo?) ++
  (bundle.axisCandidates.map fun unit =>
      OfficialDetectedUnit.ofAxialCandidate unit.axisStart unit.axisEnd unit.support) ++
  (bundle.axes.map OfficialDetectedUnit.ofAxialAssignment) ++
  (bundle.planeCandidates.map fun unit =>
      OfficialDetectedUnit.ofPlanarCandidate unit.planeAtoms) ++
  (bundle.planes.map OfficialDetectedUnit.ofPlanarAssignment) ++
  (bundle.helices.map OfficialDetectedUnit.ofHelicalAssignment) ++
  (bundle.conformationCandidates.map fun state =>
      OfficialDetectedUnit.ofConformationalState state.support state.kind?) ++
  (bundle.conformations.map fun state =>
      OfficialDetectedUnit.ofConformationalState state.support state.kind?) ++
  (bundle.ensembles.map fun state =>
      OfficialDetectedUnit.ofEnsembleState state.support state.kind?) ++
  (bundle.auxiliaryRule5Nodes.map fun node =>
      OfficialDetectedUnit.ofAuxiliaryRule5 node.anchor node.support node.descriptor
        node.rootDistance?) ++
  (bundle.phantomNodes.map fun node =>
      OfficialDetectedUnit.ofPhantomNode node.anchor node.support node.rootDistance?) ++
  (bundle.lonePairNodes.map fun node =>
      OfficialDetectedUnit.ofLonePairNode node.anchor node.support node.rootDistance?)

/-- Coverage counts for the detector bundle, useful at public/API and validation boundaries. -/
def coverage (bundle : OfficialNoncenterDetectorBundle V) : OfficialDetectorCoverage where
  doubleBonds := bundle.doubleBonds.length
  cumulenes := bundle.cumulenes.length
  axes := bundle.axisCandidates.length + bundle.axes.length
  planes := bundle.planeCandidates.length + bundle.planes.length
  helices := bundle.helices.length
  conformations := bundle.conformationCandidates.length + bundle.conformations.length
  ensembles := bundle.ensembles.length
  auxiliaryRule5Nodes := bundle.auxiliaryRule5Nodes.length
  phantomNodes := bundle.phantomNodes.length
  lonePairNodes := bundle.lonePairNodes.length
  total := bundle.detectedUnits.length

/-- Convert a non-center detector bundle into the finite official unit-detection result. -/
def toDetectionResult (bundle : OfficialNoncenterDetectorBundle V) :
    OfficialUnitDetectionResult V where
  units := bundle.detectedUnits

@[simp] theorem coverage_total_eq_detectedUnits_length
    (bundle : OfficialNoncenterDetectorBundle V) :
    bundle.coverage.total = bundle.detectedUnits.length :=
  rfl

end OfficialNoncenterDetectorBundle

/-- A branch-frontier mapping policy from atoms to registered units. -/
structure BranchFrontierUnitPolicy {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (Unit : Type*) where
  unitsAtAtom : V → List Unit
  includeSource : m.Center → Fin 4 → MoleculeGraph.CIPState V → Unit → Bool :=
    fun center _ state _ => decide (state.current ≠ center.1)

/-- A registered unit encountered at a concrete branch-frontier atom. -/
structure BranchFrontierUnitSource {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (Unit : Type*) where
  atom : V
  unit : Unit

namespace MoleculeGraph.CIPState

variable {V : Type*} [DecidableEq V]

/-- Whether a cycle-cut branch state is a duplicate node. -/
def isDuplicate (state : MoleculeGraph.CIPState V) : Bool :=
  decide (state.current ∈ state.seen)

@[simp] theorem isDuplicate_eq_false_of_current_not_mem
    (state : MoleculeGraph.CIPState V) (h : state.current ∉ state.seen) :
    state.isDuplicate = false := by
  simp [isDuplicate, h]

@[simp] theorem isDuplicate_eq_true_of_current_mem
    (state : MoleculeGraph.CIPState V) (h : state.current ∈ state.seen) :
    state.isDuplicate = true := by
  simp [isDuplicate, h]

end MoleculeGraph.CIPState

/-- Provenance of a descriptor source encountered while walking a branch. -/
inductive BranchDescriptorSourceKind where
  | atomSupport
  | duplicateAtom
  | phantom
  | lonePair
  | auxiliary
  deriving DecidableEq, Repr

namespace BranchDescriptorSourceKind

/-- Convert official virtual-node kinds to branch descriptor-source kinds. -/
def ofPhantomNodeKind : OfficialPhantomNodeKind → BranchDescriptorSourceKind
  | OfficialPhantomNodeKind.phantom => phantom
  | OfficialPhantomNodeKind.lonePair => lonePair
  | OfficialPhantomNodeKind.auxiliary => auxiliary

end BranchDescriptorSourceKind

/-- How virtual official digraph nodes are resolved to registered descriptor units. -/
inductive VirtualNodeResolutionPolicy where
  | exactDistance
  | kindFallback
  | kindOnly
  deriving DecidableEq, Repr

/-- Human-readable summary of a descriptor-source branch policy. -/
structure DescriptorSourcePolicyProfile where
  ordinaryAtomSources : Bool := true
  duplicateAtomSources : Bool := true
  phantomSources : Bool := true
  lonePairSources : Bool := true
  auxiliarySources : Bool := true
  virtualNodeResolution : VirtualNodeResolutionPolicy :=
    VirtualNodeResolutionPolicy.exactDistance
  deriving DecidableEq, Repr

namespace DescriptorSourcePolicyProfile

/-- Whether this profile includes a descriptor source kind. -/
def includesSourceKind (profile : DescriptorSourcePolicyProfile) :
    BranchDescriptorSourceKind → Bool
  | BranchDescriptorSourceKind.atomSupport => profile.ordinaryAtomSources
  | BranchDescriptorSourceKind.duplicateAtom => profile.duplicateAtomSources
  | BranchDescriptorSourceKind.phantom => profile.phantomSources
  | BranchDescriptorSourceKind.lonePair => profile.lonePairSources
  | BranchDescriptorSourceKind.auxiliary => profile.auxiliarySources

/-- Profile for exact kind-and-distance virtual-node matching. -/
def exactDistance : DescriptorSourcePolicyProfile := {}

/-- Profile for exact virtual-node matching with kind-only fallback. -/
def kindFallback : DescriptorSourcePolicyProfile where
  virtualNodeResolution := VirtualNodeResolutionPolicy.kindFallback

/-- Profile for kind-only virtual-node matching. -/
def kindOnly : DescriptorSourcePolicyProfile where
  virtualNodeResolution := VirtualNodeResolutionPolicy.kindOnly

end DescriptorSourcePolicyProfile

/-- A descriptor-bearing unit source found either at an atom/duplicate atom or at a virtual
official digraph node. -/
structure BranchDescriptorUnitSource {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (Unit : Type*) where
  atom? : Option V := none
  node? : Option (OfficialCIPNode V) := none
  sourceKind : BranchDescriptorSourceKind
  unit : Unit

/-- A descriptor-source branch policy that sees ordinary support atoms, duplicate atoms, and
virtual official digraph nodes. -/
structure DescriptorSourceBranchPolicy {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (Unit : Type*) where
  unitsAtAtom : V → List Unit
  unitsAtVirtualNode : OfficialPhantomNodeKind → ℕ → List Unit := fun _ _ => []
  officialNodesAtDepth :
    m.Center → Fin 4 → ℕ → List (OfficialCIPNode V) := fun _ _ _ => []
  includeStateSource :
    m.Center → Fin 4 → MoleculeGraph.CIPState V → BranchDescriptorSourceKind → Unit → Bool :=
    fun center _ state _ _ => decide (state.current ≠ center.1)
  includeNodeSource :
    m.Center → Fin 4 → OfficialCIPNode V → BranchDescriptorSourceKind → Unit → Bool :=
    fun _ _ _ _ _ => true

namespace DescriptorSourceBranchPolicy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {Unit : Type*}
variable {m : MultiCenterMolecule V}

/-- Promote the older atom-support policy to the descriptor-source policy. -/
def ofBranchFrontierUnitPolicy (policy : BranchFrontierUnitPolicy m Unit) :
    DescriptorSourceBranchPolicy m Unit where
  unitsAtAtom := policy.unitsAtAtom
  includeStateSource := fun center i state _ unit => policy.includeSource center i state unit

/-- Units reachable from an official hierarchical-digraph node under this policy. -/
def unitsAtOfficialNode (policy : DescriptorSourceBranchPolicy m Unit)
    (node : OfficialCIPNode V) : List Unit :=
  match node.current?, node.provenance with
  | some atom, _ => policy.unitsAtAtom atom
  | none, OfficialCIPNodeProvenance.placeholder kind distance =>
      policy.unitsAtVirtualNode kind distance
  | none, _ => []

/-- Descriptor-source kind for an official hierarchical-digraph node. -/
def sourceKindOfOfficialNode (node : OfficialCIPNode V) :
    Option BranchDescriptorSourceKind :=
  match node.current?, node.provenance with
  | some _, OfficialCIPNodeProvenance.multipleBondDuplicate _ =>
      some BranchDescriptorSourceKind.duplicateAtom
  | some _, OfficialCIPNodeProvenance.ringDuplicate _ =>
      some BranchDescriptorSourceKind.duplicateAtom
  | some _, _ => some BranchDescriptorSourceKind.atomSupport
  | none, OfficialCIPNodeProvenance.placeholder kind _ =>
      some (BranchDescriptorSourceKind.ofPhantomNodeKind kind)
  | none, _ => none

end DescriptorSourceBranchPolicy

namespace OfficialUnitDetectionResult

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite unit index type for this detector result. -/
abbrev Unit (result : OfficialUnitDetectionResult V) : Type :=
  Fin result.units.length

/-- Lookup a detected unit by its finite index. -/
def unitAt (result : OfficialUnitDetectionResult V) (unit : result.Unit) :
    OfficialDetectedUnit V :=
  result.units.get unit

/-- Virtual-node kind attached to a detected unit, when the unit is backed by a phantom,
lone-pair, or auxiliary node in the official hierarchical digraph. -/
def nodeKind? (result : OfficialUnitDetectionResult V) (unit : result.Unit) :
    Option OfficialPhantomNodeKind :=
  (result.unitAt unit).nodeKind?

/-- Virtual-node root distance attached to a detected unit, when the detector knows it. -/
def nodeRootDistance? (result : OfficialUnitDetectionResult V) (unit : result.Unit) :
    Option ℕ :=
  (result.unitAt unit).nodeRootDistance?

/-- Interpret detector output as an official stereogenic-unit registry. -/
def registry (result : OfficialUnitDetectionResult V) (molecule : MoleculeGraph V) :
    OfficialStereogenicUnitRegistry V result.Unit where
  molecule := molecule
  kind := fun unit => (result.unitAt unit).kind
  support := fun unit => (result.unitAt unit).support
  anchor? := fun unit => (result.unitAt unit).anchor?

/-- Initial official descriptor environment induced by detector-seeded descriptor facts. -/
def initialEnvironment (result : OfficialUnitDetectionResult V) :
    OfficialDescriptorEnvironment result.Unit where
  rule3Geometry := fun unit =>
    firstDescriptorProjection? OfficialDescriptorValue.rule3Geometry?
      (result.unitAt unit).initialValues
  rule4aKind := fun unit =>
    firstDescriptorProjection? OfficialDescriptorValue.rule4aKind?
      (result.unitAt unit).initialValues
  rule4bPair := fun unit =>
    firstDescriptorProjection? OfficialDescriptorValue.rule4bPair?
      (result.unitAt unit).initialValues
  rule4cDescriptor := fun unit =>
    firstDescriptorProjection? OfficialDescriptorValue.rule4cDescriptor?
      (result.unitAt unit).initialValues
  rule5Descriptor := fun unit =>
    firstDescriptorProjection? OfficialDescriptorValue.rule5Descriptor?
      (result.unitAt unit).initialValues

/-- Convert unit-detection output to the general official detector output, with a supplied
dependency schedule. -/
def toOfficialDetectorOutput (result : OfficialUnitDetectionResult V)
    (schedule : OfficialDescriptorSchedule result.Unit := { tasks := [] }) :
    OfficialDetectorOutput result.Unit where
  initialEnvironment := result.initialEnvironment
  schedule := schedule

/-- Map a branch-frontier atom to all registered units whose atom supports contain it. -/
def unitsAtAtomBySupport (result : OfficialUnitDetectionResult V) (atom : V) :
    List result.Unit :=
  (List.finRange result.units.length).filter fun unit =>
    atom ∈ (result.unitAt unit).support

/-- Map a virtual official digraph node kind to all registered units backed by that kind. -/
def unitsAtVirtualNodeByKind (result : OfficialUnitDetectionResult V)
    (kind : OfficialPhantomNodeKind) : List result.Unit :=
  (List.finRange result.units.length).filter fun unit =>
    result.nodeKind? unit = some kind

/-- Map a virtual official digraph node to registered units backed by the same kind and root
distance. -/
def unitsAtVirtualNodeByKindDistance (result : OfficialUnitDetectionResult V)
    (kind : OfficialPhantomNodeKind) (rootDistance : ℕ) : List result.Unit :=
  (List.finRange result.units.length).filter fun unit =>
    result.nodeKind? unit = some kind ∧
      result.nodeRootDistance? unit = some rootDistance

/-- Map a virtual official digraph node under an explicit resolution policy. -/
def unitsAtVirtualNodeByResolution (result : OfficialUnitDetectionResult V)
    (resolution : VirtualNodeResolutionPolicy)
    (kind : OfficialPhantomNodeKind) (rootDistance : ℕ) : List result.Unit :=
  match resolution with
  | VirtualNodeResolutionPolicy.exactDistance =>
      result.unitsAtVirtualNodeByKindDistance kind rootDistance
  | VirtualNodeResolutionPolicy.kindFallback =>
      match result.unitsAtVirtualNodeByKindDistance kind rootDistance with
      | [] => result.unitsAtVirtualNodeByKind kind
      | exact => exact
  | VirtualNodeResolutionPolicy.kindOnly =>
      result.unitsAtVirtualNodeByKind kind

/-- Registered units of one official stereochemical kind. -/
def unitsOfKind (result : OfficialUnitDetectionResult V)
    (kind : OfficialStereochemicalUnitKind) : List result.Unit :=
  (List.finRange result.units.length).filter fun unit =>
    (result.unitAt unit).kind = kind

/-- Support-based policy for mapping branch-frontier atoms to registered units. -/
def supportBranchPolicy (result : OfficialUnitDetectionResult V)
    (m : MultiCenterMolecule V) :
    BranchFrontierUnitPolicy m result.Unit where
  unitsAtAtom := result.unitsAtAtomBySupport

/-- Duplicate/virtual-aware policy for mapping branch descriptor sources to registered units. -/
def descriptorSourceBranchPolicy (result : OfficialUnitDetectionResult V)
    (m : MultiCenterMolecule V) :
    DescriptorSourceBranchPolicy m result.Unit where
  unitsAtAtom := result.unitsAtAtomBySupport
  unitsAtVirtualNode := result.unitsAtVirtualNodeByKindDistance

/-- Duplicate/virtual-aware policy with an explicit virtual-node resolution profile. -/
def descriptorSourceBranchPolicyWith (result : OfficialUnitDetectionResult V)
    (m : MultiCenterMolecule V)
    (profile : DescriptorSourcePolicyProfile := DescriptorSourcePolicyProfile.exactDistance) :
    DescriptorSourceBranchPolicy m result.Unit where
  unitsAtAtom := result.unitsAtAtomBySupport
  unitsAtVirtualNode :=
    result.unitsAtVirtualNodeByResolution profile.virtualNodeResolution
  includeStateSource := fun center _ state sourceKind _ =>
    profile.includesSourceKind sourceKind && decide (state.current ≠ center.1)
  includeNodeSource := fun _ _ _ sourceKind _ =>
    profile.includesSourceKind sourceKind

omit [Fintype V] in
theorem mem_unitsAtAtomBySupport_iff (result : OfficialUnitDetectionResult V)
    (atom : V) (unit : result.Unit) :
    unit ∈ result.unitsAtAtomBySupport atom ↔ atom ∈ (result.unitAt unit).support := by
  simp [unitsAtAtomBySupport]

omit [Fintype V] in
theorem mem_unitsAtVirtualNodeByKind_iff (result : OfficialUnitDetectionResult V)
    (kind : OfficialPhantomNodeKind) (unit : result.Unit) :
    unit ∈ result.unitsAtVirtualNodeByKind kind ↔ result.nodeKind? unit = some kind := by
  simp [unitsAtVirtualNodeByKind]

omit [Fintype V] in
theorem mem_unitsAtVirtualNodeByKindDistance_iff (result : OfficialUnitDetectionResult V)
    (kind : OfficialPhantomNodeKind) (rootDistance : ℕ) (unit : result.Unit) :
    unit ∈ result.unitsAtVirtualNodeByKindDistance kind rootDistance ↔
      result.nodeKind? unit = some kind ∧
        result.nodeRootDistance? unit = some rootDistance := by
  simp [unitsAtVirtualNodeByKindDistance]

omit [Fintype V] in
theorem mem_unitsOfKind_iff (result : OfficialUnitDetectionResult V)
    (kind : OfficialStereochemicalUnitKind) (unit : result.Unit) :
    unit ∈ result.unitsOfKind kind ↔ (result.unitAt unit).kind = kind := by
  simp [unitsOfKind]

end OfficialUnitDetectionResult

/-- External/indexed axis annotation supplied by an importer or toolkit bridge. -/
structure IndexedDetectedAxialUnit where
  axisStart : ℕ
  axisEnd : ℕ
  startHigh : ℕ
  startLow : ℕ
  endHigh : ℕ
  endLow : ℕ
  descriptor : AxialDescriptor
  deriving DecidableEq, Repr

/-- External/indexed planar annotation supplied by an importer or toolkit bridge. -/
structure IndexedDetectedPlanarUnit where
  planeAtoms : List ℕ
  pilotAtom : ℕ
  highReference : ℕ
  lowReference : ℕ
  descriptor : PlanarDescriptor
  deriving DecidableEq, Repr

/-- External/indexed helical annotation supplied by an importer or toolkit bridge. -/
structure IndexedDetectedHelicalUnit where
  helixPath : List ℕ
  frontReference : ℕ
  backReference : ℕ
  descriptor : HelicalDescriptor
  deriving DecidableEq, Repr

/-- External/indexed conformational-state annotation. -/
structure IndexedDetectedConformationalState where
  stateId : String := ""
  support : List ℕ
  kind? : Option OfficialStereogenicUnitKind := none
  deriving DecidableEq, Repr

/-- External/indexed ensemble-state annotation. -/
structure IndexedDetectedEnsembleState where
  stateId : String := ""
  support : List ℕ
  kind? : Option OfficialStereogenicUnitKind := none
  deriving DecidableEq, Repr

/-- External/indexed auxiliary Rule-5 node annotation. -/
structure IndexedDetectedAuxiliaryRule5Node where
  anchor : ℕ
  support : List ℕ
  descriptor : OfficialRule5Descriptor
  rootDistance? : Option ℕ := some 0
  deriving DecidableEq, Repr

/-- External/indexed phantom-node annotation. -/
structure IndexedDetectedPhantomNode where
  anchor : ℕ
  support : List ℕ
  rootDistance? : Option ℕ := some 0
  deriving DecidableEq, Repr

/-- External/indexed lone-pair-node annotation. -/
structure IndexedDetectedLonePairNode where
  anchor : ℕ
  support : List ℕ
  rootDistance? : Option ℕ := some 0
  deriving DecidableEq, Repr

/-- Importer/toolkit-supplied annotations for stereochemical units that Lean cannot yet infer
directly from the lightweight parser. -/
structure IndexedNoncenterStereoAnnotations where
  axes : List IndexedDetectedAxialUnit := []
  planes : List IndexedDetectedPlanarUnit := []
  helices : List IndexedDetectedHelicalUnit := []
  conformations : List IndexedDetectedConformationalState := []
  ensembles : List IndexedDetectedEnsembleState := []
  auxiliaryRule5Nodes : List IndexedDetectedAuxiliaryRule5Node := []
  phantomNodes : List IndexedDetectedPhantomNode := []
  lonePairNodes : List IndexedDetectedLonePairNode := []
  deriving DecidableEq, Repr

namespace ChemistryNormalizationResult

/-- Convert a normalized parser atom index to the proof-facing `Fin atomCount` atom type. -/
def atomFin? (result : ChemistryNormalizationResult) (idx : ℕ) :
    Option (Fin result.parsed.atomCount) :=
  if h : idx < result.parsed.atomCount then some ⟨idx, h⟩ else none

/-- Convert a list of normalized parser atom indices to proof-facing atoms, refusing the whole
annotation if any index is invalid. -/
def atomFinList? (result : ChemistryNormalizationResult) :
    List ℕ → Option (List (Fin result.parsed.atomCount))
  | [] => some []
  | idx :: rest => do
      let atom ← result.atomFin? idx
      let atoms ← result.atomFinList? rest
      some (atom :: atoms)

/-- Register one parsed double-bond assignment as an official non-center unit when both endpoints
are valid proof-facing atoms. -/
def detectedDoubleBondRecord? (result : ChemistryNormalizationResult)
    (assignment : ℕ × ℕ × DoubleBondStereo) :
    Option (DetectedDoubleBondUnit (Fin result.parsed.atomCount)) := do
  let left ← result.atomFin? assignment.1
  let right ← result.atomFin? assignment.2.1
  let stereo? := result.perceivedDoubleBondStereo? assignment.1 assignment.2.1
  some { left := left, right := right, stereo? := stereo? }

/-- Register all parsed double-bond records as non-center detector records. -/
def detectedDoubleBondRecords (result : ChemistryNormalizationResult) :
    List (DetectedDoubleBondUnit (Fin result.parsed.atomCount)) :=
  result.stereobonds.doubleBondAssignments.filterMap result.detectedDoubleBondRecord?

/-- Register all parsed double bonds as official alkene/cumulene-style units, seeding Rule-3 facts
when directional stereobond semantics determine `E/Z`. -/
def detectedDoubleBondUnits (result : ChemistryNormalizationResult) :
    List (OfficialDetectedUnit (Fin result.parsed.atomCount)) :=
  result.detectedDoubleBondRecords.map fun unit =>
    OfficialDetectedUnit.ofDoubleBond unit.left unit.right unit.stereo?

/-- All oriented parsed double-bond endpoints.  Both orientations are retained so path matching is
independent of parser bond direction. -/
def parsedDoubleBondOrientations (result : ChemistryNormalizationResult) : List (ℕ × ℕ) :=
  result.parsed.bonds.flatMap fun bond =>
    if bond.kind = ParsedBondKind.double then
      [(bond.source, bond.target), (bond.target, bond.source)]
    else
      []

/-- Length-three cumulene path candidates made from adjacent parsed double bonds.  The endpoint
inequality avoids immediate two-atom backtracking, and the endpoint order removes the reverse
orientation duplicate. -/
def parsedCumulenePathCandidates (result : ChemistryNormalizationResult) : List (ℕ × ℕ × ℕ) :=
  (result.parsedDoubleBondOrientations).flatMap fun first =>
    (result.parsedDoubleBondOrientations).filterMap fun second =>
      if first.2 = second.1 ∧ first.1 ≠ second.2 ∧ first.1 < second.2 then
        some (first.1, first.2, second.2)
      else
        none

/-- Register one parsed length-three cumulene path as a detector record when all atoms are valid. -/
def detectedCumuleneRecord? (result : ChemistryNormalizationResult)
    (path : ℕ × ℕ × ℕ) :
    Option (DetectedCumuleneUnit (Fin result.parsed.atomCount)) := do
  let left ← result.atomFin? path.1
  let middle ← result.atomFin? path.2.1
  let right ← result.atomFin? path.2.2
  some { path := [left, middle, right], stereo? := none }

/-- Register all parser-visible length-three cumulenes as non-center detector records. -/
def detectedCumuleneRecords (result : ChemistryNormalizationResult) :
    List (DetectedCumuleneUnit (Fin result.parsed.atomCount)) :=
  result.parsedCumulenePathCandidates.filterMap result.detectedCumuleneRecord?

/-- Register one parsed length-three cumulene path as an unassigned axial candidate. -/
def detectedCumuleneAxisCandidateRecord? (result : ChemistryNormalizationResult)
    (path : ℕ × ℕ × ℕ) :
    Option (DetectedAxialCandidateUnit (Fin result.parsed.atomCount)) := do
  let axisStart ← result.atomFin? path.1
  let middle ← result.atomFin? path.2.1
  let axisEnd ← result.atomFin? path.2.2
  some { axisStart := axisStart, axisEnd := axisEnd, support := [axisStart, middle, axisEnd].toFinset }

/-- Register all parser-visible length-three cumulenes as unassigned axial candidates. -/
def detectedCumuleneAxisCandidateRecords (result : ChemistryNormalizationResult) :
    List (DetectedAxialCandidateUnit (Fin result.parsed.atomCount)) :=
  result.parsedCumulenePathCandidates.filterMap result.detectedCumuleneAxisCandidateRecord?

/-- Register one validated aromatic cycle as an unassigned planar candidate. -/
def detectedAromaticPlanarCandidateRecord? (result : ChemistryNormalizationResult)
    (cycle : AromaticCycle) :
    Option (DetectedPlanarCandidateUnit (Fin result.parsed.atomCount)) :=
  if cycle.valid result.parsed then
    match result.atomFinList? cycle.atoms with
    | some atoms => some { planeAtoms := atoms }
    | none => none
  else
    none

/-- Register all validated aromatic cycles as unassigned planar candidates. -/
def detectedAromaticPlanarCandidateRecords (result : ChemistryNormalizationResult) :
    List (DetectedPlanarCandidateUnit (Fin result.parsed.atomCount)) :=
  result.aromaticCycles.filterMap result.detectedAromaticPlanarCandidateRecord?

/-- Parser-visible single-bond conformational candidates.  Directional single bonds are included
because they still have single-bond order in the normalized graph, while aromatic and multiple
bonds are excluded from this coarse conformational frontier. -/
def parsedConformationalBondCandidates (result : ChemistryNormalizationResult) :
    List (ℕ × ℕ) :=
  result.parsed.bonds.filterMap fun bond =>
    match bond.kind with
    | ParsedBondKind.single | ParsedBondKind.up | ParsedBondKind.down =>
        some (bond.source, bond.target)
    | _ => none

/-- Register one parser-visible single bond as an unassigned conformational candidate. -/
def detectedConformationalCandidateRecord? (result : ChemistryNormalizationResult)
    (bond : ℕ × ℕ) :
    Option (DetectedConformationalState (Fin result.parsed.atomCount)) := do
  let left ← result.atomFin? bond.1
  let right ← result.atomFin? bond.2
  some { support := [left, right].toFinset, kind? := none }

/-- Register all parser-visible single bonds as unassigned conformational candidates. -/
def detectedConformationalCandidateRecords (result : ChemistryNormalizationResult) :
    List (DetectedConformationalState (Fin result.parsed.atomCount)) :=
  result.parsedConformationalBondCandidates.filterMap result.detectedConformationalCandidateRecord?

/-- Convert an indexed external axis annotation into a proof-facing assignment. -/
def detectedAxialRecord? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedAxialUnit) :
    Option (AxialAssignment (Fin result.parsed.atomCount)) := do
  let axisStart ← result.atomFin? record.axisStart
  let axisEnd ← result.atomFin? record.axisEnd
  let startHigh ← result.atomFin? record.startHigh
  let startLow ← result.atomFin? record.startLow
  let endHigh ← result.atomFin? record.endHigh
  let endLow ← result.atomFin? record.endLow
  some
    { unit :=
        { axisStart := axisStart
          axisEnd := axisEnd
          startHigh := startHigh
          startLow := startLow
          endHigh := endHigh
          endLow := endLow }
      descriptor := record.descriptor }

/-- Convert an indexed external planar annotation into a proof-facing assignment. -/
def detectedPlanarRecord? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedPlanarUnit) :
    Option (PlanarAssignment (Fin result.parsed.atomCount)) := do
  let planeAtoms ← result.atomFinList? record.planeAtoms
  let pilotAtom ← result.atomFin? record.pilotAtom
  let highReference ← result.atomFin? record.highReference
  let lowReference ← result.atomFin? record.lowReference
  some
    { unit :=
        { planeAtoms := planeAtoms
          pilotAtom := pilotAtom
          highReference := highReference
          lowReference := lowReference }
      descriptor := record.descriptor }

/-- Convert an indexed external helical annotation into a proof-facing assignment. -/
def detectedHelicalRecord? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedHelicalUnit) :
    Option (HelicalAssignment (Fin result.parsed.atomCount)) := do
  let helixPath ← result.atomFinList? record.helixPath
  let frontReference ← result.atomFin? record.frontReference
  let backReference ← result.atomFin? record.backReference
  some
    { unit :=
        { helixPath := helixPath
          frontReference := frontReference
          backReference := backReference }
      descriptor := record.descriptor }

/-- Convert an indexed external conformational annotation into a proof-facing detector record. -/
def detectedConformationalState? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedConformationalState) :
    Option (DetectedConformationalState (Fin result.parsed.atomCount)) := do
  let support ← result.atomFinList? record.support
  some { support := support.toFinset, kind? := record.kind? }

/-- Convert an indexed external ensemble annotation into a proof-facing detector record. -/
def detectedEnsembleState? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedEnsembleState) :
    Option (DetectedEnsembleState (Fin result.parsed.atomCount)) := do
  let support ← result.atomFinList? record.support
  some { support := support.toFinset, kind? := record.kind? }

/-- Convert an indexed external auxiliary-node annotation into a proof-facing detector record. -/
def detectedAuxiliaryRule5Node? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedAuxiliaryRule5Node) :
    Option (DetectedAuxiliaryRule5Node (Fin result.parsed.atomCount)) := do
  let anchor ← result.atomFin? record.anchor
  let support ← result.atomFinList? record.support
  some
    { anchor := anchor
      support := support.toFinset
      descriptor := record.descriptor
      rootDistance? := record.rootDistance? }

/-- Convert an indexed external phantom-node annotation into a proof-facing detector record. -/
def detectedPhantomNode? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedPhantomNode) :
    Option (DetectedPhantomNode (Fin result.parsed.atomCount)) := do
  let anchor ← result.atomFin? record.anchor
  let support ← result.atomFinList? record.support
  some { anchor := anchor, support := support.toFinset, rootDistance? := record.rootDistance? }

/-- Convert an indexed external lone-pair-node annotation into a proof-facing detector record. -/
def detectedLonePairNode? (result : ChemistryNormalizationResult)
    (record : IndexedDetectedLonePairNode) :
    Option (DetectedLonePairNode (Fin result.parsed.atomCount)) := do
  let anchor ← result.atomFin? record.anchor
  let support ← result.atomFinList? record.support
  some { anchor := anchor, support := support.toFinset, rootDistance? := record.rootDistance? }

/-- Parser-backed detector bundle plus importer/toolkit-supplied indexed non-center annotations. -/
def officialNoncenterDetectorBundleWith (result : ChemistryNormalizationResult)
    (annotations : IndexedNoncenterStereoAnnotations := {}) :
    OfficialNoncenterDetectorBundle (Fin result.parsed.atomCount) where
  doubleBonds := result.detectedDoubleBondRecords
  cumulenes := result.detectedCumuleneRecords
  axisCandidates := result.detectedCumuleneAxisCandidateRecords
  axes := annotations.axes.filterMap result.detectedAxialRecord?
  planeCandidates := result.detectedAromaticPlanarCandidateRecords
  planes := annotations.planes.filterMap result.detectedPlanarRecord?
  helices := annotations.helices.filterMap result.detectedHelicalRecord?
  conformationCandidates := result.detectedConformationalCandidateRecords
  conformations := annotations.conformations.filterMap result.detectedConformationalState?
  ensembles := annotations.ensembles.filterMap result.detectedEnsembleState?
  auxiliaryRule5Nodes :=
    annotations.auxiliaryRule5Nodes.filterMap result.detectedAuxiliaryRule5Node?
  phantomNodes := annotations.phantomNodes.filterMap result.detectedPhantomNode?
  lonePairNodes := annotations.lonePairNodes.filterMap result.detectedLonePairNode?

/-- Parser-backed detector bundle for non-tetrahedral units visible in the normalized intake. -/
def officialNoncenterDetectorBundle (result : ChemistryNormalizationResult) :
    OfficialNoncenterDetectorBundle (Fin result.parsed.atomCount) :=
  result.officialNoncenterDetectorBundleWith {}

/-- Production-facing official unit detection populated from normalized double-bond
stereochemistry, graph-visible length-three cumulene paths, unassigned cumulene-axis candidates,
validated aromatic planar candidates, and parser-visible single-bond conformational candidates.
Additional detectors can append assigned axes, planes, helices, conformational states, ensemble
states, phantom/lone-pair nodes, and auxiliary descriptor nodes using the constructors above. -/
def officialUnitDetectionResult (result : ChemistryNormalizationResult) :
    OfficialUnitDetectionResult (Fin result.parsed.atomCount) :=
  result.officialNoncenterDetectorBundle.toDetectionResult

/-- Production-facing official unit detection with importer/toolkit-supplied indexed annotations. -/
def officialUnitDetectionResultWith (result : ChemistryNormalizationResult)
    (annotations : IndexedNoncenterStereoAnnotations := {}) :
    OfficialUnitDetectionResult (Fin result.parsed.atomCount) :=
  (result.officialNoncenterDetectorBundleWith annotations).toDetectionResult

end ChemistryNormalizationResult

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {Unit : Type*} [DecidableEq Unit]

/-- Search one descriptor-unit source against later sources for the first distinct pair carrying
Rule-5 facts. -/
def firstRule5PairWithDescriptorUnitSource? {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit) (source : BranchDescriptorUnitSource m Unit) :
    List (BranchDescriptorUnitSource m Unit) →
      Option (OfficialRule5Descriptor × OfficialRule5Descriptor)
  | [] => none
  | other :: rest =>
      if other.unit ≠ source.unit then
        match env.rule5Descriptor source.unit, env.rule5Descriptor other.unit with
        | some leftDescriptor, some rightDescriptor => some (leftDescriptor, rightDescriptor)
        | _, _ => firstRule5PairWithDescriptorUnitSource? env source rest
      else
        firstRule5PairWithDescriptorUnitSource? env source rest

/-- First distinct descriptor-unit source pair carrying Rule-5 descriptors. -/
def firstDistinctDescriptorUnitSourceRule5Pair? {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit) :
    List (BranchDescriptorUnitSource m Unit) →
      Option (OfficialRule5Descriptor × OfficialRule5Descriptor)
  | [] => none
  | source :: sources =>
      match firstRule5PairWithDescriptorUnitSource? env source sources with
      | some pair => some pair
      | none => firstDistinctDescriptorUnitSourceRule5Pair? env sources

@[simp] theorem firstDistinctDescriptorUnitSourceRule5Pair?_cons_cons_of_unit_ne_rule5
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit)
    (left right : BranchDescriptorUnitSource m Unit)
    (rest : List (BranchDescriptorUnitSource m Unit))
    {leftDescriptor rightDescriptor : OfficialRule5Descriptor}
    (hunit : right.unit ≠ left.unit)
    (hleft : env.rule5Descriptor left.unit = some leftDescriptor)
    (hright : env.rule5Descriptor right.unit = some rightDescriptor) :
    firstDistinctDescriptorUnitSourceRule5Pair? env (left :: right :: rest) =
      some (leftDescriptor, rightDescriptor) := by
  simp [firstDistinctDescriptorUnitSourceRule5Pair?, firstRule5PairWithDescriptorUnitSource?,
    hunit, hleft, hright]

/-- Build an official ligand context from descriptor sources found on branch frontier nodes. -/
def officialContextOfDescriptorUnitSources {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit)
    (sources : List (BranchDescriptorUnitSource m Unit)) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  let base :=
    match sources.head? with
    | some source => env.toOfficialLigandRuleContext source.unit
    | none => CIPRuleEngine.OfficialLigandRuleContext.empty
  match firstDistinctDescriptorUnitSourceRule5Pair? env sources with
  | some (leftDescriptor, rightDescriptor) =>
      base.withRule4bPair (OfficialRule5Descriptor.pairKind leftDescriptor rightDescriptor)
  | none => base

@[simp] theorem officialContextOfDescriptorUnitSources_nil
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit) :
    officialContextOfDescriptorUnitSources (m := m) env [] =
      CIPRuleEngine.OfficialLigandRuleContext.empty := by
  rfl

theorem officialContextOfDescriptorUnitSources_rule4bPair?_of_two_distinct_rule5
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit)
    (left right : BranchDescriptorUnitSource m Unit)
    (rest : List (BranchDescriptorUnitSource m Unit))
    {leftDescriptor rightDescriptor : OfficialRule5Descriptor}
    (hunit : right.unit ≠ left.unit)
    (hleft : env.rule5Descriptor left.unit = some leftDescriptor)
    (hright : env.rule5Descriptor right.unit = some rightDescriptor) :
    (officialContextOfDescriptorUnitSources env (left :: right :: rest)).rule4bPair? =
      some (OfficialRule5Descriptor.pairKind leftDescriptor rightDescriptor) := by
  simp [officialContextOfDescriptorUnitSources,
    firstDistinctDescriptorUnitSourceRule5Pair?_cons_cons_of_unit_ne_rule5 env left right rest
      hunit hleft hright,
    CIPRuleEngine.OfficialLigandRuleContext.withRule4bPair]

/-- Search one source against later frontier sources for the first distinct pair carrying Rule-5
facts. -/
def firstRule5PairWithFrontierSource? {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit) (source : BranchFrontierUnitSource m Unit) :
    List (BranchFrontierUnitSource m Unit) →
      Option (OfficialRule5Descriptor × OfficialRule5Descriptor)
  | [] => none
  | other :: rest =>
      if other.unit ≠ source.unit then
        match env.rule5Descriptor source.unit, env.rule5Descriptor other.unit with
        | some leftDescriptor, some rightDescriptor => some (leftDescriptor, rightDescriptor)
        | _, _ => firstRule5PairWithFrontierSource? env source rest
      else
        firstRule5PairWithFrontierSource? env source rest

/-- First distinct registered-unit pair carrying Rule-5 descriptors. -/
def firstDistinctFrontierRule5DescriptorPair? {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit) :
    List (BranchFrontierUnitSource m Unit) →
      Option (OfficialRule5Descriptor × OfficialRule5Descriptor)
  | [] => none
  | source :: sources =>
      match firstRule5PairWithFrontierSource? env source sources with
      | some pair => some pair
      | none => firstDistinctFrontierRule5DescriptorPair? env sources

@[simp] theorem firstDistinctFrontierRule5DescriptorPair?_cons_cons_of_unit_ne_rule5
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit)
    (left right : BranchFrontierUnitSource m Unit)
    (rest : List (BranchFrontierUnitSource m Unit))
    {leftDescriptor rightDescriptor : OfficialRule5Descriptor}
    (hunit : right.unit ≠ left.unit)
    (hleft : env.rule5Descriptor left.unit = some leftDescriptor)
    (hright : env.rule5Descriptor right.unit = some rightDescriptor) :
    firstDistinctFrontierRule5DescriptorPair? env (left :: right :: rest) =
      some (leftDescriptor, rightDescriptor) := by
  simp [firstDistinctFrontierRule5DescriptorPair?, firstRule5PairWithFrontierSource?,
    hunit, hleft, hright]

/-- Build an official ligand context from registered units found at branch-frontier atoms. -/
def officialContextOfFrontierUnitSources {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit)
    (sources : List (BranchFrontierUnitSource m Unit)) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  let base :=
    match sources.head? with
    | some source => env.toOfficialLigandRuleContext source.unit
    | none => CIPRuleEngine.OfficialLigandRuleContext.empty
  match firstDistinctFrontierRule5DescriptorPair? env sources with
  | some (leftDescriptor, rightDescriptor) =>
      base.withRule4bPair (OfficialRule5Descriptor.pairKind leftDescriptor rightDescriptor)
  | none => base

@[simp] theorem officialContextOfFrontierUnitSources_nil
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit) :
    officialContextOfFrontierUnitSources (m := m) env [] =
      CIPRuleEngine.OfficialLigandRuleContext.empty := by
  rfl

theorem officialContextOfFrontierUnitSources_rule4bPair?_of_two_distinct_rule5
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit)
    (left right : BranchFrontierUnitSource m Unit)
    (rest : List (BranchFrontierUnitSource m Unit))
    {leftDescriptor rightDescriptor : OfficialRule5Descriptor}
    (hunit : right.unit ≠ left.unit)
    (hleft : env.rule5Descriptor left.unit = some leftDescriptor)
    (hright : env.rule5Descriptor right.unit = some rightDescriptor) :
    (officialContextOfFrontierUnitSources env (left :: right :: rest)).rule4bPair? =
      some (OfficialRule5Descriptor.pairKind leftDescriptor rightDescriptor) := by
  simp [officialContextOfFrontierUnitSources,
    firstDistinctFrontierRule5DescriptorPair?_cons_cons_of_unit_ne_rule5 env left right rest
      hunit hleft hright,
    CIPRuleEngine.OfficialLigandRuleContext.withRule4bPair]

namespace MultiCenterMolecule

variable (m : MultiCenterMolecule V)

/-- Descriptor-unit sources found in an official hierarchical-digraph frontier, including
phantom, lone-pair, auxiliary, and duplicate nodes. -/
def officialNodeDescriptorUnitSources
    (env : OfficialDescriptorEnvironment Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    (center : m.Center) (i : Fin 4)
    (frontier : List (OfficialCIPNode V)) :
    List (BranchDescriptorUnitSource m Unit) :=
  frontier.flatMap fun node =>
    match DescriptorSourceBranchPolicy.sourceKindOfOfficialNode node with
    | none => []
    | some sourceKind =>
        (policy.unitsAtOfficialNode node).filterMap fun unit =>
          if env.hasAnyValue unit && policy.includeNodeSource center i node sourceKind unit then
            some
              { atom? := node.current?
                node? := some node
                sourceKind := sourceKind
                unit := unit }
          else
            none

/-- Descriptor-unit sources found at one branch frontier depth by a duplicate-aware policy. -/
def branchDescriptorUnitSourcesAtDepth
    (env : OfficialDescriptorEnvironment Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    (center : m.Center) (i : Fin 4) (depth : ℕ) :
    List (BranchDescriptorUnitSource m Unit) :=
  let stateSources :=
    (m.branchFrontier center i depth).flatMap fun state =>
      let sourceKind :=
        if state.isDuplicate then
          BranchDescriptorSourceKind.duplicateAtom
        else
          BranchDescriptorSourceKind.atomSupport
      (policy.unitsAtAtom state.current).filterMap fun unit =>
        if env.hasAnyValue unit && policy.includeStateSource center i state sourceKind unit then
          some { atom? := some state.current, sourceKind := sourceKind, unit := unit }
        else
          none
  let nodeSources :=
    m.officialNodeDescriptorUnitSources env policy center i
      (policy.officialNodesAtDepth center i depth)
  stateSources ++ nodeSources

/-- Descriptor-unit sources found while walking a branch by increasing frontier depth. -/
def branchDescriptorUnitSourcesFrom
    (env : OfficialDescriptorEnvironment Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    (center : m.Center) (i : Fin 4) (depth : ℕ) :
    ℕ → List (BranchDescriptorUnitSource m Unit)
  | 0 => m.branchDescriptorUnitSourcesAtDepth env policy center i depth
  | fuel + 1 =>
      m.branchDescriptorUnitSourcesAtDepth env policy center i depth ++
        branchDescriptorUnitSourcesFrom env policy center i (depth + 1) fuel

/-- Descriptor-unit sources found up to a branch-walk fuel bound. -/
def branchDescriptorUnitSourcesWithin
    (env : OfficialDescriptorEnvironment Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    List (BranchDescriptorUnitSource m Unit) :=
  m.branchDescriptorUnitSourcesFrom env policy center i 0 fuel

/-- Official branch context from duplicate/virtual-aware descriptor-unit sources. -/
def officialBranchContextFromDescriptorSourcePolicyWithin
    (env : OfficialDescriptorEnvironment Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  officialContextOfDescriptorUnitSources
    env (m.branchDescriptorUnitSourcesWithin env policy center i fuel)

/-- Official branch context from duplicate/virtual-aware detector output. -/
def officialBranchContextFromDescriptorSourceDetectorWithin
    (output : OfficialDetectorOutput Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    (scheduleFuel branchFuel : ℕ)
    (center : m.Center) (i : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialBranchContextFromDescriptorSourcePolicyWithin
    (output.finalEnvironment scheduleFuel) policy center i branchFuel

/-- Feed duplicate/virtual-aware descriptor-source contexts into the canonical official comparator. -/
def cipOfficialCompareAtFromDescriptorSourceDetectorWithin
    (output : OfficialDetectorOutput Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    (scheduleFuel branchFuel : ℕ)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialCompareAt
    (fun queryCenter queryIndex =>
      m.officialBranchContextFromDescriptorSourceDetectorWithin output policy scheduleFuel branchFuel
        queryCenter queryIndex)
    center i j

/-- Duplicate/virtual-aware branch contexts are stable once the descriptor environment is fixed. -/
theorem officialBranchContextFromDescriptorSourceDetectorWithin_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel)
    (center : m.Center) (i : Fin 4) :
    m.officialBranchContextFromDescriptorSourceDetectorWithin output policy
        (scheduleFuel + 1) branchFuel center i =
      m.officialBranchContextFromDescriptorSourceDetectorWithin output policy
        scheduleFuel branchFuel center i := by
  have henv := output.finalEnvironment_succ_eq_self_of_fixedAt h
  rw [officialBranchContextFromDescriptorSourceDetectorWithin,
    officialBranchContextFromDescriptorSourceDetectorWithin, henv]

/-- Duplicate/virtual-aware comparisons are stable once the descriptor environment is fixed. -/
theorem cipOfficialCompareAtFromDescriptorSourceDetectorWithin_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (policy : DescriptorSourceBranchPolicy m Unit)
    {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel)
    (center : m.Center) (i j : Fin 4) :
    m.cipOfficialCompareAtFromDescriptorSourceDetectorWithin output policy
        (scheduleFuel + 1) branchFuel center i j =
      m.cipOfficialCompareAtFromDescriptorSourceDetectorWithin output policy
        scheduleFuel branchFuel center i j := by
  rw [cipOfficialCompareAtFromDescriptorSourceDetectorWithin,
    cipOfficialCompareAtFromDescriptorSourceDetectorWithin]
  apply congrArg (fun context => m.cipOfficialCompareAt context center i j)
  funext queryCenter queryIndex
  exact m.officialBranchContextFromDescriptorSourceDetectorWithin_succ_eq_of_fixedAt output policy
    branchFuel h queryCenter queryIndex

/-- Registered units found at one branch frontier depth by an atom-to-unit policy. -/
def branchFrontierUnitSourcesAtDepth
    (env : OfficialDescriptorEnvironment Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    (center : m.Center) (i : Fin 4) (depth : ℕ) :
    List (BranchFrontierUnitSource m Unit) :=
  (m.branchFrontier center i depth).flatMap fun state =>
    (policy.unitsAtAtom state.current).filterMap fun unit =>
      if env.hasAnyValue unit && policy.includeSource center i state unit then
        some { atom := state.current, unit := unit }
      else
        none

/-- Registered units found while walking a branch by increasing frontier depth. -/
def branchFrontierUnitSourcesFrom
    (env : OfficialDescriptorEnvironment Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    (center : m.Center) (i : Fin 4) (depth : ℕ) :
    ℕ → List (BranchFrontierUnitSource m Unit)
  | 0 => m.branchFrontierUnitSourcesAtDepth env policy center i depth
  | fuel + 1 =>
      m.branchFrontierUnitSourcesAtDepth env policy center i depth ++
        branchFrontierUnitSourcesFrom env policy center i (depth + 1) fuel

/-- Registered units found up to a branch-walk fuel bound. -/
def branchFrontierUnitSourcesWithin
    (env : OfficialDescriptorEnvironment Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    List (BranchFrontierUnitSource m Unit) :=
  m.branchFrontierUnitSourcesFrom env policy center i 0 fuel

/-- Official branch context from registered non-center/center units found on frontier atoms. -/
def officialBranchContextFromFrontierPolicyWithin
    (env : OfficialDescriptorEnvironment Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  officialContextOfFrontierUnitSources
    env (m.branchFrontierUnitSourcesWithin env policy center i fuel)

/-- Official branch context from detector output and a branch-frontier atom-to-unit policy. -/
def officialBranchContextFromFrontierDetectorWithin
    (output : OfficialDetectorOutput Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    (scheduleFuel branchFuel : ℕ)
    (center : m.Center) (i : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialBranchContextFromFrontierPolicyWithin
    (output.finalEnvironment scheduleFuel) policy center i branchFuel

/-- Feed branch-frontier detector contexts into the canonical official comparator. -/
def cipOfficialCompareAtFromFrontierDetectorWithin
    (output : OfficialDetectorOutput Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    (scheduleFuel branchFuel : ℕ)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialCompareAt
    (fun queryCenter queryIndex =>
      m.officialBranchContextFromFrontierDetectorWithin output policy scheduleFuel branchFuel
        queryCenter queryIndex)
    center i j

/-- Branch-frontier detector contexts are stable once the descriptor environment is fixed. -/
theorem officialBranchContextFromFrontierDetectorWithin_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel)
    (center : m.Center) (i : Fin 4) :
    m.officialBranchContextFromFrontierDetectorWithin output policy
        (scheduleFuel + 1) branchFuel center i =
      m.officialBranchContextFromFrontierDetectorWithin output policy
        scheduleFuel branchFuel center i := by
  have henv := output.finalEnvironment_succ_eq_self_of_fixedAt h
  rw [officialBranchContextFromFrontierDetectorWithin,
    officialBranchContextFromFrontierDetectorWithin, henv]

/-- Branch-frontier detector comparisons are stable once the descriptor environment is fixed. -/
theorem cipOfficialCompareAtFromFrontierDetectorWithin_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (policy : BranchFrontierUnitPolicy m Unit)
    {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel)
    (center : m.Center) (i j : Fin 4) :
    m.cipOfficialCompareAtFromFrontierDetectorWithin output policy
        (scheduleFuel + 1) branchFuel center i j =
      m.cipOfficialCompareAtFromFrontierDetectorWithin output policy
        scheduleFuel branchFuel center i j := by
  rw [cipOfficialCompareAtFromFrontierDetectorWithin,
    cipOfficialCompareAtFromFrontierDetectorWithin]
  apply congrArg (fun context => m.cipOfficialCompareAt context center i j)
  funext queryCenter queryIndex
  exact m.officialBranchContextFromFrontierDetectorWithin_succ_eq_of_fixedAt output policy
    branchFuel h queryCenter queryIndex

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
