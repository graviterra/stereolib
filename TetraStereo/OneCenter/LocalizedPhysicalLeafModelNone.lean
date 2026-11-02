import TetraStereo.OneCenter.LocalizedWholeStateDescriptorLocality

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-!
# Physical leaf occurrences are nonbearing in the actual Rule-45 model

An *actual physical* occurrence is a provenance-bearing node whose provenance is
`OfficialCIPNodeProvenance.realAtom` and whose current atom is a genuine molecule atom.  This
module proves that such an occurrence cannot be a detected degree-four tetrahedral center when
its physical atom has at most one neighbor.  Automatic tetrahedral detection is exactly the
four-neighbor graph predicate, so the detection guard of the occurrence descriptor refuses.

The consequences are then transported through the *actual* whole-state Rule-4a--5 evaluator:

* the bare occurrence descriptor refuses for every dependency view;
* the whole-state descriptor refuses for every complete state;
* every fixed point of the whole-state step stores `none` at such an occurrence;
* every `CIPModel` of the concrete Rule-45 occurrence system stores `none` there; and
* the whole-state cursor reader, which maps an occurrence reader to a reroot-cursor reader,
  reads `none` at a cursor carrying such an occurrence.

No descriptor refusal, callback refusal or successful-read premise is supplied: every result is
derived from the real graph-degree guard and the actual fixed-point equation.
-/

/-- A real physical atom occurrence: the node denotes a real atom (not a duplicate or phantom
provenance) and its current atom is `atom`. -/
def ActualPhysicalAtomAtNode (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (atom : input.Atom) : Prop :=
  node.provenance = OfficialCIPNodeProvenance.realAtom ∧ node.current? = some atom

/-- The occurrence-level form of `ActualPhysicalAtomAtNode`. -/
def ActualPhysicalOccurrenceAt (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) (atom : input.Atom) : Prop :=
  input.ActualPhysicalAtomAtNode occurrence.1.node atom

theorem actualPhysicalOccurrenceAt_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) (atom : input.Atom) :
    input.ActualPhysicalOccurrenceAt occurrence atom ↔
      input.ActualPhysicalAtomAtNode occurrence.1.node atom :=
  Iff.rfl

/-! ## Degree-one atoms are not detected tetrahedral centers -/

/-- An atom with at most one semantic localized neighbor is not an automatically detected
tetrahedral center. -/
theorem not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1) :
    atom ∉ input.tetrahedralCenterSet := by
  intro detected
  have cardEq :=
    (input.mem_tetrahedralCenterSet_iff_semantic_neighbor_count atom).mp detected
  exact absurd (cardEq ▸ cardLe) (by decide)

/-- Graph-neighbor form of the same degree bound. -/
theorem not_mem_tetrahedralCenterSet_of_neighborFinset_card_le_one
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1) :
    atom ∉ input.tetrahedralCenterSet := by
  have semanticLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1 := by
    rw [input.neighborFinset_eq_semanticLocalizedNeighborFinset atom] at cardLe
    exact cardLe
  exact input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom semanticLe

/-- Generic executable center lookup refusal outside the detected center set. -/
theorem tetrahedralCenterAt?_eq_none_of_not_mem
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (notMem : atom ∉ input.tetrahedralCenterSet) :
    input.tetrahedralCenterAt? atom = none := by
  unfold tetrahedralCenterAt?
  exact dif_neg notMem

/-- Semantic degree form of the executable center lookup refusal. -/
theorem tetrahedralCenterAt?_eq_none_of_semanticNeighbor_card_le_one
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1) :
    input.tetrahedralCenterAt? atom = none :=
  input.tetrahedralCenterAt?_eq_none_of_not_mem atom
    (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe)

/-- Graph-neighbor degree form of the executable center lookup refusal. -/
theorem tetrahedralCenterAt?_eq_none_of_neighborFinset_card_le_one
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1) :
    input.tetrahedralCenterAt? atom = none :=
  input.tetrahedralCenterAt?_eq_none_of_not_mem atom
    (input.not_mem_tetrahedralCenterSet_of_neighborFinset_card_le_one atom cardLe)

/-- Executable real-node center recognition refuses whenever its current atom is not detected.
The provenance guard is handled definitionally; no real-provenance hypothesis is needed. -/
theorem realTetrahedralCenterAtNode?_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (atom : input.Atom)
    (current : node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet) :
    input.realTetrahedralCenterAtNode? node = none := by
  unfold realTetrahedralCenterAtNode?
  by_cases real : node.provenance = OfficialCIPNodeProvenance.realAtom
  · rw [if_pos real, current]
    exact input.tetrahedralCenterAt?_eq_none_of_not_mem atom notMem
  · rw [if_neg real]

/-- No center subtype is a real tetrahedral-center occurrence of a physically leaf-like node. -/
theorem not_realTetrahedralCenterNode_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    (center : input.TetrahedralCenter) :
    ¬ input.RealTetrahedralCenterNode node center := by
  intro real
  have currentEq : node.current? = some center.1 := real.2
  have centerEq : center.1 = atom :=
    Option.some.inj (currentEq.symm.trans actual.2)
  have centerMem : center.1 ∈ input.tetrahedralCenterSet := center.2
  exact (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe)
    (centerEq ▸ centerMem)

/-- Real-node center recognition refuses at a physical occurrence with degree at most one. -/
theorem realTetrahedralCenterAtNode?_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1) :
    input.realTetrahedralCenterAtNode? node = none := by
  exact input.realTetrahedralCenterAtNode?_eq_none_of_current_not_mem node atom actual.2
    (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe)

/-- Graph-neighbor form at physical occurrences. -/
theorem realTetrahedralCenterAtNode?_eq_none_of_actualPhysical_neighborCard_le_one
    (input : CertifiedLocalizedCIPInput)
    (node : OfficialCIPNode input.Atom) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1) :
    input.realTetrahedralCenterAtNode? node = none := by
  exact input.realTetrahedralCenterAtNode?_eq_none_of_current_not_mem node atom actual.2
    (input.not_mem_tetrahedralCenterSet_of_neighborFinset_card_le_one atom cardLe)

/-! ## The occurrence center guard refuses -/

/-- The occurrence descriptor-center lookup refuses at an actual physical occurrence whose atom
has at most one semantic localized neighbor. -/
theorem localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1) :
    input.localizedOccurrenceDescriptorCenter? target = none := by
  unfold localizedOccurrenceDescriptorCenter?
  exact input.realTetrahedralCenterAtNode?_eq_none_of_actualPhysical_leaf
    target.1.node atom actual cardLe

/-- Graph-neighbor form of the occurrence center refusal. -/
theorem localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_neighborCard_le_one
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1) :
    input.localizedOccurrenceDescriptorCenter? target = none := by
  unfold localizedOccurrenceDescriptorCenter?
  exact input.realTetrahedralCenterAtNode?_eq_none_of_actualPhysical_neighborCard_le_one
    target.1.node atom actual cardLe

/-! ## The bare Rule-45 occurrence descriptor refuses for every view -/

/-- If the center guard refuses, the bare occurrence Rule-45 descriptor refuses for every
dependency view. -/
theorem localizedOccurrenceRule45Descriptor?_eq_none_of_center?_eq_none
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.localizedOccurrenceRule45Descriptor? target view = none := by
  unfold localizedOccurrenceRule45Descriptor? localizedOccurrenceRule45SpatialEvidence?
  rw [centerComputed]
  rfl

/-- The bare Rule-45 occurrence descriptor refuses at every dependency view of an actual
physical leaf occurrence. -/
theorem localizedOccurrenceRule45Descriptor?_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45Descriptor? target view = none :=
  input.localizedOccurrenceRule45Descriptor?_eq_none_of_center?_eq_none target view
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_leaf
      target atom actual cardLe)

/-- Graph-neighbor form of the bare descriptor refusal for every view. -/
theorem localizedOccurrenceRule45Descriptor?_eq_none_of_actualPhysical_neighborCard_le_one
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45Descriptor? target view = none :=
  input.localizedOccurrenceRule45Descriptor?_eq_none_of_center?_eq_none target view
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_neighborCard_le_one
      target atom actual cardLe)

/-! ## The actual whole-state evaluator refuses -/

/-- If the center guard refuses, the whole-state Rule-45 descriptor refuses for every state. -/
theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_center?_eq_none
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state = none := by
  rw [input.localizedOccurrenceRule45WholeStateDescriptor?_eq_restricted_of_center?_eq_none
    target state centerComputed]
  exact input.localizedOccurrenceRule45Descriptor?_eq_none_of_center?_eq_none
    target (input.localizedDependencyView state target) centerComputed

/-- The actual whole-state Rule-45 descriptor refuses at an actual physical leaf occurrence. -/
theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    (state : input.LocalizedAuxiliaryState fuel) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state = none :=
  input.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_center?_eq_none
    target state
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_leaf
      target atom actual cardLe)

/-- Graph-neighbor form of the whole-state descriptor refusal. -/
theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_actualPhysical_neighborCard_le_one
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1)
    (state : input.LocalizedAuxiliaryState fuel) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state = none :=
  input.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_center?_eq_none
    target state
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_neighborCard_le_one
      target atom actual cardLe)

/-! ## The actual fixed point stores `none` -/

/-- Every fixed point of the actual whole-state Rule-45 step stores `none` at an occurrence whose
center guard refuses. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_center?_eq_none
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = none)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state) :
    state target = none := by
  have stepNone :=
    input.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_center?_eq_none
      target state centerComputed
  have fixedAt := congrFun fixed target
  calc
    state target = input.localizedOccurrenceRule45WholeStateStep state target := fixedAt.symm
    _ = none := stepNone

/-- Every fixed point of the actual whole-state Rule-45 step stores `none` at an actual physical
leaf occurrence. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state) :
    state target = none :=
  input.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_center?_eq_none
    target
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_leaf
      target atom actual cardLe)
    fixed

/-- Graph-neighbor form of the fixed-point refusal. -/
theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_actualPhysical_neighborCard_le_one
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state) :
    state target = none :=
  input.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_center?_eq_none
    target
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_neighborCard_le_one
      target atom actual cardLe)
    fixed

/-! ## The actual Rule-45 `CIPModel` stores `none` -/

/-- Every `CIPModel` of the concrete Rule-45 occurrence system stores `none` at an occurrence
whose center guard refuses.  The model is converted to the actual whole-state fixed point by the
unconditional `localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel_unconditional`. -/
theorem localizedOccurrenceRule45CIPModel_eq_none_of_center?_eq_none
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (centerComputed : input.localizedOccurrenceDescriptorCenter? target = none)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    state target = none := by
  have fixed : input.LocalizedWholeStateRule45FixedPoint fuel state :=
    (input.localizedOccurrenceRule45WholeStateFixedPoint_iff_cipModel_unconditional
      fuel state).mpr model
  exact input.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_center?_eq_none
    target centerComputed fixed

/-- Every `CIPModel` of the concrete Rule-45 occurrence system stores `none` at an actual
physical leaf occurrence.  This is the observation-label refusal required downstream. -/
theorem localizedOccurrenceRule45CIPModel_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    state target = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_center?_eq_none target
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_leaf
      target atom actual cardLe)
    model

/-- Graph-neighbor form of the model refusal. -/
theorem localizedOccurrenceRule45CIPModel_eq_none_of_actualPhysical_neighborCard_le_one
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode target.1.node atom)
    (cardLe : (input.moleculeGraph.neighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    state target = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_center?_eq_none target
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_neighborCard_le_one
      target atom actual cardLe)
    model

/-! ## General noncandidate atom forms

The degree bound is one way to obtain the noncandidate premise `atom ∉ tetrahedralCenterSet`.
The following statements take that premise directly, so they also apply to duplicate/placeholder
provenance whose current atom is any non-detected atom.  In that case the refusal comes from the
definitional provenance guard of `realTetrahedralCenterAtNode?`; it is not a degree claim about a
duplicate node. -/

theorem localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet) :
    input.localizedOccurrenceDescriptorCenter? target = none := by
  unfold localizedOccurrenceDescriptorCenter?
  exact input.realTetrahedralCenterAtNode?_eq_none_of_current_not_mem
    target.1.node atom current notMem

theorem localizedOccurrenceDescriptorCenter?_eq_none_of_current_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1) :
    input.localizedOccurrenceDescriptorCenter? target = none :=
  input.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem target atom current
    (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe)

theorem localizedOccurrenceRule45Descriptor?_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45Descriptor? target view = none :=
  input.localizedOccurrenceRule45Descriptor?_eq_none_of_center?_eq_none target view
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
      target atom current notMem)

theorem localizedOccurrenceRule45Descriptor?_eq_none_of_current_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceRule45Descriptor? target view = none :=
  input.localizedOccurrenceRule45Descriptor?_eq_none_of_current_not_mem target atom current
    (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe) view

theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet)
    (state : input.LocalizedAuxiliaryState fuel) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state = none :=
  input.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_center?_eq_none
    target state
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
      target atom current notMem)

theorem localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_current_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    (state : input.LocalizedAuxiliaryState fuel) :
    input.localizedOccurrenceRule45WholeStateDescriptor? target state = none :=
  input.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_current_not_mem
    target atom current
    (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe) state

theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state) :
    state target = none :=
  input.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_center?_eq_none
    target
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
      target atom current notMem)
    fixed

theorem localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_current_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (fixed : input.LocalizedWholeStateRule45FixedPoint fuel state) :
    state target = none :=
  input.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_current_not_mem
    target atom current
    (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe) fixed

/-- General noncandidate form: a `CIPModel` stores `none` at any physical occurrence whose current
atom is not a detected tetrahedral center. -/
theorem localizedOccurrenceRule45CIPModel_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    state target = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_center?_eq_none target
    (input.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
      target atom current notMem)
    model

/-- General noncandidate form with an explicit physical degree bound. -/
theorem localizedOccurrenceRule45CIPModel_eq_none_of_current_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (atom : input.Atom)
    (current : target.1.node.current? = some atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    state target = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_current_not_mem target atom current
    (input.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one atom cardLe) model

/-! ## Reroot-cursor readers

`localizedOccurrenceRule45WholeStateReader` is the occurrence reader composed with
`cursor.occurrence`.  The wrapper below exposes that composition independently, so downstream
twin/reroot consumers can use the occurrence result at a cursor without unfolding the whole-state
descriptor. -/

/-- Map an occurrence reader to a reroot-cursor reader by reading the occurrence carried by the
cursor. -/
def localizedRerootCursorReadOfOccurrence
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (read : input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel) :
    input.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel :=
  fun cursor => read cursor.occurrence

@[simp] theorem localizedRerootCursorReadOfOccurrence_apply
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (read : input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor fuel) :
    input.localizedRerootCursorReadOfOccurrence read cursor = read cursor.occurrence :=
  rfl

/-- The whole-state cursor reader is exactly the occurrence-reader wrapper at the whole state. -/
theorem localizedRerootCursorReadOfOccurrence_eq_wholeStateReader
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel) :
    input.localizedRerootCursorReadOfOccurrence state =
      input.localizedOccurrenceRule45WholeStateReader state :=
  rfl

/-- The actual whole-state cursor reader reads `none` at a cursor carrying an actual physical
leaf occurrence, whenever the state is a `CIPModel` of the concrete Rule-45 occurrence system. -/
theorem localizedOccurrenceRule45WholeStateReader_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode cursor.occurrence.1.node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    input.localizedOccurrenceRule45WholeStateReader state cursor = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_actualPhysical_leaf
    cursor.occurrence atom actual cardLe model

/-- The actual whole-state cursor reader reads `none` at a cursor carrying any physical
occurrence whose current atom is not a detected tetrahedral center. -/
theorem localizedOccurrenceRule45WholeStateReader_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (atom : input.Atom)
    (current : cursor.occurrence.1.node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    input.localizedOccurrenceRule45WholeStateReader state cursor = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_current_not_mem
    cursor.occurrence atom current notMem model

/-- The actual whole-state cursor reader reads `none` at a cursor carrying a physical leaf
occurrence (current atom of degree at most one). -/
theorem localizedOccurrenceRule45WholeStateReader_eq_none_of_current_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (atom : input.Atom)
    (current : cursor.occurrence.1.node.current? = some atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    input.localizedOccurrenceRule45WholeStateReader state cursor = none :=
  input.localizedOccurrenceRule45CIPModel_eq_none_of_current_leaf
    cursor.occurrence atom current cardLe model

/-- The occurrence-reader wrapper reads `none` at a cursor carrying any physical noncandidate
occurrence whenever the supplied reader agrees with a Rule-45 `CIPModel` state. -/
theorem localizedRerootCursorReadOfOccurrence_eq_none_of_current_not_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (read : input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor fuel) (atom : input.Atom)
    (current : cursor.occurrence.1.node.current? = some atom)
    (notMem : atom ∉ input.tetrahedralCenterSet)
    {state : input.LocalizedAuxiliaryState fuel}
    (readEq : read = state)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    input.localizedRerootCursorReadOfOccurrence read cursor = none := by
  rw [readEq]
  exact input.localizedOccurrenceRule45WholeStateReader_eq_none_of_current_not_mem
    cursor atom current notMem model

/-- The occurrence-reader wrapper reads `none` at a physical leaf cursor whenever the supplied
reader agrees with a Rule-45 `CIPModel` state. -/
theorem localizedRerootCursorReadOfOccurrence_eq_none_of_actualPhysical_leaf
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (read : input.LocalizedCIPOccurrence fuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor fuel) (atom : input.Atom)
    (actual : input.ActualPhysicalAtomAtNode cursor.occurrence.1.node atom)
    (cardLe : (input.semanticLocalizedNeighborFinset atom).card ≤ 1)
    {state : input.LocalizedAuxiliaryState fuel}
    (readEq : read = state)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state) :
    input.localizedRerootCursorReadOfOccurrence read cursor = none := by
  rw [readEq]
  exact input.localizedOccurrenceRule45WholeStateReader_eq_none_of_actualPhysical_leaf
    cursor atom actual cardLe model

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalAtomAtNode
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalOccurrenceAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalOccurrenceAt_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_mem_tetrahedralCenterSet_of_semanticNeighbor_card_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_mem_tetrahedralCenterSet_of_neighborFinset_card_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralCenterAt?_eq_none_of_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralCenterAt?_eq_none_of_semanticNeighbor_card_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.tetrahedralCenterAt?_eq_none_of_neighborFinset_card_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realTetrahedralCenterAtNode?_eq_none_of_current_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.not_realTetrahedralCenterNode_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realTetrahedralCenterAtNode?_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realTetrahedralCenterAtNode?_eq_none_of_actualPhysical_neighborCard_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_eq_none_of_actualPhysical_neighborCard_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_none_of_center?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_none_of_actualPhysical_neighborCard_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_center?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_actualPhysical_neighborCard_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_center?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_actualPhysical_neighborCard_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45CIPModel_eq_none_of_center?_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45CIPModel_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45CIPModel_eq_none_of_actualPhysical_neighborCard_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorReadOfOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorReadOfOccurrence_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorReadOfOccurrence_eq_wholeStateReader
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateReader_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorReadOfOccurrence_eq_none_of_actualPhysical_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_eq_none_of_current_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceDescriptorCenter?_eq_none_of_current_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_none_of_current_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45Descriptor?_eq_none_of_current_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_current_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateDescriptor?_eq_none_of_current_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_current_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateFixedPoint_eq_none_of_current_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45CIPModel_eq_none_of_current_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45CIPModel_eq_none_of_current_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateReader_eq_none_of_current_not_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45WholeStateReader_eq_none_of_current_leaf
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootCursorReadOfOccurrence_eq_none_of_current_not_mem
