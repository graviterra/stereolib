import TetraStereo.OneCenter.CIPRule3DescriptorBearingEndpointAffineInvariance
import TetraStereo.OneCenter.LocalizedCyclicDoubleBondDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def LocalizedCyclicCumuleneComponent.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (component : input.LocalizedCyclicCumuleneComponent)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedCyclicCumuleneComponent :=
  { representative := component.representative }

def LocalizedMonocyclicDoubleBond.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (carrier : input.LocalizedMonocyclicDoubleBond)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedMonocyclicDoubleBond :=
  { ring := carrier.ring }

@[simp] theorem localizedOrderTwoNeighbors_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (atom : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedOrderTwoNeighbors atom =
      input.localizedOrderTwoNeighbors atom := by
  unfold localizedOrderTwoNeighbors
  simp only [moleculeGraph_mapSpatialPoints]
  congr

@[simp] theorem localizedOrderTwoSimpleGraph_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedOrderTwoSimpleGraph =
      input.localizedOrderTwoSimpleGraph := by
  ext left right
  simp

@[simp] theorem localizedOrderTwoComponentAtoms_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (representative : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedOrderTwoComponentAtoms representative =
      input.localizedOrderTwoComponentAtoms representative := by
  classical
  apply Finset.ext
  intro atom
  simp

@[simp] theorem declarativeLocalizedCyclicCumuleneComponentAt_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (representative : input.Atom) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedCyclicCumuleneComponentAt
        representative ↔
      input.DeclarativeLocalizedCyclicCumuleneComponentAt representative := by
  unfold DeclarativeLocalizedCyclicCumuleneComponentAt
  simp only [localizedOrderTwoComponentAtoms_mapSpatialPoints,
    localizedOrderTwoNeighbors_mapSpatialPoints]
  exact Iff.intro id id

@[simp] theorem localizedCovalentComponentAtoms_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (representative : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedCovalentComponentAtoms representative =
      input.localizedCovalentComponentAtoms representative := by
  classical
  apply Finset.ext
  intro atom
  simp [localizedCovalentComponentAtoms]

@[simp] theorem localizedCycleNeighbors_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (vertices : Finset input.Atom) (atom : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedCycleNeighbors vertices atom =
      input.localizedCycleNeighbors vertices atom := by
  unfold localizedCycleNeighbors
  simp only [moleculeGraph_mapSpatialPoints]
  congr

@[simp] theorem localizedInducedCycleGraph_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (vertices : Finset input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedInducedCycleGraph vertices =
      input.localizedInducedCycleGraph vertices := by
  ext left right
  simp

@[simp] theorem declarativeLocalizedSimpleCycleVertexSet_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (vertices : Finset input.Atom) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedSimpleCycleVertexSet vertices ↔
      input.DeclarativeLocalizedSimpleCycleVertexSet vertices := by
  unfold DeclarativeLocalizedSimpleCycleVertexSet
  simp only [localizedCycleNeighbors_mapSpatialPoints,
    localizedInducedCycleGraph_mapSpatialPoints]
  exact Iff.intro id id

@[simp] theorem localizedSimpleCycleVertexSetsInComponent_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (representative : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedSimpleCycleVertexSetsInComponent representative =
      input.localizedSimpleCycleVertexSetsInComponent representative := by
  classical
  apply Finset.ext
  intro vertices
  simp

@[simp] theorem localizedDoubleBondCountIn_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (vertices : Finset input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedDoubleBondCountIn vertices =
      input.localizedDoubleBondCountIn vertices := by
  unfold localizedDoubleBondCountIn
  simp only [moleculeGraph_mapSpatialPoints]
  congr

noncomputable def LocalizedMonocyclicDoubleBond.unmapSpatialPoints
    {input : CertifiedLocalizedCIPInput} (mapPoint : CartesianPoint3 → CartesianPoint3)
    (carrier : (input.mapSpatialPoints mapPoint).LocalizedMonocyclicDoubleBond) :
    input.LocalizedMonocyclicDoubleBond :=
  { ring := carrier.ring }

@[simp] theorem LocalizedMonocyclicDoubleBond.map_unmapSpatialPoints
    {input : CertifiedLocalizedCIPInput} (mapPoint : CartesianPoint3 → CartesianPoint3)
    (carrier : (input.mapSpatialPoints mapPoint).LocalizedMonocyclicDoubleBond) :
    (carrier.unmapSpatialPoints mapPoint).mapSpatialPoints mapPoint = carrier := by
  cases carrier
  rfl

@[simp] theorem LocalizedMonocyclicDoubleBond.unmap_mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} (mapPoint : CartesianPoint3 → CartesianPoint3)
    (carrier : input.LocalizedMonocyclicDoubleBond) :
    (carrier.mapSpatialPoints mapPoint).unmapSpatialPoints mapPoint = carrier := by
  cases carrier
  rfl

@[simp] theorem declarativeLocalizedMonocyclicDoubleBond_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.Atom) (carrier : input.LocalizedMonocyclicDoubleBond) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedMonocyclicDoubleBond
        left right (carrier.mapSpatialPoints mapPoint) ↔
      input.DeclarativeLocalizedMonocyclicDoubleBond left right carrier := by
  unfold DeclarativeLocalizedMonocyclicDoubleBond
  simp only [moleculeGraph_mapSpatialPoints,
    LocalizedMonocyclicDoubleBond.mapSpatialPoints,
    declarativeLocalizedSimpleCycleVertexSet_mapSpatialPoints,
    localizedCovalentComponentAtoms_mapSpatialPoints,
    localizedDoubleBondCountIn_mapSpatialPoints]
  exact Iff.intro id id

theorem localizedMonocyclicDoubleBondAt?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedMonocyclicDoubleBondAt? left right =
      (input.localizedMonocyclicDoubleBondAt? left right).map
        (fun carrier => carrier.mapSpatialPoints mapPoint) := by
  cases sourceEq : input.localizedMonocyclicDoubleBondAt? left right with
  | some carrier =>
      have sourceDerived :=
        (input.localizedMonocyclicDoubleBondAt?_eq_some_iff left right carrier).mp
          sourceEq
      have targetDerived :=
        (declarativeLocalizedMonocyclicDoubleBond_mapSpatialPoints
          input mapPoint left right carrier).mpr sourceDerived
      have targetEq :=
        ((input.mapSpatialPoints mapPoint).localizedMonocyclicDoubleBondAt?_eq_some_iff
            left right (carrier.mapSpatialPoints mapPoint)).mpr targetDerived
      simp [targetEq]
  | none =>
      have sourceAbsent :=
        (input.localizedMonocyclicDoubleBondAt?_eq_none_iff left right).mp sourceEq
      have targetAbsent : ∀ carrier,
          ¬ (input.mapSpatialPoints mapPoint).DeclarativeLocalizedMonocyclicDoubleBond
            left right carrier := by
        intro carrier targetDerived
        let sourceCarrier := carrier.unmapSpatialPoints mapPoint
        have mappedDerived :
            (input.mapSpatialPoints mapPoint).DeclarativeLocalizedMonocyclicDoubleBond
              left right (sourceCarrier.mapSpatialPoints mapPoint) := by
          simpa [sourceCarrier] using targetDerived
        have sourceDerived :=
          (declarativeLocalizedMonocyclicDoubleBond_mapSpatialPoints
            input mapPoint left right sourceCarrier).mp mappedDerived
        exact sourceAbsent sourceCarrier sourceDerived
      have targetEq :=
        ((input.mapSpatialPoints mapPoint).localizedMonocyclicDoubleBondAt?_eq_none_iff
          left right).mpr targetAbsent
      simp [targetEq]

def LocalizedMonocyclicDoubleBondPolicyResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput}
    (result : input.LocalizedMonocyclicDoubleBondPolicyResult)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedMonocyclicDoubleBondPolicyResult :=
  { carrier := result.carrier.mapSpatialPoints mapPoint
    doubleBondCount := result.doubleBondCount
    policy := result.policy }

theorem localizedMonocyclicDoubleBondPolicyAt?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (left right : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedMonocyclicDoubleBondPolicyAt? left right =
      (input.localizedMonocyclicDoubleBondPolicyAt? left right).map
        (fun result => result.mapSpatialPoints mapPoint) := by
  unfold localizedMonocyclicDoubleBondPolicyAt?
  rw [localizedMonocyclicDoubleBondAt?_mapSpatialPoints]
  cases input.localizedMonocyclicDoubleBondAt? left right with
  | none => rfl
  | some carrier =>
      dsimp
      rw [localizedDoubleBondCountIn_mapSpatialPoints]
      simp only [LocalizedMonocyclicDoubleBond.mapSpatialPoints]
      cases BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
          carrier.ring.card (input.localizedDoubleBondCountIn carrier.ring) <;>
        simp [LocalizedMonocyclicDoubleBondPolicyResult.mapSpatialPoints,
          LocalizedMonocyclicDoubleBond.mapSpatialPoints]

theorem localizedCyclicCumuleneComponentAt?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (representative : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedCyclicCumuleneComponentAt? representative =
      (input.localizedCyclicCumuleneComponentAt? representative).map
        (fun component => component.mapSpatialPoints mapPoint) := by
  unfold localizedCyclicCumuleneComponentAt?
  have predicateEq := declarativeLocalizedCyclicCumuleneComponentAt_mapSpatialPoints
    input mapPoint representative
  by_cases source : input.DeclarativeLocalizedCyclicCumuleneComponentAt representative
  · have target := predicateEq.mpr source
    rw [if_pos target, if_pos source]
    rfl
  · have notTarget :
        ¬ (input.mapSpatialPoints mapPoint).DeclarativeLocalizedCyclicCumuleneComponentAt
          representative :=
      fun target => source (predicateEq.mp target)
    rw [if_neg notTarget, if_neg source]
    rfl

noncomputable def LocalizedCyclicCumuleneComponent.unmapSpatialPoints
    {input : CertifiedLocalizedCIPInput} (mapPoint : CartesianPoint3 → CartesianPoint3)
    (component : (input.mapSpatialPoints mapPoint).LocalizedCyclicCumuleneComponent) :
    input.LocalizedCyclicCumuleneComponent :=
  { representative := component.representative }

@[simp] theorem LocalizedCyclicCumuleneComponent.map_unmapSpatialPoints
    {input : CertifiedLocalizedCIPInput} (mapPoint : CartesianPoint3 → CartesianPoint3)
    (component : (input.mapSpatialPoints mapPoint).LocalizedCyclicCumuleneComponent) :
    (component.unmapSpatialPoints mapPoint).mapSpatialPoints mapPoint = component := by
  cases component
  rfl

@[simp] theorem LocalizedCyclicCumuleneComponent.unmap_mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} (mapPoint : CartesianPoint3 → CartesianPoint3)
    (component : input.LocalizedCyclicCumuleneComponent) :
    (component.mapSpatialPoints mapPoint).unmapSpatialPoints mapPoint = component := by
  cases component
  rfl

@[simp] theorem declarativeLocalizedCyclicCumuleneComponentContains_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (component : input.LocalizedCyclicCumuleneComponent) (atom : input.Atom) :
    (input.mapSpatialPoints mapPoint).DeclarativeLocalizedCyclicCumuleneComponentContains
        (component.mapSpatialPoints mapPoint) atom ↔
      input.DeclarativeLocalizedCyclicCumuleneComponentContains component atom := by
  unfold DeclarativeLocalizedCyclicCumuleneComponentContains
    DeclarativeLocalizedCyclicCumuleneComponent
  simp only [LocalizedCyclicCumuleneComponent.mapSpatialPoints,
    declarativeLocalizedCyclicCumuleneComponentAt_mapSpatialPoints,
    localizedOrderTwoComponentAtoms_mapSpatialPoints]

theorem localizedCyclicCumuleneComponentContaining?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) (mapPoint : CartesianPoint3 → CartesianPoint3)
    (atom : input.Atom) :
    (input.mapSpatialPoints mapPoint).localizedCyclicCumuleneComponentContaining? atom =
      (input.localizedCyclicCumuleneComponentContaining? atom).map
        (fun component => component.mapSpatialPoints mapPoint) := by
  cases sourceEq : input.localizedCyclicCumuleneComponentContaining? atom with
  | some component =>
      have sourceDerived :=
        (input.localizedCyclicCumuleneComponentContaining?_eq_some_iff
          atom component).mp sourceEq
      have targetDerived :=
        (declarativeLocalizedCyclicCumuleneComponentContains_mapSpatialPoints
          input mapPoint component atom).mpr sourceDerived
      have targetEq :=
        ((input.mapSpatialPoints mapPoint).localizedCyclicCumuleneComponentContaining?_eq_some_iff atom
            (component.mapSpatialPoints mapPoint)).mpr targetDerived
      simp [targetEq]
  | none =>
      have sourceAbsent :=
        (input.localizedCyclicCumuleneComponentContaining?_eq_none_iff atom).mp sourceEq
      have targetAbsent : ∀ component,
          ¬ (input.mapSpatialPoints mapPoint).DeclarativeLocalizedCyclicCumuleneComponentContains
            component atom := by
        intro component targetDerived
        let sourceComponent := component.unmapSpatialPoints mapPoint
        have mappedDerived :
            (input.mapSpatialPoints mapPoint).DeclarativeLocalizedCyclicCumuleneComponentContains
                (sourceComponent.mapSpatialPoints mapPoint) atom := by
          simpa [sourceComponent] using targetDerived
        have sourceDerived :=
          (declarativeLocalizedCyclicCumuleneComponentContains_mapSpatialPoints
            input mapPoint sourceComponent atom).mp mappedDerived
        exact sourceAbsent sourceComponent sourceDerived
      have targetEq :=
        ((input.mapSpatialPoints mapPoint).localizedCyclicCumuleneComponentContaining?_eq_none_iff
          atom).mpr targetAbsent
      simp [targetEq]

def LocalizedRule3RingClosureMoleculeRoute.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (route : input.LocalizedRule3RingClosureMoleculeRoute fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3RingClosureMoleculeRoute fuel :=
  match route with
  | .ordinaryCyclicDoubleBondSystem initial closure =>
      .ordinaryCyclicDoubleBondSystem (initial.mapSpatialPoints mapPoint)
        (closure.mapSpatialPoints mapPoint)
  | .fullyCyclicCumulene initial closure component =>
      .fullyCyclicCumulene (initial.mapSpatialPoints mapPoint)
        (closure.mapSpatialPoints mapPoint) (component.mapSpatialPoints mapPoint)

@[simp] theorem localizedRule3RingClosureMoleculeRoute?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3RingClosureMoleculeRoute?
        (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3RingClosureMoleculeRoute? occurrence).map
        (fun route => route.mapSpatialPoints mapPoint) := by
  unfold localizedRule3RingClosureMoleculeRoute?
  rw [localizedRule3CumulatedAxisEntry?_mapSpatialPoints]
  cases entryEq : input.localizedRule3CumulatedAxisEntry? occurrence with
  | none => rfl
  | some entry =>
      dsimp
      cases entry with
      | terminalStart initial | internal initial previous | branched initial first second rest =>
          rfl
      | ringClosure initial closure =>
          simp only [LocalizedRule3CumulatedAxisEntry.mapSpatialPoints,
            LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
          rw [localizedCyclicCumuleneComponentContaining?_mapSpatialPoints]
          cases input.localizedCyclicCumuleneComponentContaining? initial.left <;>
            simp [LocalizedRule3RingClosureMoleculeRoute.mapSpatialPoints,
              LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]

def LocalizedRule3CyclicAuthorityRoute.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (route : input.LocalizedRule3CyclicAuthorityRoute fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3CyclicAuthorityRoute fuel :=
  match route with
  | .fullyCyclicCumulene initial closure component =>
      .fullyCyclicCumulene (initial.mapSpatialPoints mapPoint)
        (closure.mapSpatialPoints mapPoint) (component.mapSpatialPoints mapPoint)
  | .ordinaryMonocyclicPolicy initial closure result =>
      .ordinaryMonocyclicPolicy (initial.mapSpatialPoints mapPoint)
        (closure.mapSpatialPoints mapPoint) (result.mapSpatialPoints mapPoint)
  | .ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount =>
      .ordinaryMonocyclicPolicyGap (initial.mapSpatialPoints mapPoint)
        (closure.mapSpatialPoints mapPoint) (carrier.mapSpatialPoints mapPoint)
          doubleBondCount
  | .ordinaryNonmonocyclic initial closure =>
      .ordinaryNonmonocyclic (initial.mapSpatialPoints mapPoint)
        (closure.mapSpatialPoints mapPoint)

@[simp] theorem localizedRule3CyclicAuthorityRoute?_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3CyclicAuthorityRoute?
        (occurrence.mapSpatialPoints mapPoint) =
      (input.localizedRule3CyclicAuthorityRoute? occurrence).map
        (fun route => route.mapSpatialPoints mapPoint) := by
  unfold localizedRule3CyclicAuthorityRoute?
  rw [localizedRule3RingClosureMoleculeRoute?_mapSpatialPoints]
  cases routeEq : input.localizedRule3RingClosureMoleculeRoute? occurrence with
  | none => rfl
  | some route =>
      dsimp
      cases route with
      | fullyCyclicCumulene initial closure component =>
          rfl
      | ordinaryCyclicDoubleBondSystem initial closure =>
          simp only [LocalizedRule3RingClosureMoleculeRoute.mapSpatialPoints,
            LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
          rw [localizedMonocyclicDoubleBondAt?_mapSpatialPoints]
          cases input.localizedMonocyclicDoubleBondAt? initial.left initial.right with
          | none =>
              simp [LocalizedRule3CyclicAuthorityRoute.mapSpatialPoints,
                LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]
          | some carrier =>
              dsimp
              rw [localizedDoubleBondCountIn_mapSpatialPoints]
              simp only [LocalizedMonocyclicDoubleBond.mapSpatialPoints]
              cases policyEq : BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
                  carrier.ring.card (input.localizedDoubleBondCountIn carrier.ring) <;>
                simp [LocalizedRule3CyclicAuthorityRoute.mapSpatialPoints,
                  LocalizedMonocyclicDoubleBondPolicyResult.mapSpatialPoints,
                  LocalizedMonocyclicDoubleBond.mapSpatialPoints,
                  LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints]

def LocalizedRule3RequiredMonocyclicEZResult.mapSpatialPoints
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (result : input.LocalizedRule3RequiredMonocyclicEZResult fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).LocalizedRule3RequiredMonocyclicEZResult fuel :=
  { initial := result.initial.mapSpatialPoints mapPoint
    closure := result.closure.mapSpatialPoints mapPoint
    policyResult := result.policyResult.mapSpatialPoints mapPoint
    leftCompilation := result.leftCompilation.mapSpatialPoints mapPoint
    rightCompilation := result.rightCompilation.mapSpatialPoints mapPoint
    unit := result.unit.mapSpatialPoints mapPoint
    descriptor := result.descriptor }

theorem localizedRule3RequiredMonocyclicEZWith?_affine
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (transform : RationalAffineFrameTransform)
    (mappedRule3FrameOf :
      List ((input.mapSpatialPoints transform.applyPoint).LocalizedRerootCursor carrierFuel) →
        Option (input.mapSpatialPoints transform.applyPoint).LocalizedRule3CanonicalKeyFrame)
    (rule3FrameNatural : ∀ cursors,
      mappedRule3FrameOf
          (cursors.map fun cursor => cursor.mapSpatialPoints transform.applyPoint) =
        (rule3FrameOf cursors).map
          (fun frame => frame.mapSpatialPoints transform.applyPoint))
    (determinantNonzero : transform.determinant ≠ 0) :
    (input.mapSpatialPoints transform.applyPoint).localizedRule3RequiredMonocyclicEZWith?
        (target.mapSpatialPoints transform.applyPoint)
        (occurrence.mapSpatialPoints transform.applyPoint)
        (view.mapSpatialPoints transform.applyPoint) mappedRule3FrameOf =
      (input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf).map
          (fun result => result.mapSpatialPoints transform.applyPoint) := by
  unfold localizedRule3RequiredMonocyclicEZWith?
  rw [localizedRule3CyclicAuthorityRoute?_mapSpatialPoints]
  cases routeEq : input.localizedRule3CyclicAuthorityRoute? occurrence with
  | none => rfl
  | some route =>
      dsimp
      cases route with
      | fullyCyclicCumulene initial closure component
      | ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount
      | ordinaryNonmonocyclic initial closure => rfl
      | ordinaryMonocyclicPolicy initial closure policyResult =>
          simp only [LocalizedRule3CyclicAuthorityRoute.mapSpatialPoints,
            LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints,
            LocalizedMonocyclicDoubleBondPolicyResult.mapSpatialPoints]
          cases policyEq : policyResult.policy with
          | permanentlyOmit => rfl
          | requireEZ =>
              dsimp
              rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
                input target view rule3FrameOf transform.applyPoint mappedRule3FrameOf
                  rule3FrameNatural]
              cases leftEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                  target view rule3FrameOf initial.left initial.right initial.leftCursor with
              | none => rfl
              | some leftCompilation =>
                  dsimp
                  rw [buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_mapSpatialPoints
                    input target view rule3FrameOf transform.applyPoint mappedRule3FrameOf
                      rule3FrameNatural]
                  cases rightEq : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                      target view rule3FrameOf initial.right initial.left initial.rightCursor with
                  | none => rfl
                  | some rightCompilation =>
                      dsimp
                      simp only [LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints]
                      rw [localizedRule3DescriptorBearingSpatialUnit?_affine
                        input initial.left initial.right leftCompilation.endpointFrame
                          rightCompilation.endpointFrame transform determinantNonzero]
                      cases unitEq : input.localizedRule3DescriptorBearingSpatialUnit?
                          initial.left initial.right leftCompilation.endpointFrame
                            rightCompilation.endpointFrame with
                      | none => rfl
                      | some unit =>
                          dsimp
                          simp only [LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints,
                            LocalizedRule3EndpointPriority.mapSpatialPoints,
                            LocalizedMonocyclicDoubleBond.mapSpatialPoints]
                          cases geometryEq : monocyclicSeniorLigandGeometryOfRule3?
                              unit.geometry with
                          | none =>
                              simp [LocalizedRule3RequiredMonocyclicEZResult.mapSpatialPoints,
                                LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints,
                                LocalizedMonocyclicDoubleBondPolicyResult.mapSpatialPoints,
                                LocalizedMonocyclicDoubleBond.mapSpatialPoints,
                                LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints]
                          | some cyclicGeometry =>
                              cases descriptorEq :
                                  BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?
                                    policyResult.carrier.ring.card
                                      policyResult.doubleBondCount cyclicGeometry <;>
                                simp [LocalizedRule3RequiredMonocyclicEZResult.mapSpatialPoints,
                                  descriptorEq, policyEq,
                                  LocalizedRule3PhysicalEndpointCursorFrame.mapSpatialPoints,
                                  LocalizedMonocyclicDoubleBondPolicyResult.mapSpatialPoints,
                                  LocalizedMonocyclicDoubleBond.mapSpatialPoints,
                                  LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
                                  LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints,
                                  LocalizedRule3EndpointPriority.mapSpatialPoints]

@[simp] theorem localizedRule3RequiredMonocyclicEZObservation_mapSpatialPoints
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (result : input.LocalizedRule3RequiredMonocyclicEZResult fuel)
    (mapPoint : CartesianPoint3 → CartesianPoint3) :
    (input.mapSpatialPoints mapPoint).localizedRule3RequiredMonocyclicEZObservation
        (result.mapSpatialPoints mapPoint) =
      (input.localizedRule3RequiredMonocyclicEZObservation result).mapSpatialPoints mapPoint := by
  unfold localizedRule3RequiredMonocyclicEZObservation
  simp only [LocalizedRule3RequiredMonocyclicEZResult.mapSpatialPoints,
    LocalizedRule3DescriptorBearingSpatialUnitResult.mapSpatialPoints,
    LocalizedRule3EndpointPriority.mapSpatialPoints,
    LocalizedRule3OccurrenceEndpointKeyFrame.mapSpatialPoints,
    LocalizedRule3EndpointKeyFrame.mapSpatialPoints]
  cases result.unit.leftPriority <;> cases result.unit.rightPriority <;>
    rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
