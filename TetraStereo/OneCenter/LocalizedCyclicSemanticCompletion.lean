import TetraStereo.OneCenter.LocalizedCyclicDoubleBondDescriptor
import TetraStereo.OneCenter.LocalizedRule3CumulatedChain

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput




















































































/-- The certified shorter-address parent list of a carrier frame is a singleton whenever it is
nonempty.  Root plus address is a functional coordinate of the deduplicated occurrence carrier. -/
theorem localizedCyclicCarrierParentFrames_eq_singleton_of_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {source parent : input.LocalizedCIPOccurrenceFrame}
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) source) :
    input.localizedCarrierParentFrames (fuel := fuel) source = [parent] := by
  have parentInFrames := present
  rw [localizedCarrierParentFrames, List.mem_filter] at present
  obtain ⟨parentPresent, parentConditions⟩ := present
  simp only [Bool.and_eq_true, beq_iff_eq] at parentConditions
  have parentDerived := (input.mem_localizedOccurrences_iff fuel parent).mp parentPresent
  have onlyParent : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) source →
        candidate = parent := by
    intro candidate candidatePresent
    rw [localizedCarrierParentFrames, List.mem_filter] at candidatePresent
    obtain ⟨candidatePresent, candidateConditions⟩ := candidatePresent
    simp only [Bool.and_eq_true, beq_iff_eq] at candidateConditions
    have candidateDerived :=
      (input.mem_localizedOccurrences_iff fuel candidate).mp candidatePresent
    exact input.declarativeLocalizedOccurrence_functional_at_root_address
      candidateDerived parentDerived
      (candidateConditions.1.1.trans parentConditions.1.1.symm)
      (candidateConditions.2.trans parentConditions.2.symm)
  have parentNodup :
      (input.localizedCarrierParentFrames (fuel := fuel) source).Nodup := by
    unfold localizedCarrierParentFrames
    exact (input.localizedOccurrences_nodup fuel).filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedCarrierParentFrames (fuel := fuel) source ↔
        candidate ∈ [parent] := by
    intro candidate
    constructor
    · intro candidatePresent
      simp [onlyParent candidate candidatePresent]
    · intro candidatePresent
      simp only [List.mem_singleton] at candidatePresent
      subst candidate
      exact parentInFrames
  have permutation :
      List.Perm (input.localizedCarrierParentFrames (fuel := fuel) source) [parent] :=
    (List.perm_ext_iff_of_nodup parentNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-- The executable singleton carrier-parent selection succeeds at any certified parent frame. -/
theorem localizedCyclicCarrierParentFrame?_eq_some_of_mem
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (parent : input.LocalizedCIPOccurrenceFrame)
    (present : parent ∈ input.localizedCarrierParentFrames (fuel := fuel) occurrence.1) :
    input.localizedRule3CarrierParentFrame? occurrence = some parent := by
  have singleton := localizedCyclicCarrierParentFrames_eq_singleton_of_mem input present
  simp [localizedRule3CarrierParentFrame?, singleton]

/-- Executable parent-occurrence recovery succeeds at the declarative carrier parent. -/
theorem localizedCyclicCarrierParentOccurrence?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence parent : input.LocalizedCIPOccurrence fuel)
    (decl : input.DeclarativeLocalizedRule3CarrierParentOccurrence occurrence parent) :
    input.localizedRule3CarrierParentOccurrence? occurrence = some parent := by
  classical
  have frameComputed : input.localizedRule3CarrierParentFrame? occurrence = some parent.1 :=
    localizedCyclicCarrierParentFrame?_eq_some_of_mem input occurrence parent.1 decl
  unfold localizedRule3CarrierParentOccurrence?
  rw [frameComputed]
  dsimp only
  rw [dif_pos parent.2]

/-- Every declarative physical endpoint frame is returned by the executable physical endpoint
recovery.  This is the constructive converse of
`localizedRule3PhysicalEndpointCursorFrame?_sound`, re-proved from the production definition. -/
theorem localizedCyclicPhysicalEndpointCursorFrame?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedRule3PhysicalEndpointCursorFrame fuel)
    (decl : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame occurrence frame) :
    input.localizedRule3PhysicalEndpointCursorFrame? occurrence = some frame := by
  obtain ⟨real, currentEq, parentEq, bondEq, carrierDecl, leftCurrent,
    leftPrevious, rightOccurrenceEq, rightPrevious⟩ := decl
  obtain ⟨left, right, leftCursor, rightCursor⟩ := frame
  obtain ⟨leftOccurrence, leftPrev⟩ := leftCursor
  obtain ⟨rightOccurrence, rightPrev⟩ := rightCursor
  dsimp only at leftCurrent leftPrevious rightOccurrenceEq rightPrevious ⊢
  have parentComputed :=
    localizedCyclicCarrierParentOccurrence?_eq_some_of_declarative
      input occurrence leftOccurrence carrierDecl
  unfold localizedRule3PhysicalEndpointCursorFrame?
  rw [if_pos real]
  simp only [currentEq, parentEq]
  try dsimp only
  rw [if_pos bondEq]
  rw [parentComputed]
  simp only [bind, Option.bind_some]
  rw [if_pos leftCurrent]
  simp only [Option.some.injEq]
  simp [leftPrevious, rightOccurrenceEq, rightPrevious]

/-- The executable continuation computation over one certified children list is exactly the
physical filter of that list. -/
theorem localizedCyclicAxisPhysicalContinuationCursors?_eq_some_filter
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    input.localizedRule3AxisPhysicalContinuationCursors? cursor =
      some (input.localizedRule3AxisPhysicalContinuationCursors cursor children) := by
  simp [localizedRule3AxisPhysicalContinuationCursors?, computed]

/-- A declarative singleton ring-closing continuation list forces the executable physical filter
to be exactly that singleton. -/
theorem localizedCyclicAxisPhysicalContinuationCursors_eq_singleton_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor next : input.LocalizedRerootCursor carrierFuel}
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (childrenComputed : input.localizedRerootChildren? cursor = some children)
    (derived :
      input.DeclarativeLocalizedRule3AxisPhysicalContinuationCursors cursor [next]) :
    input.localizedRule3AxisPhysicalContinuationCursors cursor children = [next] := by
  rcases derived with ⟨declared, declaredComputed, exactChildren, membership⟩
  have same : declared = children :=
    Option.some.inj (declaredComputed.symm.trans childrenComputed)
  subst declared
  have nextInFilter :
      next ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children := by
    rw [input.mem_localizedRule3AxisPhysicalContinuationCursors_iff]
    exact (membership next).mp (by simp)
  have onlyNext : ∀ candidate,
      candidate ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children →
        candidate = next := by
    intro candidate candidatePresent
    have characterized :=
      (input.mem_localizedRule3AxisPhysicalContinuationCursors_iff
        cursor candidate children).mp candidatePresent
    have inContinuations : candidate ∈ [next] := (membership candidate).mpr characterized
    simpa using inContinuations
  have childrenNodup : children.Nodup :=
    input.localizedRerootChildren_nodup cursor children exactChildren
  have filterNodup :
      (input.localizedRule3AxisPhysicalContinuationCursors cursor children).Nodup := by
    unfold localizedRule3AxisPhysicalContinuationCursors
    exact childrenNodup.filter _
  have sameMembers : ∀ candidate,
      candidate ∈ input.localizedRule3AxisPhysicalContinuationCursors cursor children ↔
        candidate ∈ [next] := by
    intro candidate
    constructor
    · intro candidatePresent
      simp [onlyNext candidate candidatePresent]
    · intro candidatePresent
      simp only [List.mem_singleton] at candidatePresent
      subst candidate
      exact nextInFilter
  have permutation :
      List.Perm (input.localizedRule3AxisPhysicalContinuationCursors cursor children) [next] :=
    (List.perm_ext_iff_of_nodup filterNodup (by simp)).mpr sameMembers
  exact List.perm_singleton.mp permutation

/-! ## Ring-closing topology recognition -/

/-- A declarative ring-closing axis topology is a singleton physical continuation list, so the
executable filter is exactly that singleton and the classifier returns the same closure cursor. -/
theorem localizedRule3AxisTopology?_eq_ringClosure_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3AxisTopology cursor (.ringClosure closure)) :
    input.localizedRule3AxisTopology? cursor = some (.ringClosure closure) := by
  cases derived with
  | ringClosure frame ring =>
      rcases frame with ⟨children, childrenComputed, exactChildren, membership⟩
      have filterSingleton :
          input.localizedRule3AxisPhysicalContinuationCursors cursor children = [closure] :=
        localizedCyclicAxisPhysicalContinuationCursors_eq_singleton_of_declarative
          input childrenComputed ⟨children, childrenComputed, exactChildren, membership⟩
      have continuationsComputed :=
        localizedCyclicAxisPhysicalContinuationCursors?_eq_some_filter
          input cursor children childrenComputed
      simp [localizedRule3AxisTopology?, continuationsComputed, filterSingleton, ring]

/-- A declarative ring-closing entry is recognized by the executable entry classifier at the
same physical endpoint frame and the same closure cursor. -/
theorem localizedRule3CumulatedAxisEntry?_eq_ringClosure_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3CumulatedAxisEntry occurrence
      (.ringClosure initial closure)) :
    input.localizedRule3CumulatedAxisEntry? occurrence =
      some (.ringClosure initial closure) := by
  cases derived with
  | ringClosure physical closureTopology =>
      have physicalComputed :=
        localizedCyclicPhysicalEndpointCursorFrame?_eq_some_of_declarative
          input occurrence initial physical
      have topologyComputed :=
        input.localizedRule3AxisTopology?_eq_ringClosure_of_declarative closureTopology
      simp [localizedRule3CumulatedAxisEntry?, physicalComputed, topologyComputed]

/-- An independent ordinary cyclic-double-bond-system molecule route is returned by the
executable molecule-route classifier at the same route. -/
theorem localizedRule3RingClosureMoleculeRoute?_complete_ordinary
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
      (.ordinaryCyclicDoubleBondSystem initial closure)) :
    input.localizedRule3RingClosureMoleculeRoute? occurrence =
      some (.ordinaryCyclicDoubleBondSystem initial closure) := by
  cases derived with
  | ordinaryCyclicDoubleBondSystem entry notFullyCyclic =>
      exact input.localizedRule3RingClosureMoleculeRoute?_eq_ordinary_of_not_contains
        occurrence initial closure
        (input.localizedRule3CumulatedAxisEntry?_eq_ringClosure_of_declarative entry)
        notFullyCyclic

/-- An independent fully cyclic cumulene molecule route is returned by the executable
molecule-route classifier at the same route, including the same component. -/
theorem localizedRule3RingClosureMoleculeRoute?_complete_fullyCyclic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {component : input.LocalizedCyclicCumuleneComponent}
    (derived : input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence
      (.fullyCyclicCumulene initial closure component)) :
    input.localizedRule3RingClosureMoleculeRoute? occurrence =
      some (.fullyCyclicCumulene initial closure component) := by
  cases derived with
  | fullyCyclicCumulene entry fullyCyclic =>
      exact input.localizedRule3RingClosureMoleculeRoute?_eq_fullyCyclic_of_contains
        occurrence initial closure component
        (input.localizedRule3CumulatedAxisEntry?_eq_ringClosure_of_declarative entry)
        fullyCyclic

/-- Every independent ring-closure molecule route is returned by the executable molecule-route
classifier at the same route. -/
theorem localizedRule3RingClosureMoleculeRoute?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (route : input.LocalizedRule3RingClosureMoleculeRoute carrierFuel)
    (derived : input.DeclarativeLocalizedRule3RingClosureMoleculeRoute occurrence route) :
    input.localizedRule3RingClosureMoleculeRoute? occurrence = some route := by
  cases route with
  | ordinaryCyclicDoubleBondSystem initial closure =>
      exact input.localizedRule3RingClosureMoleculeRoute?_complete_ordinary
        occurrence derived
  | fullyCyclicCumulene initial closure component =>
      exact input.localizedRule3RingClosureMoleculeRoute?_complete_fullyCyclic
        occurrence derived

/-! ## Cyclic authority route recognition and policy agreement -/

/-- An independent fully cyclic cumulene authority route is returned by the executable cyclic
classifier at the same route. -/
theorem localizedRule3CyclicAuthorityRoute?_complete_fullyCyclic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {component : input.LocalizedCyclicCumuleneComponent}
    (derived : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.fullyCyclicCumulene initial closure component)) :
    input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.fullyCyclicCumulene initial closure component) := by
  cases derived with
  | fullyCyclicCumulene moleculeRoute =>
      have moleculeComputed :=
        input.localizedRule3RingClosureMoleculeRoute?_complete occurrence
          (.fullyCyclicCumulene initial closure component) moleculeRoute
      simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed]

/-- An independent ordinary-monocyclic-policy authority route is returned by the executable
cyclic classifier at the same carrier, the same double-bond count that the executable recomputes
from that carrier's ring, and the same transcribed P-93 policy value. -/
theorem localizedRule3CyclicAuthorityRoute?_complete_policy
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {result : input.LocalizedMonocyclicDoubleBondPolicyResult}
    (derived : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryMonocyclicPolicy initial closure result)) :
    input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.ordinaryMonocyclicPolicy initial closure result) := by
  cases derived with
  | ordinaryMonocyclicPolicy moleculeRoute policyDerived =>
      have moleculeComputed :=
        input.localizedRule3RingClosureMoleculeRoute?_complete occurrence
          (.ordinaryCyclicDoubleBondSystem initial closure) moleculeRoute
      have carrierComputed :
          input.localizedMonocyclicDoubleBondAt? initial.left initial.right =
            some result.carrier :=
        (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
          initial.left initial.right result.carrier).mpr policyDerived.1
      have policyComputed' :
          BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy
              result.carrier.ring.card
              (input.localizedDoubleBondCountIn result.carrier.ring) =
            some result.policy := by
        rw [← policyDerived.2.1]
        exact policyDerived.2.2
      have payloadEq :
          ({ carrier := result.carrier
             doubleBondCount := input.localizedDoubleBondCountIn result.carrier.ring
             policy := result.policy } :
            input.LocalizedMonocyclicDoubleBondPolicyResult) = result := by
        rw [← policyDerived.2.1]
      have routeComputed :
          input.localizedRule3CyclicAuthorityRoute? occurrence =
            some (.ordinaryMonocyclicPolicy initial closure
              { carrier := result.carrier
                doubleBondCount := input.localizedDoubleBondCountIn result.carrier.ring
                policy := result.policy }) := by
        simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed, carrierComputed,
          policyComputed']
      simp [routeComputed, payloadEq]

/-- An independent ordinary-monocyclic policy-gap authority route is returned by the executable
cyclic classifier at the same carrier and the same recomputed double-bond count. -/
theorem localizedRule3CyclicAuthorityRoute?_complete_gap
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {carrier : input.LocalizedMonocyclicDoubleBond}
    {doubleBondCount : Nat}
    (derived : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount)) :
    input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount) := by
  cases derived with
  | ordinaryMonocyclicPolicyGap moleculeRoute monocycle countEq outsidePolicy =>
      have moleculeComputed :=
        input.localizedRule3RingClosureMoleculeRoute?_complete occurrence
          (.ordinaryCyclicDoubleBondSystem initial closure) moleculeRoute
      have carrierComputed :
          input.localizedMonocyclicDoubleBondAt? initial.left initial.right =
            some carrier :=
        (input.localizedMonocyclicDoubleBondAt?_eq_some_iff
          initial.left initial.right carrier).mpr monocycle
      have outsidePolicy' :
          BlueBookP93.Cyclic.MonocyclicDoubleBondPolicy carrier.ring.card
            (input.localizedDoubleBondCountIn carrier.ring) = none := by
        rw [← countEq]
        exact outsidePolicy
      have routeComputed :
          input.localizedRule3CyclicAuthorityRoute? occurrence =
            some (.ordinaryMonocyclicPolicyGap initial closure carrier
              (input.localizedDoubleBondCountIn carrier.ring)) := by
        simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed, carrierComputed,
          outsidePolicy']
      simp [routeComputed, countEq]

/-- An independent ordinary-nonmonocyclic authority route is returned by the executable cyclic
classifier at the same route. -/
theorem localizedRule3CyclicAuthorityRoute?_complete_nonmonocyclic
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryNonmonocyclic initial closure)) :
    input.localizedRule3CyclicAuthorityRoute? occurrence =
      some (.ordinaryNonmonocyclic initial closure) := by
  cases derived with
  | ordinaryNonmonocyclic moleculeRoute notMonocyclic =>
      have moleculeComputed :=
        input.localizedRule3RingClosureMoleculeRoute?_complete occurrence
          (.ordinaryCyclicDoubleBondSystem initial closure) moleculeRoute
      have carrierComputed :
          input.localizedMonocyclicDoubleBondAt? initial.left initial.right = none :=
        (input.localizedMonocyclicDoubleBondAt?_eq_none_iff
          initial.left initial.right).mpr notMonocyclic
      simp [localizedRule3CyclicAuthorityRoute?, moleculeComputed, carrierComputed]

/-- The converse of `localizedRule3CyclicAuthorityRoute?_sound`: every independent cyclic
authority route is the route the executable classifier returns.  This is exactly the
`cyclicRouteComplete` obligation of the original-node converse, with no compiled prerequisite
left open. -/
theorem localizedRule3CyclicAuthorityRoute?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (route : input.LocalizedRule3CyclicAuthorityRoute carrierFuel)
    (derived : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence route) :
    input.localizedRule3CyclicAuthorityRoute? occurrence = some route := by
  cases route with
  | fullyCyclicCumulene initial closure component =>
      exact input.localizedRule3CyclicAuthorityRoute?_complete_fullyCyclic
        occurrence derived
  | ordinaryMonocyclicPolicy initial closure result =>
      exact input.localizedRule3CyclicAuthorityRoute?_complete_policy
        occurrence derived
  | ordinaryMonocyclicPolicyGap initial closure carrier doubleBondCount =>
      exact input.localizedRule3CyclicAuthorityRoute?_complete_gap
        occurrence derived
  | ordinaryNonmonocyclic initial closure =>
      exact input.localizedRule3CyclicAuthorityRoute?_complete_nonmonocyclic
        occurrence derived

/-- The executable cyclic authority classifier and the independent route relation accept exactly
the same routes.  The forward direction is the existing soundness theorem; the reverse direction
is `localizedRule3CyclicAuthorityRoute?_complete`. -/
theorem localizedRule3CyclicAuthorityRoute?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (route : input.LocalizedRule3CyclicAuthorityRoute carrierFuel) :
    input.localizedRule3CyclicAuthorityRoute? occurrence = some route ↔
      input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence route :=
  ⟨input.localizedRule3CyclicAuthorityRoute?_sound occurrence route,
    input.localizedRule3CyclicAuthorityRoute?_complete occurrence route⟩

/-- The policy derivation carried by an independent ordinary-monocyclic authority route. -/
theorem DeclarativeLocalizedRule3CyclicAuthorityRoute.policy_of_ordinaryMonocyclicPolicy
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult}
    (route : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryMonocyclicPolicy initial closure policyResult)) :
    input.DeclarativeLocalizedMonocyclicDoubleBondPolicyResult
      initial.left initial.right policyResult := by
  cases route with
  | ordinaryMonocyclicPolicy _moleculeRoute policy => exact policy

/-- An independent required-monocyclic `E/Z` derivation forces the route policy to be
`requireEZ`.  The two independently derived policy equations are both
`MonocyclicDoubleBondPolicy` applications at the same ring size and bonded count. -/
theorem DeclarativeLocalizedRule3RequiredMonocyclicEZWith.policy_requireEZ
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {target occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {view : input.LocalizedDependencyView target}
    {Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel}
    {result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel}
    (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result) :
    result.policyResult.policy =
      BlueBookP93.Cyclic.DoubleBondDescriptorPolicy.requireEZ := by
  have policyDerived :=
    DeclarativeLocalizedRule3CyclicAuthorityRoute.policy_of_ordinaryMonocyclicPolicy
      input derived.1
  obtain ⟨_cyclicGeometry, _geometryRefines, assignment⟩ := derived.2.2.2.2
  exact Option.some.inj (policyDerived.2.2.symm.trans assignment.1)

/-- Unconditional permanent omission: a proved `permanentlyOmit` policy on a proved cyclic
authority route makes the actual cyclic policy path return `none`.  No endpoint compilation,
geometry or descriptor is consulted. -/
theorem localizedRule3RequiredMonocyclicEZWith?_eq_none_of_declarative_omitted
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    {policyResult : input.LocalizedMonocyclicDoubleBondPolicyResult}
    (route : input.DeclarativeLocalizedRule3CyclicAuthorityRoute occurrence
      (.ordinaryMonocyclicPolicy initial closure policyResult))
    (omitted : policyResult.policy =
      BlueBookP93.Cyclic.DoubleBondDescriptorPolicy.permanentlyOmit) :
    input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = none := by
  have routeComputed :=
    input.localizedRule3CyclicAuthorityRoute?_complete occurrence _ route
  exact input.localizedRule3RequiredMonocyclicEZWith?_eq_none_of_omitted
    target occurrence view rule3FrameOf initial closure policyResult
    routeComputed omitted

/-- Output-direction policy agreement: every descriptor the actual cyclic policy path emits has a
`requireEZ` route policy.  Consequently a `permanentlyOmit` route is never reported as
stereochemical output. -/
theorem localizedRule3RequiredMonocyclicEZWith?_requireEZ_of_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (computed : input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = some result) :
    result.policyResult.policy =
      BlueBookP93.Cyclic.DoubleBondDescriptorPolicy.requireEZ :=
  DeclarativeLocalizedRule3RequiredMonocyclicEZWith.policy_requireEZ input
    (input.localizedRule3RequiredMonocyclicEZWith?_sound
      target occurrence view rule3FrameOf Rule3FrameMeaning rule3FrameSound
      result computed)

/-! ## The lower endpoint component interface -/




def LocalizedRule3OccurrenceEndpointCompilationComplete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∀ frame,
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
        target view Rule3FrameMeaning endpoint partner endpointCursor frame →
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor = some frame

/-- Both oriented endpoint compilations needed by one cyclic double-bond occurrence. -/
structure LocalizedRule3CyclicEndpointCompletion
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop where
  /-- The left endpoint compilation returns the independently declared left key frame. -/
  leftComplete : ∀ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel),
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
        target view Rule3FrameMeaning initial.left initial.right initial.leftCursor frame →
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf initial.left initial.right initial.leftCursor = some frame
  /-- The right endpoint compilation returns the independently declared right key frame. -/
  rightComplete : ∀ (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
      (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel),
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
        target view Rule3FrameMeaning initial.right initial.left initial.rightCursor frame →
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf initial.right initial.left initial.rightCursor = some frame

/-- Canonical lower-component evidence sufficient for the endpoint completion interface: exact
Rule-3 callback completeness, canonical selection of the two reference cursors, and declarative
canonicity of the Rules-4a--5 keys.  These are exactly the lower primitives consumed by
`LocalizedEndpointSemanticCompletion`; note that the callback is required to return the declared
frame itself, since the cyclic compiler transports the compiled frame into its result. -/
structure LocalizedRule3CyclicEndpointCanonicalEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel) : Prop where
  /-- The supplied Rule-3 callback returns every independently meaningful frame. -/
  rule3FrameComplete : ∀ cursors frame,
    Rule3FrameMeaning cursors frame → rule3FrameOf cursors = some frame
  /-- At every occurrence endpoint, the two declared reference cursors are canonical. -/
  referenceCanonical : ∀ (endpoint partner : input.Atom)
      (endpointCursor : input.LocalizedRerootCursor carrierFuel)
      (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel),
    input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
        target view Rule3FrameMeaning endpoint partner endpointCursor frame →
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor
        frame.firstCursor frame.endpointFrame.first ∧
      input.CanonicalLocalizedRule3ReferenceCursor endpointCursor
        frame.secondCursor frame.endpointFrame.second
  /-- Every independently derived Rules-4a--5 key is canonical. -/
  rule45Canonical : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCompoundRule45Key),
    input.DeclarativeLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor key →
      input.CanonicalLocalizedRerootCompoundRule45Key target view
        (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor key

/-- Canonical lower-component evidence discharges the endpoint completion interface through the
two-sided canonical endpoint compilation criterion. -/
theorem LocalizedRule3CyclicEndpointCanonicalEvidence.toCompletion
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (evidence : input.LocalizedRule3CyclicEndpointCanonicalEvidence
      target view rule3FrameOf Rule3FrameMeaning) :
    input.LocalizedRule3CyclicEndpointCompletion
      target view rule3FrameOf Rule3FrameMeaning := by
  refine ⟨?_, ?_⟩
  · intro initial frame derived
    exact input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_complete_of_canonical
      target view rule3FrameOf Rule3FrameMeaning evidence.rule3FrameComplete
      initial.left initial.right initial.leftCursor frame
      ⟨derived.1,
        (evidence.referenceCanonical initial.left initial.right initial.leftCursor frame
          derived).1,
        (evidence.referenceCanonical initial.left initial.right initial.leftCursor frame
          derived).2,
        derived.2.2.2.1,
        derived.2.2.2.2.1,
        evidence.rule45Canonical _ _ derived.2.2.2.2.2.1,
        evidence.rule45Canonical _ _ derived.2.2.2.2.2.2⟩
  · intro initial frame derived
    exact input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_complete_of_canonical
      target view rule3FrameOf Rule3FrameMeaning evidence.rule3FrameComplete
      initial.right initial.left initial.rightCursor frame
      ⟨derived.1,
        (evidence.referenceCanonical initial.right initial.left initial.rightCursor frame
          derived).1,
        (evidence.referenceCanonical initial.right initial.left initial.rightCursor frame
          derived).2,
        derived.2.2.2.1,
        derived.2.2.2.2.1,
        evidence.rule45Canonical _ _ derived.2.2.2.2.2.1,
        evidence.rule45Canonical _ _ derived.2.2.2.2.2.2⟩

/-! ## Required `E/Z` completeness -/

/-- The independent required-monocyclic descriptor derivation is reproduced by the actual cyclic
policy path at the *same* result, once both lower endpoint compilations are reproduced.

The exact rational spatial unit and the final P-93 assignment are re-derived here from the
declarative spatial meaning; only the two endpoint compilations are premises.  In particular this
does not assume the desired cyclic output, its observation, or any canonical source. -/
theorem localizedRule3RequiredMonocyclicEZWith?_eq_some_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (completion : input.LocalizedRule3CyclicEndpointCompletion
      target view rule3FrameOf Rule3FrameMeaning)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result) :
    input.localizedRule3RequiredMonocyclicEZWith?
      target occurrence view rule3FrameOf = some result := by
  have routeComputed :=
    input.localizedRule3CyclicAuthorityRoute?_complete occurrence
      (.ordinaryMonocyclicPolicy result.initial result.closure result.policyResult)
      derived.1
  have required :=
    DeclarativeLocalizedRule3RequiredMonocyclicEZWith.policy_requireEZ input derived
  have leftComputed :=
    completion.leftComplete result.initial result.leftCompilation derived.2.1
  have rightComputed :=
    completion.rightComplete result.initial result.rightCompilation derived.2.2.1
  have leftValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view Rule3FrameMeaning result.initial.left result.initial.right
      result.initial.leftCursor result.leftCompilation derived.2.1
  have rightValid :=
    DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith.endpointFrame
      input target view Rule3FrameMeaning result.initial.right result.initial.left
      result.initial.rightCursor result.rightCompilation derived.2.2.1
  have unitComputed :
      input.localizedRule3DescriptorBearingSpatialUnit?
          result.initial.left result.initial.right
          result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame =
        some result.unit :=
    (input.localizedRule3DescriptorBearingSpatialUnit?_eq_some_iff
      result.initial.left result.initial.right
      result.leftCompilation.endpointFrame result.rightCompilation.endpointFrame
      _ _ leftValid rightValid result.unit).mpr derived.2.2.2.1
  obtain ⟨cyclicGeometry, geometryRefines, assignment⟩ := derived.2.2.2.2
  have geometryComputed :=
    (monocyclicSeniorLigandGeometryOfRule3?_eq_some_iff
      result.unit.geometry cyclicGeometry).mpr geometryRefines
  have descriptorComputed :=
    (BlueBookP93.Cyclic.requiredMonocyclicEZDescriptor?_eq_some_iff
      result.policyResult.carrier.ring.card result.policyResult.doubleBondCount
      cyclicGeometry result.descriptor).mpr assignment
  simp [localizedRule3RequiredMonocyclicEZWith?, routeComputed, required,
    leftComputed, rightComputed, unitComputed, geometryComputed, descriptorComputed]

/-- The node consumes an observation, not a rule payload.  Independent required-monocyclic `E/Z`
derivations therefore realize their *identical* Rule-3 observation on the actual cyclic policy
path, even when the concrete result record is only known through the lower endpoint component. -/
theorem localizedRule3RequiredMonocyclicEZWith?_observation_eq_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (completion : input.LocalizedRule3CyclicEndpointCompletion
      target view rule3FrameOf Rule3FrameMeaning)
    (result : input.LocalizedRule3RequiredMonocyclicEZResult carrierFuel)
    (derived : input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
      target occurrence view Rule3FrameMeaning result) :
    ∃ actual, input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf = some actual ∧
      input.localizedRule3RequiredMonocyclicEZObservation actual =
        input.localizedRule3RequiredMonocyclicEZObservation result :=
  ⟨result,
    input.localizedRule3RequiredMonocyclicEZWith?_eq_some_of_declarative
      target occurrence view rule3FrameOf Rule3FrameMeaning completion result derived,
    rfl⟩

/-- Exactly the `cyclicComplete` component obligation of the original-node converse, in the shape
used by `LocalizedDescriptorBearingRule3NodeWithCompletionObligations`, discharged from the
precise lower endpoint component interface. -/
theorem localizedRule3RequiredMonocyclicEZWith?_complete_of_endpointCompletion
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (completion : input.LocalizedRule3CyclicEndpointCompletion
      target view rule3FrameOf Rule3FrameMeaning) :
    ∀ result, input.DeclarativeLocalizedRule3RequiredMonocyclicEZWith
        target occurrence view Rule3FrameMeaning result →
      input.localizedRule3RequiredMonocyclicEZWith?
        target occurrence view rule3FrameOf = some result :=
  fun result derived =>
    input.localizedRule3RequiredMonocyclicEZWith?_eq_some_of_declarative
      target occurrence view rule3FrameOf Rule3FrameMeaning completion result derived

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
