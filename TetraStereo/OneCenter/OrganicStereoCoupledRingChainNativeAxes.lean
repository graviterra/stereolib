import TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress
import TetraStereo.OneCenter.OrganicStereoMonocyclicRingAssemblyIngress

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Native successor for the coupled ring/chain observation codec

The accepted legacy codec `OrganicStereoCoupledRingChainIngress` is lossless, but two of its
records are not fully native:

* `SuppliedRingChainRingAssemblyAxes` retains the *entire* `ChemistryNormalizationResult` (parsed
  `RawMolecule`, interaction graph, aromatic cycles, resonance, stereobonds and tautomer data) and
  a whole `SpatialConfiguration`;
* `SuppliedRingChainBaseNameCertificate` retains `frozenAtoms` as a source-ordered
  `List SemanticAtom`.

This module provides the concrete successor for actual source-valid coupled ring/chain
observations:

* the native axes record stores only the independent raw parsed syntax `parsed : RawMolecule`, the
  coordinates as a total native function `spatial : V → CartesianPoint3`, the relabelled assembly
  and the relabelled axis assignments.  The decoder recomputes
  `normalization := normalizeRawMolecule parsed` and rebuilds the original
  `SpatialConfiguration` exactly with `unrelabelSpatial`.  Neither the original normalization
  result nor the original physical graph is retained as an escape hatch.
* the native certificate stores the enumeration-aware lookup `frozenAtoms : V → SemanticAtom`.
  Ordered interaction participants keep using the existing native interaction codec.

The normalization fixed point
`normalization = normalizeRawMolecule normalization.parsed` is *derived* from the carrier's own
`ValidFor` predicate (the fourth conjunct of
`P93RingAssemblyAxesAuthorityObservation.ValidFor`), so the source-to-native-to-source direction
needs no extra assumption.  The native-to-source direction requires the stored raw syntax to be
already normalized (`RawMoleculeNormalized`); that condition is stated explicitly and is not
claimed to follow from validity.

The remaining fourteen of the fifteen reviewed descriptor-evidence constructors reuse the
existing legacy native records behind a proven no-axes guard, so a legacy axes record cannot be
hidden inside another payload.  The broad hybrid correspondence codec is reused unchanged; no new
chemical policy invariance is introduced and no bound is asserted for unused source references.
-/

namespace TetraStereo.OneCenter

namespace OrganicStereoCoupledRingChainNativeAxes

open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress
open TetraStereo.OneCenter.OrganicStereoCoupledRingChainIngress

variable {V : Type*} {n : ℕ}

/-! ## Generic enumeration-aware lookup codec -/

/-- Encode a source-ordered list as an enumeration-aware total lookup.  The length bound is the
only index information needed. -/
def encodeIndexedLookup {α : Type*} (e : V ≃ Fin n) (values : List α)
    (fits : values.length = n) : V → α :=
  fun atom => values.get (Fin.cast fits.symm (e atom))

/-- Decode a native lookup back into the source-ordered list. -/
def decodeIndexedLookup {α : Type*} (e : V ≃ Fin n) (lookup : V → α) : List α :=
  List.ofFn fun index : Fin n => lookup (e.symm index)

/-- Source-side exactness: the decoded lookup is the original ordered list. -/
theorem decodeIndexedLookup_encodeIndexedLookup {α : Type*} (e : V ≃ Fin n)
    (values : List α) (fits : values.length = n) :
    decodeIndexedLookup e (encodeIndexedLookup e values fits) = values := by
  simp only [decodeIndexedLookup, encodeIndexedLookup, Equiv.apply_symm_apply]
  trans List.ofFn (fun index : Fin values.length =>
      values.get (Fin.cast fits.symm (Fin.cast fits index)))
  · exact List.ofFn_congr (h := fits.symm)
      (f := fun index : Fin n => values.get (Fin.cast fits.symm index))
  · rw [show (fun index : Fin values.length =>
        values.get (Fin.cast fits.symm (Fin.cast fits index))) =
        (fun index : Fin values.length => values.get index) from by
      funext index
      exact congrArg values.get (Fin.ext rfl)]
    exact List.ofFn_get values

/-- Native-side exactness: every native lookup is its own decoded list, re-encoded. -/
theorem encodeIndexedLookup_decodeIndexedLookup {α : Type*} (e : V ≃ Fin n)
    (lookup : V → α) :
    encodeIndexedLookup e (decodeIndexedLookup e lookup)
      (List.length_ofFn (f := fun index : Fin n => lookup (e.symm index))) = lookup := by
  funext atom
  simp only [encodeIndexedLookup, decodeIndexedLookup, List.get_ofFn]
  rw [← Equiv.symm_apply_apply e atom]
  simp only [Equiv.apply_symm_apply]
  exact congrArg (fun index : Fin n => lookup (e.symm index)) (Fin.ext rfl)

/-- The monocyclic module's raw-syntax normalization predicate, re-exported for statements in
this module.  It is a definitional alias, not an additional claim. -/
abbrev RawMoleculeNormalized (mol : RawMolecule) : Prop :=
  OrganicStereoMonocyclicRingAssemblyIngress.RawMoleculeNormalized mol

/-! ## Native ring-assembly axes observation -/

/-- Native mirror of `P93RingAssemblyAxesAuthorityObservation` inside the coupled evidence codec.
The whole `ChemistryNormalizationResult` and the whole `SpatialConfiguration` are gone: only the
independent raw parsed syntax and the total native coordinate function are stored. -/
structure SuppliedNativeRingChainRingAssemblyAxes (V : Type*)
    (policy : P93RingAssemblyAuthorityPolicy) where
  assembly : SuppliedRingChainRingAssembly V
  parsed : RawMolecule
  spatial : V → CartesianPoint3
  assignments : List (SuppliedRingChainRingAssemblyAxisAssignment V)

/-- The bounds needed to encode an axes observation natively.  The coordinate length is an
explicit bound derived below from the source spatial equality and `SpatialIndicesWellFormed`. -/
structure NativeAxesSourceBoundedIn (n : Nat) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy) : Prop where
  axes : RingAssemblyAxesBoundedIn n policy observation
  spatialLength : observation.spatial.positions.length = n

/-- Encode one bounded axes observation.  The raw parsed syntax and every non-atom field are
copied; the assembly, coordinate list and axis assignments are relabelled. -/
def relabelNativeAxes [DecidableEq V] (e : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (bounded : NativeAxesSourceBoundedIn n policy observation) :
    SuppliedNativeRingChainRingAssemblyAxes V policy where
  assembly := relabelRingAssembly e observation.assembly bounded.axes.assembly
  parsed := observation.normalization.parsed
  spatial := OrganicStereoMonocyclicRingAssemblyIngress.relabelSpatial e observation.spatial
    bounded.spatialLength
  assignments :=
    observation.assignments.attach.map fun assignment =>
      relabelRingAssemblyAxisAssignment e assignment.1
        (bounded.axes.assignments assignment.1 assignment.2)

/-- Decode one axes observation, recomputing the normalization result from its parsed syntax and
rebuilding the original `SpatialConfiguration` exactly. -/
def unrelabelNativeAxes [DecidableEq V] (e : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedNativeRingChainRingAssemblyAxes V policy) :
    P93RingAssemblyAxesAuthorityObservation policy where
  assembly := unrelabelRingAssembly e observation.assembly
  normalization := normalizeRawMolecule observation.parsed
  spatial := OrganicStereoMonocyclicRingAssemblyIngress.unrelabelSpatial e observation.spatial
  assignments :=
    observation.assignments.map (unrelabelRingAssemblyAxisAssignment e)

/-- Bounds of a decoded axes observation. -/
def unrelabelNativeAxesBounded [DecidableEq V] (e : V ≃ Fin n)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedNativeRingChainRingAssemblyAxes V policy) :
    NativeAxesSourceBoundedIn n policy (unrelabelNativeAxes e policy observation) where
  axes :=
    { assembly := unrelabelRingAssemblyBounded e observation.assembly
      assignments := fun assignment member => by
        rw [unrelabelNativeAxes, List.mem_map] at member
        rcases member with ⟨presented, _presentedMember, rfl⟩
        exact unrelabelRingAssemblyAxisAssignmentBounded e presented }
  spatialLength := by
    simp [unrelabelNativeAxes,
      OrganicStereoMonocyclicRingAssemblyIngress.unrelabelSpatial]

/-- The exact normalization fixed point used by the source-side inverse.  For source-valid
observations this is *derived* (see `nativeAxesNormalizationFixed_of_validFor`). -/
def NativeAxesNormalizationFixed {policy : P93RingAssemblyAuthorityPolicy}
    (observation : P93RingAssemblyAxesAuthorityObservation policy) : Prop :=
  observation.normalization = normalizeRawMolecule observation.normalization.parsed

/-- The normalization fixed point is exactly the fourth conjunct of the axes observation's own
`ValidFor`; no additional assumption is made. -/
theorem nativeAxesNormalizationFixed_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    NativeAxesNormalizationFixed observation :=
  valid.2.2.2.1

/-- **Exact source-side recovery of one axes observation.**  The decoder rebuilds the original
normalization result from `parsed` and the original `SpatialConfiguration` from the native
coordinate function.  The normalization equality is the carrier's own `ValidFor` conjunct. -/
theorem unrelabelNativeAxes_relabelNativeAxes [DecidableEq V]
    (e : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (bounded : NativeAxesSourceBoundedIn n policy observation)
    (normalizationFixed : NativeAxesNormalizationFixed observation) :
    unrelabelNativeAxes e policy (relabelNativeAxes e policy observation bounded) =
      observation := by
  obtain ⟨assembly, normalization, spatial, assignments⟩ := observation
  have normalizationEq : normalizeRawMolecule normalization.parsed = normalization :=
    normalizationFixed.symm
  simp only [relabelNativeAxes, unrelabelNativeAxes]
  rw [P93RingAssemblyAxesAuthorityObservation.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact unrelabelRingAssembly_relabelRingAssembly e assembly bounded.axes.assembly
  · exact normalizationEq
  · exact OrganicStereoMonocyclicRingAssemblyIngress.unrelabelSpatial_relabelSpatial
      e spatial bounded.spatialLength
  · rw [List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact unrelabelRingAssemblyAxisAssignment_relabelRingAssemblyAxisAssignment e
        assignment.1 (bounded.axes.assignments assignment.1 assignment.2)
    · exact List.attach_map_subtype_val assignments

/-- Native-side exactness of one axes observation.  The only extra condition is that the stored
raw syntax is already in its unspecified-bond-normalized form; without it the decoder's
recomputed normalization would be normalized a second time. -/
theorem relabelNativeAxes_unrelabelNativeAxes [DecidableEq V]
    (e : V ≃ Fin n) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : SuppliedNativeRingChainRingAssemblyAxes V policy)
    (rawSyntaxNormalized : RawMoleculeNormalized observation.parsed) :
    relabelNativeAxes e policy (unrelabelNativeAxes e policy observation)
        (unrelabelNativeAxesBounded e policy observation) = observation := by
  obtain ⟨assembly, parsed, spatial, assignments⟩ := observation
  have idempotent : parsed.normalizeUnspecifiedBonds = parsed := by
    simpa [RawMoleculeNormalized,
      OrganicStereoMonocyclicRingAssemblyIngress.RawMoleculeNormalized] using rawSyntaxNormalized
  simp only [relabelNativeAxes, unrelabelNativeAxes, unrelabelNativeAxesBounded]
  rw [SuppliedNativeRingChainRingAssemblyAxes.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact relabelRingAssembly_unrelabelRingAssembly e assembly
  · exact (OrganicStereoMonocyclicRingAssemblyIngress.normalizeRawMolecule_parsed parsed).trans
      idempotent
  · exact OrganicStereoMonocyclicRingAssemblyIngress.relabelSpatial_unrelabelSpatial e spatial
  · rw [List.attach_map, List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact relabelRingAssemblyAxisAssignment_unrelabelRingAssemblyAxisAssignment e
        assignment.1
    · exact List.attach_map_subtype_val assignments

/-! ## Bounds derived from the actual source-family predicates -/

/-- The axes bounds are derived from the axes observation's own `ValidFor`: the assembly and
assignment bounds from `ringAssemblyAxesBoundedIn_of_validFor`, and the coordinate length from the
source spatial equality together with `SpatialIndicesWellFormed`. -/
theorem nativeAxesSourceBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (valid : observation.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    NativeAxesSourceBoundedIn source.molecule.atomCount policy observation where
  axes := ringAssemblyAxesBoundedIn_of_validFor source policy observation valid
  spatialLength := by
    have h := spatialWellFormed
    unfold AuthoritativeChemicalInput.SpatialIndicesWellFormed at h
    rw [valid.2.1] at h
    exact h

/-- The same bounds through an actual `PhysicalFrameSourceBinding`: the coordinate length is
derived from the binding's spatial well-formedness and its proven atom-count equality. -/
theorem nativeAxesSourceBoundedIn_of_validFor_binding [DecidableEq V] [Fintype V]
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (policy : P93RingAssemblyAuthorityPolicy)
    (observation : P93RingAssemblyAxesAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    NativeAxesSourceBoundedIn (Fintype.card V) policy observation := by
  have bounded := nativeAxesSourceBoundedIn_of_validFor binding.source policy observation valid
    binding.spatial_wellFormed
  rwa [binding.atomCount_eq] at bounded

/-! ## Native reviewed base-name certificate -/

/-- Native mirror of `P93RingChainReviewedBaseNameCertificate`.  The frozen name is copied, the
frozen atom records become an enumeration-aware lookup, and the frozen interaction records keep
using the existing native interaction codec. -/
structure SuppliedNativeRingChainBaseNameCertificate (V : Type*) where
  frozenName : P93RingChainBaseName
  frozenAtoms : V → SemanticAtom
  frozenInteractions : List (SuppliedRingChainSemanticInteraction V)

/-- Bounds needed to encode a certificate: the frozen atom count and the interaction participant
bounds. -/
structure NativeCertificateBoundedIn (n : Nat)
    (certificate : P93RingChainReviewedBaseNameCertificate) : Prop where
  atoms : certificate.frozenAtoms.length = n
  interactions : RingChainCertificateBoundedIn n certificate

def relabelNativeCertificate [DecidableEq V] (e : V ≃ Fin n)
    (certificate : P93RingChainReviewedBaseNameCertificate)
    (bounded : NativeCertificateBoundedIn n certificate) :
    SuppliedNativeRingChainBaseNameCertificate V where
  frozenName := certificate.frozenName
  frozenAtoms := encodeIndexedLookup e certificate.frozenAtoms bounded.atoms
  frozenInteractions :=
    relabelSemanticInteractionList e certificate.frozenInteractions bounded.interactions

def unrelabelNativeCertificate (e : V ≃ Fin n)
    (certificate : SuppliedNativeRingChainBaseNameCertificate V) :
    P93RingChainReviewedBaseNameCertificate where
  frozenName := certificate.frozenName
  frozenAtoms := decodeIndexedLookup e certificate.frozenAtoms
  frozenInteractions :=
    unrelabelSemanticInteractionList e certificate.frozenInteractions

def unrelabelNativeCertificateBounded (e : V ≃ Fin n)
    (certificate : SuppliedNativeRingChainBaseNameCertificate V) :
    NativeCertificateBoundedIn n (unrelabelNativeCertificate e certificate) where
  atoms := List.length_ofFn
  interactions :=
    unrelabelSemanticInteractionListBounded e certificate.frozenInteractions

theorem unrelabelNativeCertificate_relabelNativeCertificate [DecidableEq V]
    (e : V ≃ Fin n) (certificate : P93RingChainReviewedBaseNameCertificate)
    (bounded : NativeCertificateBoundedIn n certificate) :
    unrelabelNativeCertificate e
        (relabelNativeCertificate e certificate bounded) = certificate := by
  obtain ⟨frozenName, frozenAtoms, frozenInteractions⟩ := certificate
  simp [relabelNativeCertificate, unrelabelNativeCertificate,
    decodeIndexedLookup_encodeIndexedLookup,
    unrelabelSemanticInteractionList_relabelSemanticInteractionList]

theorem relabelNativeCertificate_unrelabelNativeCertificate [DecidableEq V]
    (e : V ≃ Fin n) (certificate : SuppliedNativeRingChainBaseNameCertificate V) :
    relabelNativeCertificate e (unrelabelNativeCertificate e certificate)
        (unrelabelNativeCertificateBounded e certificate) = certificate := by
  obtain ⟨frozenName, frozenAtoms, frozenInteractions⟩ := certificate
  simp [relabelNativeCertificate, unrelabelNativeCertificate,
    unrelabelNativeCertificateBounded,
    encodeIndexedLookup_decodeIndexedLookup,
    relabelSemanticInteractionList_unrelabelSemanticInteractionList]

/-- The certificate bounds are derived from the certificate's own `ValidFor`: the atom count from
the frozen-atom equality and the interaction bounds from structural well-formedness. -/
theorem nativeCertificateBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput) (name : P93RingChainBaseName)
    (certificate : P93RingChainReviewedBaseNameCertificate)
    (valid : certificate.ValidFor source name) :
    NativeCertificateBoundedIn source.molecule.atomCount certificate where
  atoms := by
    rw [valid.2.2.2.1]
    rfl
  interactions := certificateBoundedIn_of_validFor source name certificate valid

theorem nativeCertificateBoundedIn_of_validFor_binding [DecidableEq V] [Fintype V]
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (name : P93RingChainBaseName)
    (certificate : P93RingChainReviewedBaseNameCertificate)
    (valid : certificate.ValidFor binding.source name) :
    NativeCertificateBoundedIn (Fintype.card V) certificate := by
  have bounded := nativeCertificateBoundedIn_of_validFor binding.source name certificate valid
  rwa [binding.atomCount_eq] at bounded

/-! ## Native reviewed descriptor evidence -/

/-- Whether a *legacy native* evidence record is the axes constructor.  The successor evidence
uses this guard to keep the legacy axes record out of the reusable non-axes payload. -/
def SuppliedEvidenceIsAxes {V : Type*} {policies : P93CoupledRingChainDescriptorPolicies} :
    SuppliedRingChainReviewedDescriptorEvidence V policies → Prop
  | .ringAssemblyAxis _ _ => True
  | _ => False

/-- Native successor of the fifteen reviewed descriptor-evidence constructors.  The axes case is
the fully native one; the other fourteen constructors reuse the legacy native records behind a
proven no-axes guard, so the legacy axes record can never be hidden inside another payload. -/
inductive SuppliedNativeRingChainReviewedDescriptorEvidence (V : Type*)
    (policies : P93CoupledRingChainDescriptorPolicies) where
  | ringAssemblyAxis
      (observation : SuppliedNativeRingChainRingAssemblyAxes V policies.ringAssembly)
      (assignment : SuppliedRingChainRingAssemblyAxisAssignment V)
  | other
      (evidence : { evidence : SuppliedRingChainReviewedDescriptorEvidence V policies //
        ¬ SuppliedEvidenceIsAxes evidence })

/-- Bounds needed to encode each evidence case.  Only the axes case changes: it additionally
requires the native source bounds (including the coordinate length). -/
def NativeEvidenceBoundedIn (n : Nat) (policies : P93CoupledRingChainDescriptorPolicies) :
    P93RingChainReviewedDescriptorEvidence policies → Prop
  | .ringAssemblyAxis observation assignment =>
      NativeAxesSourceBoundedIn n policies.ringAssembly observation ∧
        RingAssemblyAxisAssignmentBoundedIn n assignment
  | evidence => EvidenceBoundedIn n policies evidence

/-- Encode one further source evidence case.  The axes constructor becomes the native successor;
every other constructor reuses the accepted legacy native codec inside the guarded `other`
case. -/
def relabelNativeEvidence [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies} :
    (evidence : P93RingChainReviewedDescriptorEvidence policies) →
      NativeEvidenceBoundedIn n policies evidence →
      SuppliedNativeRingChainReviewedDescriptorEvidence V policies
  | .ringAssemblyAxis observation assignment, bounded =>
      .ringAssemblyAxis (relabelNativeAxes e policies.ringAssembly observation bounded.1)
        (relabelRingAssemblyAxisAssignment e assignment bounded.2)
  | .acyclicCenter observation, bounded =>
      .other ⟨.acyclicCenter (relabelRingChainAcyclicCenter e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .acyclicDoubleBond observation, bounded =>
      .other ⟨.acyclicDoubleBond (relabelRingChainAcyclicDoubleBond e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .acyclicEvenCumulene observation, bounded =>
      .other ⟨.acyclicEvenCumulene (relabelRingChainAcyclicEvenCumulene e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .acyclicOddCumulene observation, bounded =>
      .other ⟨.acyclicOddCumulene (relabelRingChainAcyclicOddCumulene e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .monocyclicCenter observation, bounded =>
      .other ⟨.monocyclicCenter (relabelRingChainMonocyclicCenter e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .monocyclicDoubleBond observation citation descriptor, bounded =>
      .other ⟨.monocyclicDoubleBond
          (relabelRingChainMonocyclicDoubleBond e observation bounded) citation descriptor,
        by simp [SuppliedEvidenceIsAxes]⟩
  | .fusedCIP observation, bounded =>
      .other ⟨.fusedCIP (relabelRingChainFusedCIP e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .cyclophanePlane observation, bounded =>
      .other ⟨.cyclophanePlane (relabelRingChainCyclophanePlane e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .cyclophaneCenterCIP observation context kind descriptor, bounded =>
      .other ⟨.cyclophaneCenterCIP (relabelRingChainCyclophaneCenter e observation bounded)
          context kind descriptor, by simp [SuppliedEvidenceIsAxes]⟩
  | .cyclophaneCenterRelative observation assignment, bounded =>
      .other ⟨.cyclophaneCenterRelative
          (relabelRingChainCyclophaneCenter e observation bounded.1)
          (relabelCyclophaneAssignment e assignment bounded.2),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .cyclophaneDoubleBond observation descriptor, bounded =>
      .other ⟨.cyclophaneDoubleBond
          (relabelRingChainCyclophaneDoubleBond e observation bounded) descriptor,
        by simp [SuppliedEvidenceIsAxes]⟩
  | .spiroPolyhedral observation, bounded =>
      .other ⟨.spiroPolyhedral (relabelRingChainSpiroPolyhedral e observation bounded),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .ringAssemblyCenter observation assignment, bounded =>
      .other ⟨.ringAssemblyCenter
          (relabelRingChainRingAssemblyCenters e observation bounded.1)
          (relabelRingAssemblyCenterAssignment e assignment bounded.2),
        by simp [SuppliedEvidenceIsAxes]⟩
  | .ringAssemblyDoubleBond observation assignment, bounded =>
      .other ⟨.ringAssemblyDoubleBond
          (relabelRingChainRingAssemblyDoubleBonds e observation bounded.1)
          (relabelRingAssemblyDoubleBondAssignment e assignment bounded.2),
        by simp [SuppliedEvidenceIsAxes]⟩

/-- Decode one native evidence case.  The guarded `other` case is decoded by the accepted legacy
codec; the native axes case recomputes its normalization and spatial configuration. -/
def unrelabelNativeEvidence [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies} :
    SuppliedNativeRingChainReviewedDescriptorEvidence V policies →
      P93RingChainReviewedDescriptorEvidence policies
  | .ringAssemblyAxis observation assignment =>
      .ringAssemblyAxis (unrelabelNativeAxes e policies.ringAssembly observation)
        (unrelabelRingAssemblyAxisAssignment e assignment)
  | .other evidence => unrelabelRingChainEvidence e evidence.1

/-- Bounds of a decoded native evidence case. -/
def unrelabelNativeEvidenceBounded [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (evidence : SuppliedNativeRingChainReviewedDescriptorEvidence V policies) :
    NativeEvidenceBoundedIn n policies (unrelabelNativeEvidence e evidence) := by
  cases evidence with
  | ringAssemblyAxis observation assignment =>
      exact ⟨unrelabelNativeAxesBounded e policies.ringAssembly observation,
        unrelabelRingAssemblyAxisAssignmentBounded e assignment⟩
  | other evidence =>
      obtain ⟨value, guard⟩ := evidence
      cases value with
      | ringAssemblyAxis observation assignment => exact absurd trivial guard
      | acyclicCenter observation =>
          exact unrelabelRingChainEvidenceBounded e (.acyclicCenter observation)
      | acyclicDoubleBond observation =>
          exact unrelabelRingChainEvidenceBounded e (.acyclicDoubleBond observation)
      | acyclicEvenCumulene observation =>
          exact unrelabelRingChainEvidenceBounded e (.acyclicEvenCumulene observation)
      | acyclicOddCumulene observation =>
          exact unrelabelRingChainEvidenceBounded e (.acyclicOddCumulene observation)
      | monocyclicCenter observation =>
          exact unrelabelRingChainEvidenceBounded e (.monocyclicCenter observation)
      | monocyclicDoubleBond observation citation descriptor =>
          exact unrelabelRingChainEvidenceBounded e
            (.monocyclicDoubleBond observation citation descriptor)
      | fusedCIP observation =>
          exact unrelabelRingChainEvidenceBounded e (.fusedCIP observation)
      | cyclophanePlane observation =>
          exact unrelabelRingChainEvidenceBounded e (.cyclophanePlane observation)
      | cyclophaneCenterCIP observation context kind descriptor =>
          exact unrelabelRingChainEvidenceBounded e
            (.cyclophaneCenterCIP observation context kind descriptor)
      | cyclophaneCenterRelative observation assignment =>
          exact unrelabelRingChainEvidenceBounded e
            (.cyclophaneCenterRelative observation assignment)
      | cyclophaneDoubleBond observation descriptor =>
          exact unrelabelRingChainEvidenceBounded e
            (.cyclophaneDoubleBond observation descriptor)
      | spiroPolyhedral observation =>
          exact unrelabelRingChainEvidenceBounded e (.spiroPolyhedral observation)
      | ringAssemblyCenter observation assignment =>
          exact unrelabelRingChainEvidenceBounded e
            (.ringAssemblyCenter observation assignment)
      | ringAssemblyDoubleBond observation assignment =>
          exact unrelabelRingChainEvidenceBounded e
            (.ringAssemblyDoubleBond observation assignment)

/-- The normalization fixed point required by the source-side evidence inverse.  It is `True`
for every non-axes constructor, which carries no normalization result at all. -/
def EvidenceNormalizationFixed {policies : P93CoupledRingChainDescriptorPolicies} :
    P93RingChainReviewedDescriptorEvidence policies → Prop
  | .ringAssemblyAxis observation _ => NativeAxesNormalizationFixed observation
  | _ => True

/-- The evidence-level normalization fixed point follows from the evidence's own `ValidFor`;
this is not an extra assumption. -/
theorem EvidenceNormalizationFixed.of_validFor
    (source : AuthoritativeChemicalInput)
    (policies : P93CoupledRingChainDescriptorPolicies)
    (evidence : P93RingChainReviewedDescriptorEvidence policies)
    (valid : evidence.ValidFor source) :
    EvidenceNormalizationFixed evidence := by
  cases evidence with
  | ringAssemblyAxis observation assignment =>
      simpa only [EvidenceNormalizationFixed] using
        nativeAxesNormalizationFixed_of_validFor source policies.ringAssembly observation valid.1
  | acyclicCenter observation => simp [EvidenceNormalizationFixed]
  | acyclicDoubleBond observation => simp [EvidenceNormalizationFixed]
  | acyclicEvenCumulene observation => simp [EvidenceNormalizationFixed]
  | acyclicOddCumulene observation => simp [EvidenceNormalizationFixed]
  | monocyclicCenter observation => simp [EvidenceNormalizationFixed]
  | monocyclicDoubleBond observation citation descriptor =>
      simp [EvidenceNormalizationFixed]
  | fusedCIP observation => simp [EvidenceNormalizationFixed]
  | cyclophanePlane observation => simp [EvidenceNormalizationFixed]
  | cyclophaneCenterCIP observation context kind descriptor =>
      simp [EvidenceNormalizationFixed]
  | cyclophaneCenterRelative observation assignment => simp [EvidenceNormalizationFixed]
  | cyclophaneDoubleBond observation descriptor => simp [EvidenceNormalizationFixed]
  | spiroPolyhedral observation => simp [EvidenceNormalizationFixed]
  | ringAssemblyCenter observation assignment => simp [EvidenceNormalizationFixed]
  | ringAssemblyDoubleBond observation assignment => simp [EvidenceNormalizationFixed]

/-- Source-side exactness of the evidence codec.  The axes case uses the carrier's derived
normalization fixed point; the other cases are exactly the accepted legacy inverse. -/
theorem unrelabelNativeEvidence_relabelNativeEvidence [DecidableEq V]
    (e : V ≃ Fin n) {policies : P93CoupledRingChainDescriptorPolicies}
    (evidence : P93RingChainReviewedDescriptorEvidence policies)
    (bounded : NativeEvidenceBoundedIn n policies evidence)
    (normalizationFixed : EvidenceNormalizationFixed evidence) :
    unrelabelNativeEvidence e (relabelNativeEvidence e evidence bounded) = evidence := by
  cases evidence with
  | ringAssemblyAxis observation assignment =>
      have normalizationFixedAxes : NativeAxesNormalizationFixed observation :=
        normalizationFixed
      simp only [relabelNativeEvidence, unrelabelNativeEvidence]
      rw [unrelabelNativeAxes_relabelNativeAxes e policies.ringAssembly observation
        bounded.1 normalizationFixedAxes]
      rw [unrelabelRingAssemblyAxisAssignment_relabelRingAssemblyAxisAssignment e assignment
        bounded.2]
  | acyclicCenter observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicCenter_relabelRingChainAcyclicCenter]
  | acyclicDoubleBond observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicDoubleBond_relabelRingChainAcyclicDoubleBond]
  | acyclicEvenCumulene observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicEvenCumulene_relabelRingChainAcyclicEvenCumulene]
  | acyclicOddCumulene observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainAcyclicOddCumulene_relabelRingChainAcyclicOddCumulene]
  | monocyclicCenter observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainMonocyclicCenter_relabelRingChainMonocyclicCenter]
  | monocyclicDoubleBond observation citation descriptor =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainMonocyclicDoubleBond_relabelRingChainMonocyclicDoubleBond]
  | fusedCIP observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainFusedCIP_relabelRingChainFusedCIP]
  | cyclophanePlane observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophanePlane_relabelRingChainCyclophanePlane]
  | cyclophaneCenterCIP observation context kind descriptor =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophaneCenter_relabelRingChainCyclophaneCenter]
  | cyclophaneCenterRelative observation assignment =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophaneCenter_relabelRingChainCyclophaneCenter,
        unrelabelCyclophaneAssignment_relabelCyclophaneAssignment]
  | cyclophaneDoubleBond observation descriptor =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainCyclophaneDoubleBond_relabelRingChainCyclophaneDoubleBond]
  | spiroPolyhedral observation =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainSpiroPolyhedral_relabelRingChainSpiroPolyhedral]
  | ringAssemblyCenter observation assignment =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainRingAssemblyCenters_relabelRingChainRingAssemblyCenters,
        unrelabelRingAssemblyCenterAssignment_relabelRingAssemblyCenterAssignment]
  | ringAssemblyDoubleBond observation assignment =>
      simp [relabelNativeEvidence, unrelabelNativeEvidence, unrelabelRingChainEvidence,
        unrelabelRingChainRingAssemblyDoubleBonds_relabelRingChainRingAssemblyDoubleBonds,
        unrelabelRingAssemblyDoubleBondAssignment_relabelRingAssemblyDoubleBondAssignment]

/-- The raw-syntax fixed point required by the native-side evidence inverse.  It is `True` for
every non-axes constructor, which stores no parsed normalization syntax. -/
def NativeEvidenceRawSyntaxNormalized {V : Type*}
    {policies : P93CoupledRingChainDescriptorPolicies} :
    SuppliedNativeRingChainReviewedDescriptorEvidence V policies → Prop
  | .ringAssemblyAxis observation _ => RawMoleculeNormalized observation.parsed
  | _ => True

/-- Native-side exactness of the evidence codec.  The axes case requires the stored raw syntax to
be already normalized; the `other` cases are exactly the accepted legacy inverse. -/
theorem relabelNativeEvidence_unrelabelNativeEvidence [DecidableEq V]
    (e : V ≃ Fin n) {policies : P93CoupledRingChainDescriptorPolicies}
    (evidence : SuppliedNativeRingChainReviewedDescriptorEvidence V policies)
    (rawSyntaxNormalized : NativeEvidenceRawSyntaxNormalized evidence) :
    relabelNativeEvidence e (unrelabelNativeEvidence e evidence)
        (unrelabelNativeEvidenceBounded e evidence) = evidence := by
  cases evidence with
  | ringAssemblyAxis observation assignment =>
      have rawSyntaxNormalizedAxes : RawMoleculeNormalized observation.parsed :=
        rawSyntaxNormalized
      simp only [unrelabelNativeEvidence, relabelNativeEvidence]
      rw [relabelNativeAxes_unrelabelNativeAxes e policies.ringAssembly observation
        rawSyntaxNormalizedAxes]
      rw [relabelRingAssemblyAxisAssignment_unrelabelRingAssemblyAxisAssignment e assignment]
  | other evidence =>
      obtain ⟨value, guard⟩ := evidence
      cases value with
      | ringAssemblyAxis observation assignment => exact absurd trivial guard
      | acyclicCenter observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainAcyclicCenter_unrelabelRingChainAcyclicCenter]
      | acyclicDoubleBond observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainAcyclicDoubleBond_unrelabelRingChainAcyclicDoubleBond]
      | acyclicEvenCumulene observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainAcyclicEvenCumulene_unrelabelRingChainAcyclicEvenCumulene]
      | acyclicOddCumulene observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainAcyclicOddCumulene_unrelabelRingChainAcyclicOddCumulene]
      | monocyclicCenter observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainMonocyclicCenter_unrelabelRingChainMonocyclicCenter]
      | monocyclicDoubleBond observation citation descriptor =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainMonocyclicDoubleBond_unrelabelRingChainMonocyclicDoubleBond]
      | fusedCIP observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainFusedCIP_unrelabelRingChainFusedCIP]
      | cyclophanePlane observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainCyclophanePlane_unrelabelRingChainCyclophanePlane]
      | cyclophaneCenterCIP observation context kind descriptor =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainCyclophaneCenter_unrelabelRingChainCyclophaneCenter]
      | cyclophaneCenterRelative observation assignment =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainCyclophaneCenter_unrelabelRingChainCyclophaneCenter,
            relabelCyclophaneAssignment_unrelabelCyclophaneAssignment]
      | cyclophaneDoubleBond observation descriptor =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainCyclophaneDoubleBond_unrelabelRingChainCyclophaneDoubleBond]
      | spiroPolyhedral observation =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainSpiroPolyhedral_unrelabelRingChainSpiroPolyhedral]
      | ringAssemblyCenter observation assignment =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainRingAssemblyCenters_unrelabelRingChainRingAssemblyCenters,
            relabelRingAssemblyCenterAssignment_unrelabelRingAssemblyCenterAssignment]
      | ringAssemblyDoubleBond observation assignment =>
          simp [unrelabelNativeEvidence, relabelNativeEvidence, unrelabelRingChainEvidence,
            unrelabelRingChainEvidenceBounded,
            relabelRingChainRingAssemblyDoubleBonds_unrelabelRingChainRingAssemblyDoubleBonds,
            relabelRingAssemblyDoubleBondAssignment_unrelabelRingAssemblyDoubleBondAssignment]

/-- Every evidence case is bounded by the source atom count, derived from the evidence's own
`ValidFor`.  The axes case additionally gets the native source bounds, including the coordinate
length derived from the source spatial equality. -/
theorem NativeEvidenceBoundedIn.of_validFor
    (source : AuthoritativeChemicalInput)
    (policies : P93CoupledRingChainDescriptorPolicies)
    (evidence : P93RingChainReviewedDescriptorEvidence policies)
    (valid : evidence.ValidFor source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    NativeEvidenceBoundedIn source.molecule.atomCount policies evidence := by
  cases evidence with
  | ringAssemblyAxis observation assignment =>
      exact ⟨nativeAxesSourceBoundedIn_of_validFor source policies.ringAssembly observation
          valid.1 spatialWellFormed,
        ringAssemblyAxisAssignmentBoundedIn_of_validFor source policies.ringAssembly observation
          assignment valid.2 valid.1⟩
  | acyclicCenter observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | acyclicDoubleBond observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | acyclicEvenCumulene observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | acyclicOddCumulene observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | monocyclicCenter observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | monocyclicDoubleBond observation citation descriptor =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | fusedCIP observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | cyclophanePlane observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | cyclophaneCenterCIP observation context kind descriptor =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | cyclophaneCenterRelative observation assignment =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | cyclophaneDoubleBond observation descriptor =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | spiroPolyhedral observation =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | ringAssemblyCenter observation assignment =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)
  | ringAssemblyDoubleBond observation assignment =>
      simpa only [NativeEvidenceBoundedIn] using
        (EvidenceBoundedIn.of_validFor source policies _ valid spatialWellFormed)

/-! ## Native descriptor assignments -/

structure SuppliedNativeRingChainDescriptorAssignment (V : Type*)
    (policies : P93CoupledRingChainDescriptorPolicies) where
  evidence : SuppliedNativeRingChainReviewedDescriptorEvidence V policies

def relabelNativeDescriptorAssignment [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : P93RingChainDescriptorAssignment policies)
    (bounded : NativeEvidenceBoundedIn n policies assignment.evidence) :
    SuppliedNativeRingChainDescriptorAssignment V policies where
  evidence := relabelNativeEvidence e assignment.evidence bounded

def unrelabelNativeDescriptorAssignment [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : SuppliedNativeRingChainDescriptorAssignment V policies) :
    P93RingChainDescriptorAssignment policies where
  evidence := unrelabelNativeEvidence e assignment.evidence

def unrelabelNativeDescriptorAssignmentBounded [DecidableEq V] (e : V ≃ Fin n)
    {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : SuppliedNativeRingChainDescriptorAssignment V policies) :
    NativeEvidenceBoundedIn n policies
      (unrelabelNativeDescriptorAssignment e assignment).evidence :=
  unrelabelNativeEvidenceBounded e assignment.evidence

theorem unrelabelNativeDescriptorAssignment_relabelNativeDescriptorAssignment [DecidableEq V]
    (e : V ≃ Fin n) {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : P93RingChainDescriptorAssignment policies)
    (bounded : NativeEvidenceBoundedIn n policies assignment.evidence)
    (normalizationFixed : EvidenceNormalizationFixed assignment.evidence) :
    unrelabelNativeDescriptorAssignment e
        (relabelNativeDescriptorAssignment e assignment bounded) = assignment := by
  obtain ⟨evidence⟩ := assignment
  simp only [relabelNativeDescriptorAssignment, unrelabelNativeDescriptorAssignment]
  rw [unrelabelNativeEvidence_relabelNativeEvidence e evidence bounded normalizationFixed]

theorem relabelNativeDescriptorAssignment_unrelabelNativeDescriptorAssignment [DecidableEq V]
    (e : V ≃ Fin n) {policies : P93CoupledRingChainDescriptorPolicies}
    (assignment : SuppliedNativeRingChainDescriptorAssignment V policies)
    (rawSyntaxNormalized : NativeEvidenceRawSyntaxNormalized assignment.evidence) :
    relabelNativeDescriptorAssignment e
        (unrelabelNativeDescriptorAssignment e assignment)
        (unrelabelNativeDescriptorAssignmentBounded e assignment) = assignment := by
  obtain ⟨evidence⟩ := assignment
  simp only [relabelNativeDescriptorAssignment, unrelabelNativeDescriptorAssignment,
    unrelabelNativeDescriptorAssignmentBounded]
  rw [relabelNativeEvidence_unrelabelNativeEvidence e evidence rawSyntaxNormalized]

/-! ## The complete native coupled ring/chain observation -/

/-- Native successor of `SuppliedCoupledRingChainObservation`.  The certificate and the evidence
assignments are the native ones; every other role-bearing field (reviewed name, annotated name,
multiplicative bit, ordered repeated components, ordered correspondence pairs and ownership
indices) is preserved exactly. -/
structure SuppliedNativeCoupledRingChainObservation (V : Type*)
    (policy : P93CoupledRingChainAuthorityPolicy) where
  reviewedBaseName : P93RingChainBaseName
  baseNameCertificate : SuppliedNativeRingChainBaseNameCertificate V
  annotatedBaseName : P93RingChainBaseName
  assignments : List (SuppliedNativeRingChainDescriptorAssignment V policy.descriptorPolicies)
  multiplicativeSelected : Bool
  repeatedComponents : List (SuppliedRingChainRepeatedComponent V)
  componentCorrespondences : List (SuppliedRingChainComponentCorrespondence V)
  assignmentOwnerships : List (P93RingChainAssignmentOwnership)

/-- Bounds needed to encode a complete observation.  Correspondences still require no bound: the
broad hybrid codec keeps out-of-range source references explicit. -/
structure NativeObservationBoundedIn (n : Nat)
    (policy : P93CoupledRingChainAuthorityPolicy)
    (observation : P93CoupledRingChainAuthorityObservation policy) : Prop where
  certificate : NativeCertificateBoundedIn n observation.baseNameCertificate
  assignments :
    ∀ assignment ∈ observation.assignments,
      NativeEvidenceBoundedIn n policy.descriptorPolicies assignment.evidence
  components :
    ∀ component ∈ observation.repeatedComponents,
      ∀ atom ∈ component.atoms, atom < n

/-- A raw native coupled observation source: the exact source binding plus an ordered list of
`Nat`-indexed carrier observations, each valid at the bound source. -/
structure RawNativeCoupledObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93CoupledRingChainAuthorityPolicy) where
  binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V
  observations : List (P93CoupledRingChainAuthorityObservation policy)
  valid : ∀ observation ∈ observations, observation.ValidFor policy binding.source

/-- The composable native satellite.  It carries the same graph/spatial/diagram context as the
existing molecule codec and the ordered list of native observations.  Neither an original
observation record nor an original `AuthoritativeChemicalInput` is stored here. -/
structure NativeCoupledObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93CoupledRingChainAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (SuppliedNativeCoupledRingChainObservation V policy)

namespace NativeCoupledObservationSatellite

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {policy : P93CoupledRingChainAuthorityPolicy}

def toFiniteSource (satellite : NativeCoupledObservationSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end NativeCoupledObservationSatellite

section CoupledObservations

variable {policy : P93CoupledRingChainAuthorityPolicy}

def relabelNativeObservation [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (bounded : NativeObservationBoundedIn n policy observation) :
    SuppliedNativeCoupledRingChainObservation V policy where
  reviewedBaseName := observation.reviewedBaseName
  baseNameCertificate :=
    relabelNativeCertificate e observation.baseNameCertificate bounded.certificate
  annotatedBaseName := observation.annotatedBaseName
  assignments :=
    observation.assignments.attach.map fun assignment =>
      relabelNativeDescriptorAssignment e assignment.1
        (bounded.assignments assignment.1 assignment.2)
  multiplicativeSelected := observation.multiplicativeSelected
  repeatedComponents :=
    relabelRepeatedComponentList e observation.repeatedComponents bounded.components
  componentCorrespondences :=
    relabelComponentCorrespondenceList e observation.componentCorrespondences
  assignmentOwnerships := observation.assignmentOwnerships

def unrelabelNativeObservation [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedNativeCoupledRingChainObservation V policy) :
    P93CoupledRingChainAuthorityObservation policy where
  reviewedBaseName := observation.reviewedBaseName
  baseNameCertificate :=
    unrelabelNativeCertificate e observation.baseNameCertificate
  annotatedBaseName := observation.annotatedBaseName
  assignments :=
    observation.assignments.map (unrelabelNativeDescriptorAssignment e)
  multiplicativeSelected := observation.multiplicativeSelected
  repeatedComponents :=
    unrelabelRepeatedComponentList e observation.repeatedComponents
  componentCorrespondences :=
    unrelabelComponentCorrespondenceList e observation.componentCorrespondences
  assignmentOwnerships := observation.assignmentOwnerships

def unrelabelNativeObservationBounded [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedNativeCoupledRingChainObservation V policy) :
    NativeObservationBoundedIn n policy
      (unrelabelNativeObservation e observation) where
  certificate :=
    unrelabelNativeCertificateBounded e observation.baseNameCertificate
  assignments := fun assignment member => by
    rw [unrelabelNativeObservation, List.mem_map] at member
    rcases member with ⟨presented, _presentedMember, rfl⟩
    exact unrelabelNativeDescriptorAssignmentBounded e presented
  components :=
    unrelabelRepeatedComponentListBounded e observation.repeatedComponents

/-- The observation-level normalization fixed point needed by the source-side inverse.  For
source-valid observations it follows from validity
(`nativeObservationNormalizationFixed_of_validFor`). -/
def NativeObservationNormalizationFixed
    (observation : P93CoupledRingChainAuthorityObservation policy) : Prop :=
  ∀ assignment ∈ observation.assignments, EvidenceNormalizationFixed assignment.evidence

/-- The observation-level fixed point is derived from the observation's own `ValidFor`. -/
theorem nativeObservationNormalizationFixed_of_validFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    NativeObservationNormalizationFixed observation := by
  intro assignment member
  exact EvidenceNormalizationFixed.of_validFor source policy.descriptorPolicies
    assignment.evidence (valid.2.2.2.2.2.2.2.1 assignment member).1

/-- **Exact source-side recovery of a complete native observation.** -/
theorem unrelabelNativeObservation_relabelNativeObservation [DecidableEq V]
    (e : V ≃ Fin n)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (bounded : NativeObservationBoundedIn n policy observation)
    (normalizationFixed : NativeObservationNormalizationFixed observation) :
    unrelabelNativeObservation e
        (relabelNativeObservation e observation bounded) = observation := by
  obtain ⟨reviewedBaseName, baseNameCertificate, annotatedBaseName, assignments,
    multiplicativeSelected, repeatedComponents, componentCorrespondences,
    assignmentOwnerships⟩ := observation
  have assignmentEq :
      List.map (unrelabelNativeDescriptorAssignment e)
          (List.map
            (fun assignment =>
              relabelNativeDescriptorAssignment e assignment.1
                (bounded.assignments assignment.1 assignment.2))
            assignments.attach) = assignments := by
    rw [List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact unrelabelNativeDescriptorAssignment_relabelNativeDescriptorAssignment e
        assignment.1 (bounded.assignments assignment.1 assignment.2)
        (normalizationFixed assignment.1 assignment.2)
    · exact List.attach_map_subtype_val assignments
  have correspondenceEq :
      unrelabelComponentCorrespondenceList e
          (relabelComponentCorrespondenceList e componentCorrespondences) =
        componentCorrespondences :=
    unrelabelComponentCorrespondenceList_relabelComponentCorrespondenceList e
      componentCorrespondences
  simp [relabelNativeObservation, unrelabelNativeObservation, assignmentEq,
    unrelabelNativeCertificate_relabelNativeCertificate,
    unrelabelRepeatedComponentList_relabelRepeatedComponentList, correspondenceEq]

/-- Native observations whose hybrid correspondence atoms are all canonical. -/
def NativeCoupledObservationCanonical [DecidableEq V] (e : V ≃ Fin n)
    (observation : SuppliedNativeCoupledRingChainObservation V policy) : Prop :=
  ComponentCorrespondenceListCanonical e observation.componentCorrespondences

/-- Native observations whose stored axes raw syntax is already normalized. -/
def NativeObservationRawSyntaxNormalized
    (observation : SuppliedNativeCoupledRingChainObservation V policy) : Prop :=
  ∀ assignment ∈ observation.assignments,
    NativeEvidenceRawSyntaxNormalized assignment.evidence

/-- **Native-side exactness of a complete observation.**  The correspondence canonicality and the
raw-syntax fixed point are explicit native-side conditions; they are not assumed for the source
direction. -/
theorem relabelNativeObservation_unrelabelNativeObservation [DecidableEq V]
    (e : V ≃ Fin n)
    (observation : SuppliedNativeCoupledRingChainObservation V policy)
    (canonical : NativeCoupledObservationCanonical e observation)
    (rawSyntaxNormalized : NativeObservationRawSyntaxNormalized observation) :
    relabelNativeObservation e (unrelabelNativeObservation e observation)
        (unrelabelNativeObservationBounded e observation) = observation := by
  obtain ⟨reviewedBaseName, baseNameCertificate, annotatedBaseName, assignments,
    multiplicativeSelected, repeatedComponents, componentCorrespondences,
    assignmentOwnerships⟩ := observation
  have assignmentEq :
      List.map
          (fun assignment =>
            relabelNativeDescriptorAssignment e assignment.1
              ((unrelabelNativeObservationBounded e
                ⟨reviewedBaseName, baseNameCertificate, annotatedBaseName, assignments,
                  multiplicativeSelected, repeatedComponents, componentCorrespondences,
                  assignmentOwnerships⟩).assignments assignment.1 assignment.2))
          (List.attach
            (List.map (unrelabelNativeDescriptorAssignment e) assignments)) =
        assignments := by
    rw [List.attach_map, List.map_map]
    trans assignments.attach.map Subtype.val
    · apply List.map_congr_left
      intro assignment _
      exact relabelNativeDescriptorAssignment_unrelabelNativeDescriptorAssignment e
        assignment.1 (rawSyntaxNormalized assignment.1 assignment.2)
    · exact List.attach_map_subtype_val assignments
  have correspondenceEq :
      relabelComponentCorrespondenceList e
          (unrelabelComponentCorrespondenceList e componentCorrespondences) =
        componentCorrespondences :=
    relabelComponentCorrespondenceList_unrelabelComponentCorrespondenceList e
      componentCorrespondences canonical
  simp [relabelNativeObservation, unrelabelNativeObservation, assignmentEq,
    relabelNativeCertificate_unrelabelNativeCertificate,
    relabelRepeatedComponentList_unrelabelRepeatedComponentList,
    correspondenceEq]

/-- Every field of a source-valid observation is bounded by the source atom count, derived from
its own `ValidFor`.  The native axes bounds are derived from the embedded axes `ValidFor`. -/
theorem NativeObservationBoundedIn.of_validFor
    (source : AuthoritativeChemicalInput)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    NativeObservationBoundedIn source.molecule.atomCount policy observation where
  certificate :=
    nativeCertificateBoundedIn_of_validFor source observation.reviewedBaseName
      observation.baseNameCertificate valid.2.1
  assignments := fun assignment member =>
    NativeEvidenceBoundedIn.of_validFor source policy.descriptorPolicies assignment.evidence
      (valid.2.2.2.2.2.2.2.1 assignment member).1 valid.2.1.2.1.2.1
  components := by
    have componentsValid : P93RingChainRepeatedComponentsValid source
        observation.repeatedComponents := by
      have decision := valid.2.2.2.2.2.2.2.2.2.2.2
      generalize hb : observation.multiplicativeSelected = b at decision
      cases decision with
      | selected symmetryComplete => exact symmetryComplete.1
      | rejected rejection => exact rejection.componentsValid
    intro component member atom atomMember
    exact (componentsValid.2.2.1 component member).2 atom atomMember

theorem NativeObservationBoundedIn.of_validFor_binding [DecidableEq V] [Fintype V]
    (binding : OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (valid : observation.ValidFor policy binding.source) :
    NativeObservationBoundedIn (Fintype.card V) policy observation := by
  have bounded := NativeObservationBoundedIn.of_validFor binding.source observation valid
  rwa [binding.atomCount_eq] at bounded

/-! ## Ordered lists of native observations -/

def relabelNativeObservationList [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      NativeObservationBoundedIn n policy observation) :
    List (SuppliedNativeCoupledRingChainObservation V policy) :=
  observations.attach.map fun observation =>
    relabelNativeObservation e observation.1 (bounded observation.1 observation.2)

def unrelabelNativeObservationList [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SuppliedNativeCoupledRingChainObservation V policy)) :
    List (P93CoupledRingChainAuthorityObservation policy) :=
  observations.map (unrelabelNativeObservation e)

def unrelabelNativeObservationListBounded [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SuppliedNativeCoupledRingChainObservation V policy)) :
    ∀ observation ∈ unrelabelNativeObservationList e observations,
      NativeObservationBoundedIn n policy observation := by
  intro observation member
  rw [unrelabelNativeObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelNativeObservationBounded e presented

@[simp] theorem relabelNativeObservationList_length [DecidableEq V]
    (e : V ≃ Fin n)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      NativeObservationBoundedIn n policy observation) :
    (relabelNativeObservationList e observations bounded).length =
      observations.length := by
  simp [relabelNativeObservationList]

/-- Ordered-list inverse: order and repetitions are preserved exactly. -/
theorem unrelabelNativeObservationList_relabelNativeObservationList [DecidableEq V]
    (e : V ≃ Fin n)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      NativeObservationBoundedIn n policy observation)
    (normalizationFixed : ∀ observation ∈ observations,
      NativeObservationNormalizationFixed observation) :
    unrelabelNativeObservationList e
        (relabelNativeObservationList e observations bounded) = observations := by
  unfold unrelabelNativeObservationList relabelNativeObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelNativeObservation_relabelNativeObservation e observation.1
      (bounded observation.1 observation.2)
      (normalizationFixed observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

def NativeObservationListCanonical [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SuppliedNativeCoupledRingChainObservation V policy)) : Prop :=
  ∀ observation ∈ observations, NativeCoupledObservationCanonical e observation

def NativeObservationListRawSyntaxNormalized
    (observations : List (SuppliedNativeCoupledRingChainObservation V policy)) : Prop :=
  ∀ observation ∈ observations, NativeObservationRawSyntaxNormalized observation

theorem relabelNativeObservationList_unrelabelNativeObservationList [DecidableEq V]
    (e : V ≃ Fin n)
    (observations : List (SuppliedNativeCoupledRingChainObservation V policy))
    (canonical : NativeObservationListCanonical e observations)
    (rawSyntaxNormalized : NativeObservationListRawSyntaxNormalized observations) :
    relabelNativeObservationList e
        (unrelabelNativeObservationList e observations)
        (unrelabelNativeObservationListBounded e observations) = observations := by
  unfold relabelNativeObservationList unrelabelNativeObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelNativeObservation_unrelabelNativeObservation e observation.1
      (canonical observation.1 observation.2)
      (rawSyntaxNormalized observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-! ## Correlated arbitrary sets of native observations -/

def relabelNativeObservationSet [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      NativeObservationBoundedIn n policy observation) :
    Set (SuppliedNativeCoupledRingChainObservation V policy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelNativeObservation e observation (bounded observation member) = presented

def unrelabelNativeObservationSet [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SuppliedNativeCoupledRingChainObservation V policy)) :
    Set (P93CoupledRingChainAuthorityObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations, unrelabelNativeObservation e presented = recovered

def unrelabelNativeObservationSetBounded [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SuppliedNativeCoupledRingChainObservation V policy)) :
    ∀ observation ∈ unrelabelNativeObservationSet e observations,
      NativeObservationBoundedIn n policy observation := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelNativeObservationBounded e presented

theorem unrelabelNativeObservationSet_relabelNativeObservationSet [DecidableEq V]
    (e : V ≃ Fin n)
    (observations : Set (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      NativeObservationBoundedIn n policy observation)
    (normalizationFixed : ∀ observation ∈ observations,
      NativeObservationNormalizationFixed observation) :
    unrelabelNativeObservationSet e
        (relabelNativeObservationSet e observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelNativeObservation_relabelNativeObservation e observation
      (bounded observation member) (normalizationFixed observation member)] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelNativeObservation e recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelNativeObservation_relabelNativeObservation e recovered
        (bounded recovered member) (normalizationFixed recovered member)⟩

theorem relabelNativeObservation_bound_irrel [DecidableEq V] (e : V ≃ Fin n)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (first second : NativeObservationBoundedIn n policy observation) :
    relabelNativeObservation e observation first =
      relabelNativeObservation e observation second := by
  cases observation
  rfl

theorem relabelNativeObservation_congr [DecidableEq V] (e : V ≃ Fin n)
    {first second : P93CoupledRingChainAuthorityObservation policy}
    (h : first = second)
    (firstBounded : NativeObservationBoundedIn n policy first)
    (secondBounded : NativeObservationBoundedIn n policy second) :
    relabelNativeObservation e first firstBounded =
      relabelNativeObservation e second secondBounded := by
  cases h
  exact relabelNativeObservation_bound_irrel e _ firstBounded secondBounded

def NativeObservationSetCanonical [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SuppliedNativeCoupledRingChainObservation V policy)) : Prop :=
  ∀ observation ∈ observations, NativeCoupledObservationCanonical e observation

def NativeObservationSetRawSyntaxNormalized
    (observations : Set (SuppliedNativeCoupledRingChainObservation V policy)) : Prop :=
  ∀ observation ∈ observations, NativeObservationRawSyntaxNormalized observation

theorem relabelNativeObservationSet_unrelabelNativeObservationSet [DecidableEq V]
    (e : V ≃ Fin n)
    (observations : Set (SuppliedNativeCoupledRingChainObservation V policy))
    (canonical : NativeObservationSetCanonical e observations)
    (rawSyntaxNormalized : NativeObservationSetRawSyntaxNormalized observations) :
    relabelNativeObservationSet e
        (unrelabelNativeObservationSet e observations)
        (unrelabelNativeObservationSetBounded e observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have presentedEq : presented = presented₀ := by
      calc
        presented =
            relabelNativeObservation e observation
              (unrelabelNativeObservationSetBounded e observations observation
                ⟨presented₀, presentedMember, decodeEq⟩) := relabelEq.symm
        _ = relabelNativeObservation e
              (unrelabelNativeObservation e presented₀)
              (unrelabelNativeObservationBounded e presented₀) :=
            relabelNativeObservation_congr e decodeEq.symm _ _
        _ = presented₀ :=
            relabelNativeObservation_unrelabelNativeObservation e presented₀
              (canonical presented₀ presentedMember)
              (rawSyntaxNormalized presented₀ presentedMember)
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelNativeObservation e presented,
      ⟨presented, member, rfl⟩,
      relabelNativeObservation_unrelabelNativeObservation e presented
        (canonical presented member) (rawSyntaxNormalized presented member)⟩

/-- **Correlated set validity at the same source and policy.**  A native observation belongs to
the image of a set exactly when its decoded record is one of the source observations.
`normalizationFixed` is the per-observation fixed point, derivable from that observation's own
`ValidFor`; it is needed only because the successor decoder recomputes the normalization. -/
theorem validFor_mem_relabelNativeObservationSet_iff [DecidableEq V]
    (e : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observations : Set (P93CoupledRingChainAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations,
      NativeObservationBoundedIn n policy observation)
    (normalizationFixed : ∀ observation ∈ observations,
      NativeObservationNormalizationFixed observation)
    (presented : SuppliedNativeCoupledRingChainObservation V policy)
    (member : presented ∈ relabelNativeObservationSet e observations bounded) :
    (unrelabelNativeObservation e presented).ValidFor policy source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelNativeObservation e observation
            (bounded observation observationMember) = presented ∧
          observation.ValidFor policy source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rw [unrelabelNativeObservation_relabelNativeObservation e observation
      (bounded observation observationMember)
      (normalizationFixed observation observationMember)] at valid
    exact valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rw [unrelabelNativeObservation_relabelNativeObservation e observation
      (bounded observation observationMember)
      (normalizationFixed observation observationMember)]
    exact valid

/-! ## Shared source context and the composable satellite -/

def adaptNative [DecidableEq V] [Fintype V]
    (raw : RawNativeCoupledObservationSource V policy) :
    NativeCoupledObservationSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelNativeObservation raw.binding.enumeration observation.1
      (NativeObservationBoundedIn.of_validFor_binding raw.binding observation.1
        (raw.valid observation.1 observation.2))

@[simp] theorem adaptNative_graph [DecidableEq V] [Fintype V]
    (raw : RawNativeCoupledObservationSource V policy) :
    (adaptNative raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adaptNative_spatial? [DecidableEq V] [Fintype V]
    (raw : RawNativeCoupledObservationSource V policy) :
    (adaptNative raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adaptNative_diagram? [DecidableEq V] [Fintype V]
    (raw : RawNativeCoupledObservationSource V policy) :
    (adaptNative raw).diagram? = raw.binding.shared.diagram? := rfl

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; observations are decoded with the same enumeration. -/
def suppliedSource [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V))
    (satellite : NativeCoupledObservationSatellite V policy) :
    RecoveredCoupledObservationSource policy where
  source := satellite.toFiniteSource.encode e
  observations := unrelabelNativeObservationList e satellite.observations

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input (through the binding's actual source equality) and the exact ordered list of
pre-existing coupled ring-chain observation records, including order and repetitions. -/
theorem suppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawNativeCoupledObservationSource V policy) :
    suppliedSource raw.binding.enumeration (adaptNative raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredCoupledObservationSource.ext
  · exact raw.binding.encode_shared
  · change unrelabelNativeObservationList raw.binding.enumeration
        (adaptNative raw).observations = raw.observations
    rw [show (adaptNative raw).observations = raw.observations.attach.map (fun observation =>
        relabelNativeObservation raw.binding.enumeration observation.1
          (NativeObservationBoundedIn.of_validFor_binding raw.binding observation.1
            (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelNativeObservationList_relabelNativeObservationList
      raw.binding.enumeration raw.observations
      (fun observation member =>
        NativeObservationBoundedIn.of_validFor_binding raw.binding observation
          (raw.valid observation member))
      (fun observation member =>
        nativeObservationNormalizationFixed_of_validFor raw.binding.source observation
          (raw.valid observation member))

/-- Validity is preserved for the whole recovered list at the same source and policy. -/
theorem suppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawNativeCoupledObservationSource V policy)
    (observation : P93CoupledRingChainAuthorityObservation policy)
    (member : observation ∈
      (suppliedSource raw.binding.enumeration (adaptNative raw)).observations) :
    observation.ValidFor policy raw.binding.source := by
  have listEq : (suppliedSource raw.binding.enumeration (adaptNative raw)).observations =
      raw.observations := by
    simpa using congrArg (RecoveredCoupledObservationSource.observations)
      (suppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-! ## Concrete certified-source adapter -/

def certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding
      (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    NativeCoupledObservationSatellite (Fin certified.input.molecule.atomCount) policy :=
  adaptNative { binding := certifiedBinding certified
                observations := observations
                valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (P93CoupledRingChainAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor policy certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := certifiedBinding certified
      observations := observations
      valid := valid }

end CoupledObservations

end OrganicStereoCoupledRingChainNativeAxes

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.decodeIndexedLookup_encodeIndexedLookup
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.encodeIndexedLookup_decodeIndexedLookup
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.nativeAxesNormalizationFixed_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeAxes_relabelNativeAxes
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.relabelNativeAxes_unrelabelNativeAxes
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.nativeAxesSourceBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.nativeAxesSourceBoundedIn_of_validFor_binding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.nativeCertificateBoundedIn_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.nativeCertificateBoundedIn_of_validFor_binding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeCertificate_relabelNativeCertificate
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.relabelNativeCertificate_unrelabelNativeCertificate
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.EvidenceNormalizationFixed.of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.nativeObservationNormalizationFixed_of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeEvidence_relabelNativeEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.relabelNativeEvidence_unrelabelNativeEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.NativeEvidenceBoundedIn.of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeDescriptorAssignment_relabelNativeDescriptorAssignment
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.relabelNativeDescriptorAssignment_unrelabelNativeDescriptorAssignment
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservation_relabelNativeObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservation_unrelabelNativeObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.NativeObservationBoundedIn.of_validFor_binding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservationList_relabelNativeObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservationList_unrelabelNativeObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.unrelabelNativeObservationSet_relabelNativeObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.relabelNativeObservationSet_unrelabelNativeObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.validFor_mem_relabelNativeObservationSet_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.suppliedSource_adapt_validFor
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCoupledRingChainNativeAxes.suppliedSource_adaptCertified
