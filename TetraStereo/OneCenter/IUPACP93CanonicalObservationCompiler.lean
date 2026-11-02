import TetraStereo.OneCenter.IUPACP93CanonicalObservationCompilerCore
import TetraStereo.OneCenter.IUPACP93CanonicalObservationCompilerCyclic

set_option autoImplicit false

/-!
# Canonical P-93 observation compiler

This module erases one clause-indexed canonical source payload into the corresponding reviewed
authority observation.  Its theorems are entry-local: source-key inversion prevents another
program entry from enlarging a closed-world policy relation, while the physical-support manifest
supplies the audited qualitative frame used by the observation.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open BlueBookP93.NoncarbonTetrahedra
open IUPACNormativeProvision

namespace P93CanonicalSourceProgram



def IncludedPayloadContext.ofSubset
    {program : P93CanonicalSourceProgram} {scope : P93ClaimFamily}
    {source : AuthoritativeChemicalInput} {outerClause innerClause : P93Clause}
    {outer : P93ClausePayloadData outerClause} {inner : P93ClausePayloadData innerClause}
    (outerCtx : PayloadContext program scope source outer)
    (validFor : inner.ValidFor source)
    (claimsSubset : ∀ claim ∈ inner.toClaims, claim ∈ outer.toClaims)
    (exactPhysicalSubset : ∀ claim ∈ inner.exactQualitativePhysicalClaims,
      claim ∈ outer.exactQualitativePhysicalClaims) :
    IncludedPayloadContext program scope source inner where
  validFor := validFor
  claimsIncluded := fun claim claimMem =>
    (outerCtx.claimsExact claim).2 (claimsSubset claim claimMem)
  qualitativeSupported := by
    intro unit unitMem
    exact outerCtx.qualitativeSupported unit (by
      rcases List.mem_flatMap.mp unitMem with ⟨claim, claimMem, unitMem⟩
      exact List.mem_flatMap.mpr ⟨claim, claimsSubset claim claimMem, unitMem⟩)
  exactPhysicalSupported := fun claim claimMem =>
    outerCtx.exactPhysicalSupported claim (exactPhysicalSubset claim claimMem)

theorem nestedClaim_mem_coupledClaims
    (payload : P93CoupledClausePayload)
    {evidence : P93CanonicalReviewedDescriptorEvidence}
    (evidenceMem : evidence ∈ payload.assignments)
    {claim : P93SourceClaim} (claimMem : claim ∈ evidence.upstreamClaims) :
    claim ∈ payload.toClaims := by
  simp only [P93CoupledClausePayload.toClaims, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨evidence, evidenceMem, Or.inl (Or.inl claimMem)⟩)

theorem nestedExactPhysical_mem_coupledExactPhysical
    (payload : P93CoupledClausePayload)
    {evidence : P93CanonicalReviewedDescriptorEvidence}
    (evidenceMem : evidence ∈ payload.assignments)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ evidence.exactQualitativePhysicalClaims) :
    claim ∈ payload.exactQualitativePhysicalClaims := by
  exact List.mem_flatMap.mpr ⟨evidence, evidenceMem, claimMem⟩

def IncludedPayloadContext.ofCoupledEvidence
    {program : P93CanonicalSourceProgram} {scope : P93ClaimFamily}
    {source : AuthoritativeChemicalInput} {innerClause : P93Clause}
    {inner : P93ClausePayloadData innerClause}
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program scope source (.coupled coupledPayload))
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (evidenceMem : evidence ∈ coupledPayload.assignments)
    (upstreamEq : evidence.upstreamClaims = inner.toClaims)
    (exactPhysicalEq : evidence.exactQualitativePhysicalClaims =
      inner.exactQualitativePhysicalClaims)
    (validFor : inner.ValidFor source) :
    IncludedPayloadContext program scope source inner := by
  apply IncludedPayloadContext.ofSubset outerCtx validFor
  · intro claim claimMem
    exact nestedClaim_mem_coupledClaims coupledPayload evidenceMem
      (by simpa [upstreamEq] using claimMem)
  · intro claim claimMem
    exact nestedExactPhysical_mem_coupledExactPhysical coupledPayload evidenceMem
      (by simpa [exactPhysicalEq] using claimMem)



theorem nonCoupledClaim_origin
    (payload : P93CoupledClausePayload) {claim : P93SourceClaim}
    (notCoupled : ∀ coupledClaim, claim ≠ .coupled coupledClaim)
    (claimMem : claim ∈ payload.toClaims) :
    ∃ evidence ∈ payload.assignments, claim ∈ evidence.upstreamClaims := by
  rw [P93CoupledClausePayload.toClaims] at claimMem
  rcases List.mem_append.mp claimMem with beforeDecision | decision
  · rcases List.mem_append.mp beforeDecision with base | nested
    · simp only [List.mem_singleton] at base
      exact False.elim (notCoupled _ base)
    · rcases List.mem_flatMap.mp nested with ⟨evidence, evidenceMem, evidenceClaim⟩
      rcases List.mem_append.mp evidenceClaim with upstreamOrOwn | citation
      · rcases List.mem_append.mp upstreamOrOwn with upstream | own
        · exact ⟨evidence, evidenceMem, upstream⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at own
          exact own.elim (fun eq => False.elim (notCoupled _ eq))
            (fun eq => False.elim (notCoupled _ eq))
      · rcases List.mem_map.mp citation with ⟨citation, _, citationEq⟩
        exact False.elim (notCoupled _ citationEq.symm)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at decision
    exact decision.elim (fun eq => False.elim (notCoupled _ eq))
      (fun eq => False.elim (notCoupled _ eq))

theorem physicalValidFor_of_envelope
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    {unit : P93AuthorityPhysicalUnit}
    (envelope : P93CanonicalPhysicalUnitEnvelope entry.source unit)
    (unitMem : unit ∈ entry.qualitativePhysicalUnits) :
    unit.ValidFor (program.physicalPolicy entry.clause.family) entry.source := by
  cases unit with
  | atomCenter center => exact envelope
  | bond first second => exact envelope
  | axis path => exact envelope
  | plane members =>
      rcases program.qualitative_support_for entryMem unitMem with
        ⟨support, supportMem, sourceEq, clauseEq, unitEq⟩
      have supportEnvelope := support.sourceEnvelope
      rw [sourceEq] at supportEnvelope
      cases supportClaimEq : support.claim with
      | helix path frame => simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
      | polyhedron center positions geometry frame =>
          simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
      | plane supportMembers frame =>
          simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
          subst supportMembers
          simp [P93PhysicalClaim.SourceEnvelope, supportClaimEq] at supportEnvelope
          refine ⟨frame, supportEnvelope, ?_⟩
          exact ⟨support, supportMem, sourceEq,
            congrArg P93Clause.family clauseEq, supportClaimEq⟩


  | helix path =>
      rcases program.qualitative_support_for entryMem unitMem with
        ⟨support, supportMem, sourceEq, clauseEq, unitEq⟩
      have supportEnvelope := support.sourceEnvelope
      rw [sourceEq] at supportEnvelope
      cases supportClaimEq : support.claim with
      | plane members frame => simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
      | polyhedron center positions geometry frame =>
          simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
      | helix supportPath frame =>
          simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
          subst supportPath
          simp [P93PhysicalClaim.SourceEnvelope, supportClaimEq] at supportEnvelope
          refine ⟨frame, supportEnvelope, ?_⟩
          exact ⟨support, supportMem, sourceEq,
            congrArg P93Clause.family clauseEq, supportClaimEq⟩
  | polyhedron center positions =>
      rcases program.qualitative_support_for entryMem unitMem with
        ⟨support, supportMem, sourceEq, clauseEq, unitEq⟩
      have supportEnvelope := support.sourceEnvelope
      rw [sourceEq] at supportEnvelope
      cases supportClaimEq : support.claim with
      | plane members frame => simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
      | helix path frame => simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
      | polyhedron supportCenter supportPositions geometry frame =>
          simp [P93PhysicalClaim.unit, supportClaimEq] at unitEq
          rcases unitEq with ⟨rfl, rfl⟩
          simp [P93PhysicalClaim.SourceEnvelope, supportClaimEq] at supportEnvelope
          refine ⟨geometry, frame, supportEnvelope, ?_⟩
          exact ⟨support, supportMem, sourceEq,
            congrArg P93Clause.family clauseEq, supportClaimEq⟩

/-! ## Coupled evidence erasure -/

@[simp] theorem canonicalEvidence_toAuthority_unit
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (valid : evidence.ValidFor source) :
    (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
      program source evidence valid).unit = evidence.unit := by
  cases evidence <;>
    first
    | cases ‹P93AcyclicClausePayload _› <;> rfl
    | cases ‹P93MonocyclicClausePayload _› <;> rfl
    | cases ‹P93FusedCyclophaneClausePayload _› <;>
        simp_all [P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority,
          P93CanonicalReviewedDescriptorEvidence.unit,
          P93RingChainReviewedDescriptorEvidence.unit]
    | cases ‹P93RingAssemblyClausePayload _› <;> rfl
    | rfl
  all_goals
    cases ‹P93CyclophaneCenterSpecification› <;> simp_all
  all_goals
    rcases valid.2.2 with ⟨context, kind, descriptor, impossible⟩
    cases impossible

@[simp] theorem canonicalEvidence_toAuthority_citation
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (valid : evidence.ValidFor source) :
    (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
      program source evidence valid).citation? = evidence.citation? := by
  cases evidence <;>
    first
    | cases ‹P93AcyclicClausePayload _› <;> rfl
    | cases ‹P93MonocyclicClausePayload _› <;> rfl
    | cases ‹P93FusedCyclophaneClausePayload _› <;>
        simp_all [P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority,
          P93CanonicalReviewedDescriptorEvidence.citation?,
          P93RingChainReviewedDescriptorEvidence.citation?]
    | cases ‹P93RingAssemblyClausePayload _› <;> rfl
    | rfl
  all_goals
    cases ‹P93CyclophaneCenterSpecification› <;> simp_all
  all_goals
    rcases valid.2.2 with ⟨context, kind, descriptor, impossible⟩
    cases impossible

def P93CanonicalDescriptor.toRingChain : P93CanonicalDescriptor → P93RingChainDescriptor
  | .acyclic descriptor => .acyclic descriptor
  | .fused descriptor => .fused descriptor
  | .cyclophanePlane descriptor => .cyclophanePlane descriptor
  | .cyclophaneRelativeCenter descriptor => .cyclophaneRelativeCenter descriptor
  | .polyhedral descriptor => .polyhedral descriptor
  | .fullerene _ => .acyclic .R
  | .ringAssemblyAxis descriptor => .ringAssemblyAxis descriptor
  | .ringAssemblyCenter descriptor => .ringAssemblyCenter descriptor

@[simp] theorem canonicalEvidence_toAuthority_descriptor
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (valid : evidence.ValidFor source) :
    (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
      program source evidence valid).descriptor =
        P93CanonicalReviewedDescriptorEvidence.ringDescriptor evidence := by
  cases evidence <;>
    first
    | cases ‹P93AcyclicClausePayload _› <;> rfl
    | cases ‹P93MonocyclicClausePayload _› <;> rfl
    | cases ‹P93FusedCyclophaneClausePayload _› <;>
        simp_all [P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority,
          P93CanonicalReviewedDescriptorEvidence.ringDescriptor,
          P93CanonicalReviewedDescriptorEvidence.descriptor,
          P93RingChainReviewedDescriptorEvidence.descriptor]
    | cases ‹P93RingAssemblyClausePayload _› <;> rfl
    | rfl
  all_goals
    cases ‹P93CyclophaneCenterSpecification› <;> simp_all
  all_goals
    rcases valid.2.2 with ⟨context, kind, descriptor, impossible⟩
    cases impossible

def coupledAssignments
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source) :
    List (P93RingChainDescriptorAssignment program.coupledDescriptorPolicies) :=
  assignments.pmap
    (fun evidence valid =>
      { evidence :=
          P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
            program source evidence valid })
    allValid

@[simp] theorem coupledAssignments_map_unit
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source) :
    (coupledAssignments program source assignments allValid).map
        P93RingChainDescriptorAssignment.unit =
      assignments.map P93CanonicalReviewedDescriptorEvidence.unit := by
  induction assignments with
  | nil => rfl
  | cons head tail ih =>
      simpa only [coupledAssignments, List.pmap, List.map_cons,
          P93RingChainDescriptorAssignment.unit,
          canonicalEvidence_toAuthority_unit] using
        congrArg (List.cons head.unit)
          (ih (fun evidence evidenceMem =>
            allValid evidence (List.mem_cons_of_mem head evidenceMem)))

@[simp] theorem coupledAssignments_filterMap_citation
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source) :
    (coupledAssignments program source assignments allValid).filterMap
        (fun assignment => assignment.evidence.citation?) =
      assignments.filterMap P93CanonicalReviewedDescriptorEvidence.citation? := by
  induction assignments with
  | nil => rfl
  | cons head tail ih =>
      cases citationEq : head.citation? with
      | none =>
          simpa only [coupledAssignments, List.pmap, List.filterMap_cons,
              canonicalEvidence_toAuthority_citation, citationEq] using
            ih (fun evidence evidenceMem =>
              allValid evidence (List.mem_cons_of_mem head evidenceMem))
      | some citation =>
          simpa only [coupledAssignments, List.pmap, List.filterMap_cons,
              canonicalEvidence_toAuthority_citation, citationEq] using
            congrArg (List.cons citation)
              (ih (fun evidence evidenceMem =>
                allValid evidence (List.mem_cons_of_mem head evidenceMem)))

@[simp] theorem coupledAssignments_map_physicalIdentity
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source) :
    (coupledAssignments program source assignments allValid).map
        (fun assignment => assignment.unit.physicalIdentity) =
      assignments.map (fun assignment => assignment.unit.physicalIdentity) := by
  induction assignments with
  | nil => rfl
  | cons head tail ih =>
      simpa only [coupledAssignments, List.pmap, List.map_cons,
          P93RingChainDescriptorAssignment.unit,
          canonicalEvidence_toAuthority_unit] using
        congrArg (List.cons head.unit.physicalIdentity)
          (ih (fun evidence evidenceMem =>
            allValid evidence (List.mem_cons_of_mem head evidenceMem)))

@[simp] theorem coupledAssignments_length
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source) :
    (coupledAssignments program source assignments allValid).length = assignments.length := by
  simp [coupledAssignments]

theorem coupledAssignments_get?_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    {index : Nat} {evidence : P93CanonicalReviewedDescriptorEvidence}
    (atIndex : assignments[index]? = some evidence) :
    ∃ valid : evidence.ValidFor source,
      (coupledAssignments program source assignments allValid)[index]? =
        some
          { evidence :=
              P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
                program source evidence valid } := by
  induction assignments generalizing index evidence with
  | nil => simp at atIndex
  | cons head tail ih =>
      cases index with
      | zero =>
          simp at atIndex
          subst evidence
          refine ⟨allValid head (by simp), ?_⟩
          rfl
      | succ index =>
          change tail[index]? = some evidence at atIndex
          obtain ⟨valid, result⟩ := ih
            (fun candidate candidateMem =>
              allValid candidate (List.mem_cons_of_mem head candidateMem)) atIndex
          exact ⟨valid, result⟩

theorem coupledAssignments_canonical_of_get?
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    {index : Nat}
    {assignment : P93RingChainDescriptorAssignment program.coupledDescriptorPolicies}
    (atIndex : (coupledAssignments program source assignments allValid)[index]? =
      some assignment) :
    ∃ evidence, ∃ valid : evidence.ValidFor source,
      assignments[index]? = some evidence ∧
        assignment =
          { evidence :=
              P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
                program source evidence valid } := by
  induction assignments generalizing index assignment with
  | nil => simp [coupledAssignments] at atIndex
  | cons head tail ih =>
      cases index with
      | zero =>
          simp [coupledAssignments] at atIndex
          refine ⟨head, allValid head (by simp), rfl, ?_⟩
          exact atIndex.symm
      | succ index =>
          simp [coupledAssignments] at atIndex
          rcases atIndex with ⟨evidence, canonicalAtIndex, valid, assignmentEq⟩
          exact ⟨evidence, valid, canonicalAtIndex, assignmentEq⟩

theorem coupledAssignments_mem_iff
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (assignment : P93RingChainDescriptorAssignment program.coupledDescriptorPolicies) :
    assignment ∈ coupledAssignments program source assignments allValid ↔
      ∃ evidence, ∃ evidenceMem : evidence ∈ assignments,
        assignment =
          { evidence :=
              P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
                program source evidence (allValid evidence evidenceMem) } := by
  constructor
  · intro assignmentMem
    rcases List.mem_iff_getElem?.1 assignmentMem with ⟨index, assignmentAtIndex⟩
    rcases coupledAssignments_canonical_of_get? program source assignments allValid
      assignmentAtIndex with ⟨evidence, valid, evidenceAtIndex, assignmentEq⟩
    have evidenceMem : evidence ∈ assignments :=
      List.mem_iff_getElem?.2 ⟨index, evidenceAtIndex⟩
    exact ⟨evidence, evidenceMem, assignmentEq⟩
  · rintro ⟨evidence, evidenceMem, rfl⟩
    rcases List.mem_iff_getElem?.1 evidenceMem with ⟨index, evidenceAtIndex⟩
    rcases coupledAssignments_get?_of_canonical program source assignments allValid
      evidenceAtIndex with ⟨valid, authorityAtIndex⟩
    exact List.mem_iff_getElem?.2 ⟨index, authorityAtIndex⟩

theorem coupledAssignmentOwnershipsComplete_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (ownerships : List P93RingChainAssignmentOwnership)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (complete : P93CanonicalAssignmentOwnershipsComplete components assignments ownerships) :
    P93RingChainAssignmentOwnershipsComplete components
      (coupledAssignments program source assignments allValid) ownerships := by
  rcases complete with ⟨ownershipKeys, ownershipSound, ownershipComplete⟩
  refine ⟨ownershipKeys, ?_, ?_⟩
  · intro ownership ownershipMem
    rcases ownershipSound ownership ownershipMem with
      ⟨evidence, component, evidenceAtIndex, componentAtIndex, touches⟩
    rcases coupledAssignments_get?_of_canonical program source assignments allValid
      evidenceAtIndex with ⟨valid, authorityAtIndex⟩
    refine ⟨
      { evidence :=
          P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
            program source evidence valid }, component, authorityAtIndex, componentAtIndex, ?_⟩
    change ¬Disjoint
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
        program source evidence valid).unit.atoms component.atoms
    rw [canonicalEvidence_toAuthority_unit]
    exact touches
  · intro assignmentIndex assignment assignmentAtIndex componentIndex component
      componentAtIndex touches
    rcases coupledAssignments_canonical_of_get? program source assignments allValid
      assignmentAtIndex with ⟨evidence, valid, evidenceAtIndex, rfl⟩
    apply ownershipComplete assignmentIndex evidence evidenceAtIndex componentIndex component
      componentAtIndex
    change ¬Disjoint
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
        program source evidence valid).unit.atoms component.atoms at touches
    rwa [canonicalEvidence_toAuthority_unit] at touches

theorem coupledAtomInOwnedBoundaryUnit_iff
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex atom : Nat) :
    P93RingChainAtomInOwnedBoundaryUnit
        (coupledAssignments program source assignments allValid) ownerships
        componentIndex atom ↔
      P93CanonicalAtomInOwnedBoundaryUnit assignments ownerships componentIndex atom := by
  constructor
  · rintro ⟨ownership, ownershipMem, assignment, componentEq, assignmentAtIndex,
      atomMem⟩
    rcases coupledAssignments_canonical_of_get? program source assignments allValid
      assignmentAtIndex with ⟨evidence, valid, evidenceAtIndex, rfl⟩
    refine ⟨ownership, ownershipMem, evidence, componentEq, evidenceAtIndex, ?_⟩
    change atom ∈
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
        program source evidence valid).unit.atoms at atomMem
    rwa [canonicalEvidence_toAuthority_unit] at atomMem
  · rintro ⟨ownership, ownershipMem, evidence, componentEq, evidenceAtIndex, atomMem⟩
    rcases coupledAssignments_get?_of_canonical program source assignments allValid
      evidenceAtIndex with ⟨valid, authorityAtIndex⟩
    refine ⟨ownership, ownershipMem,
      { evidence :=
          P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
            program source evidence valid }, componentEq, authorityAtIndex, ?_⟩
    change atom ∈
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
        program source evidence valid).unit.atoms
    rwa [canonicalEvidence_toAuthority_unit]

theorem coupledInterfaceAtom_iff
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex : Nat) (component : P93RingChainRepeatedComponent) (atom : Nat) :
    P93RingChainInterfaceAtom source components
        (coupledAssignments program source assignments allValid) ownerships
        componentIndex component atom ↔
      P93CanonicalRingChainInterfaceAtom source components assignments ownerships
        componentIndex component atom := by
  simp only [P93RingChainInterfaceAtom, P93CanonicalRingChainInterfaceAtom,
    coupledAtomInOwnedBoundaryUnit_iff]

theorem coupledInteractionTouchesOwnedInterface_iff
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (componentIndex : Nat) (component : P93RingChainRepeatedComponent)
    (interaction : SemanticInteraction) :
    P93RingChainInteractionTouchesOwnedInterface source components
        (coupledAssignments program source assignments allValid) ownerships
        componentIndex component interaction ↔
      P93CanonicalInteractionTouchesOwnedInterface source components assignments ownerships
        componentIndex component interaction := by
  simp only [P93RingChainInteractionTouchesOwnedInterface,
    P93CanonicalInteractionTouchesOwnedInterface, coupledInterfaceAtom_iff,
    coupledAtomInOwnedBoundaryUnit_iff]

theorem coupledComponentCorrespondenceValidFor_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (correspondence : P93RingChainComponentCorrespondence)
    (valid : P93CanonicalComponentCorrespondenceValidFor source components assignments
      ownerships correspondence) :
    correspondence.ValidFor source components
      (coupledAssignments program source assignments allValid) ownerships := by
  simpa only [P93CanonicalComponentCorrespondenceValidFor,
    P93RingChainComponentCorrespondence.ValidFor, coupledInterfaceAtom_iff,
    coupledInteractionTouchesOwnedInterface_iff] using valid

theorem coupledAssignmentsStereoCorrespond_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (leftIndex rightIndex : Nat)
    (correspondence : P93RingChainComponentCorrespondence)
    (stereo : P93CanonicalAssignmentsStereoCorrespond assignments ownerships
      leftIndex rightIndex correspondence) :
    P93RingChainAssignmentsStereoCorrespond
      (coupledAssignments program source assignments allValid) ownerships
      leftIndex rightIndex correspondence := by
  rcases stereo with ⟨leftToRight, rightToLeft⟩
  constructor
  · intro ownership ownershipMem componentEq assignment assignmentAtIndex
    rcases coupledAssignments_canonical_of_get? program source assignments allValid
      assignmentAtIndex with ⟨evidence, valid, evidenceAtIndex, rfl⟩
    rcases leftToRight ownership ownershipMem componentEq evidence evidenceAtIndex with
      ⟨mappedOwnership, mappedOwnershipMem, mappedEvidence, mappedComponentEq,
        mappedEvidenceAtIndex, unitsCorrespond, descriptorsEq⟩
    rcases coupledAssignments_get?_of_canonical program source assignments allValid
      mappedEvidenceAtIndex with ⟨mappedValid, mappedAuthorityAtIndex⟩
    refine ⟨mappedOwnership, mappedOwnershipMem,
      { evidence :=
          P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
            program source mappedEvidence mappedValid }, mappedComponentEq,
      mappedAuthorityAtIndex, ?_, ?_⟩
    · simpa only [P93RingChainDescriptorAssignment.unit,
        canonicalEvidence_toAuthority_unit] using unitsCorrespond
    · simpa only [P93RingChainDescriptorAssignment.descriptor,
        canonicalEvidence_toAuthority_descriptor] using
          congrArg P93CanonicalSourceProgram.P93CanonicalDescriptor.toRingChain descriptorsEq
  · intro mappedOwnership mappedOwnershipMem componentEq mappedAssignment mappedAtIndex
    rcases coupledAssignments_canonical_of_get? program source assignments allValid
      mappedAtIndex with ⟨mappedEvidence, mappedValid, mappedEvidenceAtIndex, rfl⟩
    rcases rightToLeft mappedOwnership mappedOwnershipMem componentEq mappedEvidence
      mappedEvidenceAtIndex with
      ⟨ownership, ownershipMem, evidence, ownershipComponentEq, evidenceAtIndex,
        unitsCorrespond, descriptorsEq⟩
    rcases coupledAssignments_get?_of_canonical program source assignments allValid
      evidenceAtIndex with ⟨valid, authorityAtIndex⟩
    refine ⟨ownership, ownershipMem,
      { evidence :=
          P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
            program source evidence valid }, ownershipComponentEq, authorityAtIndex, ?_, ?_⟩
    · simpa only [P93RingChainDescriptorAssignment.unit,
        canonicalEvidence_toAuthority_unit] using unitsCorrespond
    · simpa only [P93RingChainDescriptorAssignment.descriptor,
        canonicalEvidence_toAuthority_descriptor] using
          congrArg P93CanonicalSourceProgram.P93CanonicalDescriptor.toRingChain descriptorsEq

theorem coupledMultiplicativeSymmetryComplete_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (correspondences : List P93RingChainComponentCorrespondence)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (complete : P93CanonicalMultiplicativeSymmetryComplete source components
      correspondences assignments ownerships) :
    P93RingChainMultiplicativeSymmetryComplete source components correspondences
      (coupledAssignments program source assignments allValid) ownerships := by
  rcases complete with
    ⟨componentsValid, ownershipsComplete, correspondenceKeys,
      correspondencesValid, correspondenceCoverage⟩
  refine ⟨componentsValid,
    coupledAssignmentOwnershipsComplete_of_canonical program source components assignments
      ownerships allValid ownershipsComplete,
    correspondenceKeys, ?_, correspondenceCoverage⟩
  intro correspondence correspondenceMem
  rcases correspondencesValid correspondence correspondenceMem with
    ⟨correspondenceValid, stereoCorrespond⟩
  exact ⟨
    coupledComponentCorrespondenceValidFor_of_canonical program source components assignments
      allValid ownerships correspondence correspondenceValid,
    coupledAssignmentsStereoCorrespond_of_canonical program source assignments allValid
      ownerships correspondence.leftIndex correspondence.rightIndex correspondence
      stereoCorrespond⟩

theorem coupledOwnedDescriptorMismatch_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (mismatch : P93CanonicalOwnedDescriptorMismatch assignments ownerships) :
    P93RingChainOwnedDescriptorMismatch
      (coupledAssignments program source assignments allValid) ownerships := by
  rcases mismatch with
    ⟨leftOwnership, leftOwnershipMem, rightOwnership, rightOwnershipMem,
      componentNe, leftEvidence, rightEvidence, leftAtIndex, rightAtIndex,
      descriptorNe⟩
  rcases coupledAssignments_get?_of_canonical program source assignments allValid
    leftAtIndex with ⟨leftValid, leftAuthorityAtIndex⟩
  rcases coupledAssignments_get?_of_canonical program source assignments allValid
    rightAtIndex with ⟨rightValid, rightAuthorityAtIndex⟩
  refine ⟨leftOwnership, leftOwnershipMem, rightOwnership, rightOwnershipMem,
    componentNe,
    { evidence := P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
        program source leftEvidence leftValid },
    { evidence := P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
        program source rightEvidence rightValid },
    leftAuthorityAtIndex, rightAuthorityAtIndex, ?_⟩
  intro descriptorsEq
  apply descriptorNe
  simpa only [P93RingChainDescriptorAssignment.descriptor,
    canonicalEvidence_toAuthority_descriptor] using descriptorsEq

theorem coupledMultiplicativeRejectionEvidence_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership)
    (rejected : P93CanonicalMultiplicativeRejectionEvidence source components
      assignments ownerships) :
    P93RingChainMultiplicativeRejectionEvidence source components
      (coupledAssignments program source assignments allValid) ownerships := by
  exact
    { componentsValid := rejected.componentsValid
      ownershipsComplete := coupledAssignmentOwnershipsComplete_of_canonical
        program source components assignments ownerships allValid rejected.ownershipsComplete
      descriptorMismatch := coupledOwnedDescriptorMismatch_of_canonical
        program source assignments allValid ownerships rejected.descriptorMismatch
      componentNonisomorphism := rejected.componentNonisomorphism }

theorem coupledMultiplicativeDecisionValid_of_canonical
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (components : List P93RingChainRepeatedComponent)
    (correspondences : List P93RingChainComponentCorrespondence)
    (assignments : List P93CanonicalReviewedDescriptorEvidence)
    (allValid : ∀ evidence ∈ assignments, evidence.ValidFor source)
    (ownerships : List P93RingChainAssignmentOwnership) (selected : Bool)
    (decision : P93CanonicalMultiplicativeDecisionValid source components correspondences
      assignments ownerships selected) :
    P93RingChainMultiplicativeDecisionValid source components correspondences
      (coupledAssignments program source assignments allValid) ownerships selected := by
  cases decision with
  | selected symmetryComplete =>
      exact .selected (coupledMultiplicativeSymmetryComplete_of_canonical program source
        components correspondences assignments allValid ownerships symmetryComplete)
  | rejected evidence =>
      exact .rejected (coupledMultiplicativeRejectionEvidence_of_canonical program source
        components assignments allValid ownerships evidence)

/-! The four acyclic reviewed-evidence constructors reuse the same production theorem at the
coupled claim scope.  The claim hypothesis is an inclusion, because the enclosing coupled entry
also contains the other reviewed assignments. -/

theorem coupledAcyclicCenterEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (payload : P93AcyclicClausePayload .singleAcyclicCenter)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (valid : (P93CanonicalReviewedDescriptorEvidence.acyclicCenter payload).ValidFor
      entry.source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority program
        entry.source (.acyclicCenter payload) valid) := by
  cases payload
  rcases valid with ⟨envelope, intrinsic⟩
  simpa only [P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority,
    P93RingChainReviewedDescriptorEvidenceSourceCore] using
      program.acyclicObservation_productionJudgesAt entryMem .coupled familyEq _ claims intrinsic

theorem coupledAcyclicDoubleBondEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (payload : P93AcyclicClausePayload .doubleBondEZCisTrans)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (valid : (P93CanonicalReviewedDescriptorEvidence.acyclicDoubleBond payload).ValidFor
      entry.source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority program
        entry.source (.acyclicDoubleBond payload) valid) := by
  cases payload
  rcases valid with ⟨envelope, intrinsic⟩
  simpa only [P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority,
    P93RingChainReviewedDescriptorEvidenceSourceCore] using
      program.acyclicObservation_productionJudgesAt entryMem .coupled familyEq _ claims intrinsic

theorem coupledAcyclicEvenCumuleneEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (payload : P93AcyclicClausePayload .evenCumulenes)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (valid : (P93CanonicalReviewedDescriptorEvidence.acyclicEvenCumulene payload).ValidFor
      entry.source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority program
        entry.source (.acyclicEvenCumulene payload) valid) := by
  cases payload
  rcases valid with ⟨envelope, intrinsic⟩
  simpa only [P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority,
    P93RingChainReviewedDescriptorEvidenceSourceCore] using
      program.acyclicObservation_productionJudgesAt entryMem .coupled familyEq _ claims intrinsic

theorem coupledAcyclicOddCumuleneEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (payload : P93AcyclicClausePayload .oddCumulenes)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (valid : (P93CanonicalReviewedDescriptorEvidence.acyclicOddCumulene payload).ValidFor
      entry.source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority program
        entry.source (.acyclicOddCumulene payload) valid) := by
  cases payload
  rcases valid with ⟨envelope, intrinsic⟩
  simpa only [P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority,
    P93RingChainReviewedDescriptorEvidenceSourceCore] using
      program.acyclicObservation_productionJudgesAt entryMem .coupled familyEq _ claims intrinsic

theorem coupledMonocyclicAbsoluteEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (payload : P93MonocyclicClausePayload .monocyclicAbsoluteCenters)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.monocyclicAbsoluteCenter payload ∈
      coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.monocyclicAbsoluteCenter payload).ValidFor
      source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.monocyclicAbsoluteCenter payload) valid) := by
  have innerValid : (P93ClausePayloadData.monocyclic payload).ValidFor source := by
    simpa [P93ClausePayloadData.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.ValidFor] using valid
  have ctx : IncludedPayloadContext program .coupled source (.monocyclic payload) :=
    IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
      (.monocyclicAbsoluteCenter payload) evidenceMem rfl rfl innerValid
  have judged := program.monocyclicAbsoluteAuthority_judged_of_included
    .coupled source payload ctx
  cases payload
  exact judged.1

theorem coupledMonocyclicAchiralEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (payload : P93MonocyclicClausePayload .monocyclicAchiralCenters)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.monocyclicAchiralCenter payload ∈
      coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.monocyclicAchiralCenter payload).ValidFor
      source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.monocyclicAchiralCenter payload) valid) := by
  have innerValid : (P93ClausePayloadData.monocyclic payload).ValidFor source := by
    simpa [P93ClausePayloadData.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.ValidFor] using valid
  have ctx : IncludedPayloadContext program .coupled source (.monocyclic payload) :=
    IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
      (.monocyclicAchiralCenter payload) evidenceMem rfl rfl innerValid
  have judged := program.monocyclicAchiralAuthority_judged_of_included
    .coupled source payload ctx
  cases payload
  exact judged.1

theorem coupledMonocyclicDoubleBondEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (payload : P93MonocyclicClausePayload .cyclicDoubleBonds)
    (citation : P93AuthorityCitationToken) (descriptor : BlueBookP93.Acyclic.Descriptor)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.monocyclicDoubleBond
      payload citation descriptor ∈ coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.monocyclicDoubleBond
      payload citation descriptor).ValidFor source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.monocyclicDoubleBond payload citation descriptor) valid) := by
  have innerValid : (P93ClausePayloadData.monocyclic payload).ValidFor source :=
    ⟨valid.1, valid.2.1⟩
  have ctx : IncludedPayloadContext program .coupled source (.monocyclic payload) :=
    IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
      (.monocyclicDoubleBond payload citation descriptor) evidenceMem rfl rfl innerValid
  have judged := program.monocyclicDoubleBondAuthority_judged_of_included
    .coupled source payload ctx
  cases payload
  exact ⟨judged, valid.2.2.2, valid.2.2.1⟩

theorem coupledFusedCIPEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (observation : P93CanonicalFusedCIPObservation)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.fusedCIP observation ∈
      coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.fusedCIP observation).ValidFor source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.fusedCIP observation) valid) := by
  have innerValid : (P93ClausePayloadData.fusedCyclophane
      (.fusedCIP observation)).ValidFor source := by
    simpa [P93ClausePayloadData.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.ValidFor] using valid
  have ctx : IncludedPayloadContext program .coupled source
      (.fusedCyclophane (.fusedCIP observation)) :=
    IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
      (.fusedCIP observation) evidenceMem rfl rfl innerValid
  exact program.fusedCIPAuthority_sourceCore_of_included .coupled source observation ctx

theorem coupledSpiroPolyhedralEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (payload : P93SpiroNontetrahedralPayload)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.spiroPolyhedral payload ∈
      coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.spiroPolyhedral payload).ValidFor source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.spiroPolyhedral payload) valid) := by
  have innerValid : (P93ClausePayloadData.spiroNontetrahedral payload).ValidFor source := by
    simpa [P93ClausePayloadData.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.ValidFor] using valid
  have ctx : IncludedPayloadContext program .coupled source
      (.spiroNontetrahedral payload) :=
    IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
      (.spiroPolyhedral payload) evidenceMem rfl rfl innerValid
  exact program.spiroNontetrahedralAuthority_sourceCore_of_included
    .coupled source payload ctx

theorem coupledCyclophanePlaneEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (payload : P93FusedCyclophaneClausePayload .cyclophanePlanes)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.cyclophanePlane payload ∈
      coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.cyclophanePlane payload).ValidFor source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.cyclophanePlane payload) valid) := by
  have innerValid : (P93ClausePayloadData.fusedCyclophane payload).ValidFor source := by
    simpa [P93ClausePayloadData.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.ValidFor] using valid
  have ctx : IncludedPayloadContext program .coupled source
      (.fusedCyclophane payload) :=
    IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
      (.cyclophanePlane payload) evidenceMem rfl rfl innerValid
  cases payload with
  | cyclophanePlanes printed executable =>
      exact program.cyclophanePlanesAuthority_sourceCore_of_included .coupled source
        printed executable ctx

theorem coupledCyclophaneDoubleBondEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (payload : P93FusedCyclophaneClausePayload .cyclophaneDoubleBonds)
    (descriptor : BlueBookP93.Acyclic.Descriptor)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.cyclophaneDoubleBond
      payload descriptor ∈ coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.cyclophaneDoubleBond
      payload descriptor).ValidFor source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.cyclophaneDoubleBond payload descriptor) valid) := by
  cases payload with
  | cyclophaneDoubleBonds system unit citation ring phaneRing geometry carbonContext context
      descriptor? =>
      have innerValid : (P93ClausePayloadData.fusedCyclophane
          (.cyclophaneDoubleBonds system unit citation ring phaneRing geometry carbonContext context
            descriptor?)).ValidFor source := ⟨valid.1, valid.2.1⟩
      have ctx : IncludedPayloadContext program .coupled source
          (.fusedCyclophane
            (.cyclophaneDoubleBonds system unit citation ring phaneRing geometry carbonContext context
              descriptor?)) :=
        IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
          (.cyclophaneDoubleBond
            (.cyclophaneDoubleBonds system unit citation ring phaneRing geometry carbonContext context
              descriptor?) descriptor) evidenceMem rfl rfl innerValid
      exact ⟨program.cyclophaneDoubleBondsAuthority_sourceCore_of_included .coupled source
        system unit citation ring phaneRing geometry carbonContext context descriptor? ctx,
        valid.2.2⟩

theorem coupledCyclophaneCIPEvidence_sourceCore
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (coupledPayload : P93CoupledClausePayload)
    (outerCtx : PayloadContext program .coupled source (.coupled coupledPayload))
    (payload : P93FusedCyclophaneClausePayload .cyclophaneCenters)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.cyclophaneCenterCIP payload ∈
      coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.cyclophaneCenterCIP payload).ValidFor
      source) :
    P93RingChainReviewedDescriptorEvidenceSourceCore source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program source
        (.cyclophaneCenterCIP payload) valid) := by
  cases payload with
  | cyclophaneCenters system unit citation specification =>
      cases specification with
      | cip context kind descriptor =>
          have innerValid : (P93ClausePayloadData.fusedCyclophane
              (.cyclophaneCenters system unit citation (.cip context kind descriptor))).ValidFor
              source := ⟨valid.1, valid.2.1⟩
          have ctx : IncludedPayloadContext program .coupled source
              (.fusedCyclophane
                (.cyclophaneCenters system unit citation (.cip context kind descriptor))) :=
            IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
              (.cyclophaneCenterCIP
                (.cyclophaneCenters system unit citation (.cip context kind descriptor)))
              evidenceMem rfl rfl innerValid
          exact ⟨program.cyclophaneCentersCIPAuthority_sourceCore_of_included .coupled source
            system unit citation context kind descriptor ctx, rfl⟩
      | relativeRCT candidates selected referenceSide assignments =>
          rcases valid.2.2 with ⟨context, kind, descriptor, impossible⟩
          cases impossible

theorem coupledCyclophaneRelativeEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (coupledPayload : P93CoupledClausePayload)
    (auditEq : entry.observation.auditClaims = coupledPayload.toClaims)
    (outerCtx : PayloadContext program .coupled entry.source (.coupled coupledPayload))
    (payload : P93FusedCyclophaneClausePayload .cyclophaneCenters)
    (assignment : P93CyclophaneRCTLocatedAssignment)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.cyclophaneCenterRelative
      payload assignment ∈ coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.cyclophaneCenterRelative
      payload assignment).ValidFor entry.source)
    (allValid : ∀ evidence ∈ coupledPayload.assignments, evidence.ValidFor entry.source)
    (unionClosed : P93CoupledAssignmentsUnionClosed coupledPayload.assignments) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program entry.source
        (.cyclophaneCenterRelative payload assignment) valid) := by
  cases payload with
  | cyclophaneCenters system unit citation specification =>
      cases specification with
      | cip context kind descriptor =>
          rcases valid.2.2 with ⟨candidates, selected, referenceSide, assignments,
            impossible, _assignmentMem⟩
          cases impossible
      | relativeRCT candidates selected referenceSide assignments =>
          have innerValid : (P93ClausePayloadData.fusedCyclophane
              (.cyclophaneCenters system unit citation
                (.relativeRCT candidates selected referenceSide assignments))).ValidFor
              entry.source := ⟨valid.1, valid.2.1⟩
          have ctx : IncludedPayloadContext program .coupled entry.source
              (.fusedCyclophane
                (.cyclophaneCenters system unit citation
                  (.relativeRCT candidates selected referenceSide assignments))) :=
            IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
              (.cyclophaneCenterRelative
                (.cyclophaneCenters system unit citation
                  (.relativeRCT candidates selected referenceSide assignments)) assignment)
              evidenceMem rfl rfl innerValid
          have complete := program.coupledCyclophaneRelative_complete entryMem familyEq
            coupledPayload auditEq system unit citation candidates selected referenceSide
            assignments assignment evidenceMem allValid unionClosed
          refine ⟨program.cyclophaneCentersRelativeAuthority_sourceCore_of_included
            .coupled entry.source system unit citation candidates selected referenceSide
            assignments ctx complete, ?_⟩
          exact valid.2.2

theorem coupledRingAssemblyAxisEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (coupledPayload : P93CoupledClausePayload)
    (auditEq : entry.observation.auditClaims = coupledPayload.toClaims)
    (outerCtx : PayloadContext program .coupled entry.source (.coupled coupledPayload))
    (payload : P93RingAssemblyClausePayload .axes)
    (assignment : P93RingAssemblyAxisAssignment)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.ringAssemblyAxis
      payload assignment ∈ coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.ringAssemblyAxis
      payload assignment).ValidFor entry.source)
    (unionClosed : P93CoupledAssignmentsUnionClosed coupledPayload.assignments) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program entry.source
        (.ringAssemblyAxis payload assignment) valid) := by
  cases payload with
  | axes printed executable =>
      have innerValid : (P93ClausePayloadData.ringAssembly
          (.axes printed executable)).ValidFor entry.source :=
        ⟨valid.1, valid.2.1⟩
      have ctx : IncludedPayloadContext program .coupled entry.source
          (.ringAssembly (.axes printed executable)) :=
        IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
          (.ringAssemblyAxis (.axes printed executable) assignment)
          evidenceMem rfl rfl innerValid
      have completePrinted := program.coupledRingAssemblyAxis_complete entryMem familyEq
        coupledPayload auditEq printed executable assignment
        evidenceMem unionClosed
      have complete : ∀ junction,
          program.HasClaim .coupled entry.source
              (.ringAssembly (.axisEligible printed.assembly junction)) →
            ∃ carried ∈ executable.assignments, carried.junction = junction := by
        intro junction eligible
        rcases completePrinted junction eligible with
          ⟨printedAssignment, printedMem, junctionEq⟩
        rcases valid.2.1 with ⟨_printedValid,
          ⟨_spatialEq, _normalizationAgreement, _normalizationExact, agreement,
            _assignmentsValid⟩⟩
        rw [agreement] at printedMem
        rcases List.mem_map.mp printedMem with ⟨carried, carriedMem, carriedEq⟩
        refine ⟨carried, carriedMem, ?_⟩
        have junctionAgreement : carried.junction = printedAssignment.junction := by
          simpa [P93RingAssemblyAxisAssignment.toPrinted] using
            congrArg P93CanonicalRingAssemblyPrintedAxisAssignment.junction carriedEq
        exact junctionAgreement.trans junctionEq
      exact ⟨program.ringAssemblyAxesAuthority_sourceCore_of_included .coupled entry.source
        printed executable ctx complete, valid.2.2⟩

theorem coupledRingAssemblyCenterEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (coupledPayload : P93CoupledClausePayload)
    (auditEq : entry.observation.auditClaims = coupledPayload.toClaims)
    (outerCtx : PayloadContext program .coupled entry.source (.coupled coupledPayload))
    (payload : P93RingAssemblyClausePayload .centers)
    (assignment : P93RingAssemblyCenterAssignment)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.ringAssemblyCenter
      payload assignment ∈ coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.ringAssemblyCenter
      payload assignment).ValidFor entry.source)
    (unionClosed : P93CoupledAssignmentsUnionClosed coupledPayload.assignments) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program entry.source
        (.ringAssemblyCenter payload assignment) valid) := by
  cases payload with
  | centers assembly assignments =>
      have innerValid : (P93ClausePayloadData.ringAssembly
          (.centers assembly assignments)).ValidFor entry.source := ⟨valid.1, valid.2.1⟩
      have ctx : IncludedPayloadContext program .coupled entry.source
          (.ringAssembly (.centers assembly assignments)) :=
        IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
          (.ringAssemblyCenter (.centers assembly assignments) assignment)
          evidenceMem rfl rfl innerValid
      have complete := program.coupledRingAssemblyCenter_complete entryMem familyEq
        coupledPayload auditEq assembly assignments assignment evidenceMem unionClosed
      exact ⟨program.ringAssemblyCentersAuthority_sourceCore_of_included .coupled entry.source
        assembly assignments ctx complete, valid.2.2⟩

theorem coupledRingAssemblyDoubleBondEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (coupledPayload : P93CoupledClausePayload)
    (auditEq : entry.observation.auditClaims = coupledPayload.toClaims)
    (outerCtx : PayloadContext program .coupled entry.source (.coupled coupledPayload))
    (payload : P93RingAssemblyClausePayload .doubleBonds)
    (assignment : P93RingAssemblyDoubleBondAssignment)
    (evidenceMem : P93CanonicalReviewedDescriptorEvidence.ringAssemblyDoubleBond
      payload assignment ∈ coupledPayload.assignments)
    (valid : (P93CanonicalReviewedDescriptorEvidence.ringAssemblyDoubleBond
      payload assignment).ValidFor entry.source)
    (unionClosed : P93CoupledAssignmentsUnionClosed coupledPayload.assignments) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program entry.source
        (.ringAssemblyDoubleBond payload assignment) valid) := by
  cases payload with
  | doubleBonds assembly assignments =>
      have innerValid : (P93ClausePayloadData.ringAssembly
          (.doubleBonds assembly assignments)).ValidFor entry.source := ⟨valid.1, valid.2.1⟩
      have ctx : IncludedPayloadContext program .coupled entry.source
          (.ringAssembly (.doubleBonds assembly assignments)) :=
        IncludedPayloadContext.ofCoupledEvidence coupledPayload outerCtx
          (.ringAssemblyDoubleBond (.doubleBonds assembly assignments) assignment)
          evidenceMem rfl rfl innerValid
      have complete := program.coupledRingAssemblyDoubleBond_complete entryMem familyEq
        coupledPayload auditEq assembly assignments assignment evidenceMem unionClosed
      exact ⟨program.ringAssemblyDoubleBondsAuthority_sourceCore_of_included
        .coupled entry.source assembly assignments ctx complete, valid.2.2⟩

/-- Every retained reviewed-evidence constructor compiles to its exact legacy source core.
The four non-monotone constructors use `P93CoupledAssignmentsUnionClosed`; the other twelve
transport monotonically from their complete nested payload. -/
theorem coupledNestedEvidence_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (coupledPayload : P93CoupledClausePayload)
    (auditEq : entry.observation.auditClaims = coupledPayload.toClaims)
    (outerCtx : PayloadContext program .coupled entry.source (.coupled coupledPayload))
    (intrinsic : coupledPayload.Intrinsic entry.source)
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (evidenceMem : evidence ∈ coupledPayload.assignments) :
    P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
      (P93CanonicalReviewedDescriptorEvidence.toAuthority program entry.source evidence
        (intrinsic.2.2.2.2.1 evidence evidenceMem)) := by
  have claims : ∀ claim ∈ evidence.upstreamClaims,
      claim ∈ entry.observation.auditClaims := by
    intro claim claimMem
    rw [auditEq]
    exact nestedClaim_mem_coupledClaims coupledPayload evidenceMem claimMem
  have valid := intrinsic.2.2.2.2.1 evidence evidenceMem
  have unionClosed := intrinsic.2.2.2.2.2.1
  cases evidence with
  | acyclicCenter payload =>
      exact program.coupledAcyclicCenterEvidence_sourceCore entryMem familyEq payload
        claims valid
  | acyclicDoubleBond payload =>
      exact program.coupledAcyclicDoubleBondEvidence_sourceCore entryMem familyEq payload
        claims valid
  | acyclicEvenCumulene payload =>
      exact program.coupledAcyclicEvenCumuleneEvidence_sourceCore entryMem familyEq payload
        claims valid
  | acyclicOddCumulene payload =>
      exact program.coupledAcyclicOddCumuleneEvidence_sourceCore entryMem familyEq payload
        claims valid
  | monocyclicAbsoluteCenter payload =>
      exact program.coupledMonocyclicAbsoluteEvidence_sourceCore entry.source coupledPayload
        outerCtx payload evidenceMem valid
  | monocyclicAchiralCenter payload =>
      exact program.coupledMonocyclicAchiralEvidence_sourceCore entry.source coupledPayload
        outerCtx payload evidenceMem valid
  | monocyclicDoubleBond payload citation descriptor =>
      exact program.coupledMonocyclicDoubleBondEvidence_sourceCore entry.source coupledPayload
        outerCtx payload citation descriptor evidenceMem valid
  | fusedCIP observation =>
      exact program.coupledFusedCIPEvidence_sourceCore entry.source coupledPayload outerCtx
        observation evidenceMem valid
  | cyclophanePlane payload =>
      exact program.coupledCyclophanePlaneEvidence_sourceCore entry.source coupledPayload
        outerCtx payload evidenceMem valid
  | cyclophaneCenterCIP payload =>
      exact program.coupledCyclophaneCIPEvidence_sourceCore entry.source coupledPayload
        outerCtx payload evidenceMem valid
  | cyclophaneCenterRelative payload assignment =>
      exact program.coupledCyclophaneRelativeEvidence_sourceCore entryMem familyEq
        coupledPayload auditEq outerCtx payload assignment evidenceMem valid
        intrinsic.2.2.2.2.1 unionClosed
  | cyclophaneDoubleBond payload descriptor =>
      exact program.coupledCyclophaneDoubleBondEvidence_sourceCore entry.source coupledPayload
        outerCtx payload descriptor evidenceMem valid
  | spiroPolyhedral payload =>
      exact program.coupledSpiroPolyhedralEvidence_sourceCore entry.source coupledPayload
        outerCtx payload evidenceMem valid
  | ringAssemblyAxis payload assignment =>
      exact program.coupledRingAssemblyAxisEvidence_sourceCore entryMem familyEq coupledPayload
        auditEq outerCtx payload assignment evidenceMem valid unionClosed
  | ringAssemblyCenter payload assignment =>
      exact program.coupledRingAssemblyCenterEvidence_sourceCore entryMem familyEq coupledPayload
        auditEq outerCtx payload assignment evidenceMem valid unionClosed
  | ringAssemblyDoubleBond payload assignment =>
      exact program.coupledRingAssemblyDoubleBondEvidence_sourceCore entryMem familyEq
        coupledPayload auditEq outerCtx payload assignment evidenceMem valid unionClosed

def coupledObservation
    (program : P93CanonicalSourceProgram) (source : AuthoritativeChemicalInput)
    (payload : P93CoupledClausePayload) (intrinsic : payload.Intrinsic source) :
    P93CoupledRingChainAuthorityObservation program.compiledPolicies.cyclic.coupledRingChain :=
  { reviewedBaseName := payload.reviewedBaseName
    baseNameCertificate := payload.baseNameCertificate
    annotatedBaseName := payload.reviewedBaseName
    assignments := coupledAssignments program source payload.assignments
      intrinsic.2.2.2.2.1
    multiplicativeSelected := payload.multiplicativeSelected
    repeatedComponents := payload.repeatedComponents
    componentCorrespondences := payload.componentCorrespondences
    assignmentOwnerships := payload.assignmentOwnerships }

theorem coupledObservation_sourceCore
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (payload : P93CoupledClausePayload)
    (auditEq : entry.observation.auditClaims = payload.toClaims)
    (noCoupledUpstream : ∀ evidence ∈ payload.assignments, ∀ claim,
      P93SourceClaim.coupled claim ∉ evidence.upstreamClaims)
    (contains : ∀ evidence ∈ payload.assignments,
      P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.ContainsCoupledEvidence
        entry payload.reviewedBaseName evidence)
    (intrinsic : payload.Intrinsic entry.source)
    (nestedSourceCore : ∀ evidence (evidenceMem : evidence ∈ payload.assignments),
      P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
        (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
          program entry.source evidence (intrinsic.2.2.2.2.1 evidence evidenceMem))) :
    P93CoupledRingChainObservationSourceCore program.coupledPolicy entry.source
      (program.coupledObservation entry.source payload intrinsic) := by
  rcases intrinsic with
    ⟨certificateValid, assignmentsNonempty, identitiesNodup, citationsNodup, allValid,
      unionClosed, multiplicativeDecision⟩
  refine ⟨certificateValid.1, certificateValid, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨payload.baseNameCertificate, ?_⟩
    simpa [coupledPolicy, familyEq] using program.hasClaim_of_mem entryMem
      (show P93SourceClaim.coupled
          (.baseName payload.reviewedBaseName payload.baseNameCertificate) ∈
        entry.observation.auditClaims by
          rw [auditEq]
          simp [P93CoupledClausePayload.toClaims])
  · intro assignmentsEq
    apply assignmentsNonempty
    have assignmentsEq' : coupledAssignments program entry.source payload.assignments
        allValid = [] := by
      simpa only [coupledObservation] using assignmentsEq
    apply List.length_eq_zero_iff.1
    rw [← coupledAssignments_length program entry.source payload.assignments allValid,
      assignmentsEq']
    rfl
  · change (List.map (fun assignment => assignment.unit.physicalIdentity)
      (coupledAssignments program entry.source payload.assignments allValid)).Nodup
    rw [coupledAssignments_map_physicalIdentity]
    exact identitiesNodup
  · change (List.filterMap (fun assignment => assignment.evidence.citation?)
      (coupledAssignments program entry.source payload.assignments allValid)).Nodup
    rw [coupledAssignments_filterMap_citation]
    exact citationsNodup
  · intro assignment assignmentMem
    rw [coupledObservation, coupledAssignments_mem_iff] at assignmentMem
    rcases assignmentMem with ⟨evidence, evidenceMem, rfl⟩
    refine ⟨nestedSourceCore evidence evidenceMem, ?_, ?_, ?_⟩
    · change program.coupledPolicy.StereogenicUnitEligible entry.source
        payload.reviewedBaseName
        (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
          program entry.source evidence (allValid evidence evidenceMem)).unit
      rw [canonicalEvidence_toAuthority_unit]
      change program.HasClaim .coupled entry.source
        (.coupled (.eligibleUnit payload.reviewedBaseName evidence.unit))
      simpa [coupledObservation, coupledPolicy, familyEq] using
        program.hasClaim_of_mem entryMem
          (show P93SourceClaim.coupled
              (.eligibleUnit payload.reviewedBaseName evidence.unit) ∈
              entry.observation.auditClaims by
            rw [auditEq]
            simp only [P93CoupledClausePayload.toClaims, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false, List.mem_flatMap]
            apply Or.inl
            apply Or.inr
            exact ⟨evidence, evidenceMem, Or.inl (Or.inr (Or.inl rfl))⟩)
    · change program.coupledPolicy.EvidenceBelongsToName entry.source
        payload.reviewedBaseName
        (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
          program entry.source evidence (allValid evidence evidenceMem))
      refine ⟨evidence, allValid evidence evidenceMem, ?_, rfl⟩
      exact ⟨entry, entryMem, rfl, contains evidence evidenceMem⟩
    · rw [canonicalEvidence_toAuthority_citation]
      cases citationEq : evidence.citation? with
      | none => trivial
      | some citation =>
          have citationMem : P93SourceClaim.coupled
              (.citation payload.reviewedBaseName citation evidence.unit) ∈
              entry.observation.auditClaims := by
            rw [auditEq]
            simp only [P93CoupledClausePayload.toClaims, List.mem_append, List.mem_cons,
              List.not_mem_nil, or_false, List.mem_flatMap, List.mem_map]
            apply Or.inl
            apply Or.inr
            refine ⟨evidence, evidenceMem, Or.inr ?_⟩
            exact ⟨citation, by simp [citationEq], rfl⟩
          have citationEnvelope := entry.observation.validFor.1 _ citationMem
          refine ⟨?_, ?_⟩
          · simpa [P93SourceClaim.SourceEnvelope, P93CoupledClaim.SourceEnvelope] using
              citationEnvelope.2.1
          · change program.coupledPolicy.CitationConformsToBaseNumbering entry.source
                payload.reviewedBaseName citation
                (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
                  program entry.source evidence (allValid evidence evidenceMem)).unit
            rw [canonicalEvidence_toAuthority_unit]
            change program.HasClaim .coupled entry.source
              (.coupled (.citation payload.reviewedBaseName citation evidence.unit))
            simpa [coupledObservation, coupledPolicy, familyEq,
              canonicalEvidence_toAuthority_unit] using
              program.hasClaim_of_mem entryMem citationMem
  · intro unit eligible
    simp only [coupledObservation] at eligible ⊢
    have eligibleMem := (program.hasClaim_iff entryMem
      (.coupled (.eligibleUnit payload.reviewedBaseName unit))).1
        (by simpa [coupledPolicy, familyEq] using eligible)
    rw [auditEq] at eligibleMem
    simp only [P93CoupledClausePayload.toClaims, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_flatMap] at eligibleMem
    simp at eligibleMem
    rcases eligibleMem with ⟨evidence, evidenceMem, unitOrUpstream⟩
    have unitEq : unit = evidence.unit := unitOrUpstream.resolve_left
      (noCoupledUpstream evidence evidenceMem _)
    let authority : P93RingChainDescriptorAssignment program.coupledDescriptorPolicies :=
      { evidence :=
          P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
            program entry.source evidence (allValid evidence evidenceMem) }
    refine ⟨authority, ?_, ?_⟩
    · exact (coupledAssignments_mem_iff program entry.source payload.assignments allValid
        authority).2 ⟨evidence, evidenceMem, rfl⟩
    · change
        (P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
          program entry.source evidence (allValid evidence evidenceMem)).unit = unit
      rw [canonicalEvidence_toAuthority_unit]
      exact unitEq.symm
  · change payload.multiplicativeSelected = true ↔
      program.HasClaim .coupled entry.source
        (.coupled (.multiplicativeDecision payload.reviewedBaseName true))
    constructor
    · intro selected
      simpa [coupledObservation, coupledPolicy, familyEq] using
        program.hasClaim_of_mem entryMem
        (show P93SourceClaim.coupled
            (.multiplicativeDecision payload.reviewedBaseName true) ∈
            entry.observation.auditClaims by
          rw [auditEq]
          simp [P93CoupledClausePayload.toClaims, selected])
    · intro selectedClaim
      have selectedMem := (program.hasClaim_iff entryMem
        (.coupled (.multiplicativeDecision payload.reviewedBaseName true))).1
          (by simpa [coupledObservation, coupledPolicy, familyEq] using selectedClaim)
      rw [auditEq] at selectedMem
      simp [P93CoupledClausePayload.toClaims] at selectedMem
      rcases selectedMem with upstream | selected
      · rcases upstream with ⟨evidence, evidenceMem, claimMem⟩
        exact False.elim (noCoupledUpstream evidence evidenceMem _ claimMem)
      · exact selected
  · change program.HasClaim .coupled entry.source
      (.coupled (.repeatedComponents payload.reviewedBaseName payload.repeatedComponents))
    simpa [coupledObservation, coupledPolicy, familyEq] using
      program.hasClaim_of_mem entryMem
      (show P93SourceClaim.coupled
          (.repeatedComponents payload.reviewedBaseName payload.repeatedComponents) ∈
          entry.observation.auditClaims by
        rw [auditEq]
        simp [P93CoupledClausePayload.toClaims])
  · exact coupledMultiplicativeDecisionValid_of_canonical program entry.source
      payload.repeatedComponents payload.componentCorrespondences payload.assignments allValid
      payload.assignmentOwnerships payload.multiplicativeSelected multiplicativeDecision

theorem coupledObservation_productionJudges
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .coupled)
    (payload : P93CoupledClausePayload)
    (auditEq : entry.observation.auditClaims = payload.toClaims)
    (noCoupledUpstream : ∀ evidence ∈ payload.assignments, ∀ claim,
      P93SourceClaim.coupled claim ∉ evidence.upstreamClaims)
    (contains : ∀ evidence ∈ payload.assignments,
      P93CanonicalClauseObservationEntry.ContainsCoupledEvidence
        entry payload.reviewedBaseName evidence)
    (intrinsic : payload.Intrinsic entry.source)
    (nestedSourceCore : ∀ evidence (evidenceMem : evidence ∈ payload.assignments),
      P93RingChainReviewedDescriptorEvidenceSourceCore entry.source
        (P93CanonicalReviewedDescriptorEvidence.toAuthority
          program entry.source evidence (intrinsic.2.2.2.2.1 evidence evidenceMem))) :
    Remaining71P93CoupledRingChainAuthorityRow.configurations.ProductionJudges
      program.coupledPolicy entry.source
      (program.coupledObservation entry.source payload intrinsic) :=
  program.coupledObservation_sourceCore entryMem familyEq payload auditEq noCoupledUpstream
    contains intrinsic nestedSourceCore

theorem entry_coupled_productionJudges
    (program : P93CanonicalSourceProgram)
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    (clauseEq : entry.clause = .coupledRingChain .configurations) :
    ∃ observation :
        (Remaining71P93CoupledRingChainAuthorityRow.configurations.reference
          program.coupledPolicy).Observation,
      Remaining71P93CoupledRingChainAuthorityRow.configurations.ProductionJudges
        program.coupledPolicy entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | coupled payload =>
      have outerCtx : PayloadContext program .coupled source (.coupled payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      have intrinsic : payload.Intrinsic source := by
        simpa [P93ClausePayloadData.ValidFor, payloadEq] using sourceObservation.validFor.2
      have auditEq : sourceObservation.auditClaims = payload.toClaims := by
        rw [P93ClauseObservation.auditClaims, payloadEq]
        rfl
      refine ⟨program.coupledObservation source payload intrinsic,
        program.coupledObservation_productionJudges entryMem rfl payload auditEq ?_ ?_
          intrinsic ?_⟩
      · intro evidence _evidenceMem claim
        exact coupledEvidence_upstream_not_coupled evidence claim
      · intro evidence evidenceMem
        simp [P93CanonicalClauseObservationEntry.ContainsCoupledEvidence, payloadEq]
        exact evidenceMem
      · intro evidence evidenceMem
        exact program.coupledNestedEvidence_sourceCore entryMem rfl payload auditEq outerCtx
          intrinsic evidence evidenceMem

theorem entry_fullerene_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93FullereneAuthorityRow}
    (clauseEq : entry.clause = .fullerene row) :
    ∃ observation : (row.reference (program.fullerenePolicy .fullerene)
        program.relationalFullerenePolicy).Observation,
      row.ProductionJudges (program.fullerenePolicy .fullerene)
        program.relationalFullerenePolicy entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | fullerene payload =>
      have ctx : PayloadContext program .fullerene source (.fullerene payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      exact ⟨fullereneAuthority program .fullerene payload,
        fullereneAuthority_productionJudges program .fullerene source payload ctx⟩

theorem entry_monocyclic_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93MonocyclicAuthorityRow}
    (clauseEq : entry.clause = .monocyclic row) :
    ∃ observation : (row.reference (program.monocyclicPolicy .monocyclic)).Observation,
      row.ProductionJudges (program.monocyclicPolicy .monocyclic) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | monocyclic payload =>
      have ctx : PayloadContext program .monocyclic source (.monocyclic payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      exact ⟨monocyclicAuthority program .monocyclic payload,
        monocyclicAuthority_productionJudges program .monocyclic source payload ctx⟩

theorem entry_vonBaeyer_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93VonBaeyerAuthorityRow}
    (clauseEq : entry.clause = .vonBaeyer row) :
    ∃ observation : (row.reference (program.vonBaeyerPolicy .vonBaeyer)).Observation,
      row.ProductionJudges (program.vonBaeyerPolicy .vonBaeyer) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | vonBaeyer payload =>
      have ctx : PayloadContext program .vonBaeyer source (.vonBaeyer payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      exact ⟨vonBaeyerAuthority program .vonBaeyer payload,
        vonBaeyerAuthority_productionJudges program .vonBaeyer source payload ctx⟩

theorem entry_ringAssembly_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93RingAssemblyAuthorityRow}
    (clauseEq : entry.clause = .ringAssembly row) :
    ∃ observation : (row.reference (program.ringAssemblyPolicy .ringAssembly)).Observation,
      row.ProductionJudges (program.ringAssemblyPolicy .ringAssembly) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | ringAssembly payload =>
      have ctx : PayloadContext program .ringAssembly source (.ringAssembly payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      exact ⟨ringAssemblyAuthority program .ringAssembly payload,
        ringAssemblyAuthority_productionJudges program .ringAssembly source payload ctx⟩

theorem entry_spiro_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93SpiroReadyAuthorityRow}
    (clauseEq : entry.clause = .spiro row) :
    ∃ observation : (row.reference (program.spiroPolicy .spiro)).Observation,
      row.ProductionJudges (program.spiroPolicy .spiro) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | spiro payload =>
      have ctx : PayloadContext program .spiro source (.spiro payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      exact ⟨spiroAuthority program .spiro payload,
        spiroAuthority_productionJudges_of_included program .spiro source payload
          ctx.toIncluded⟩

theorem entry_spiroNontetrahedral_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    (clauseEq : entry.clause = .spiroNontetrahedral) :
    ∃ observation :
        (Remaining71P93SpiroAuthorityRow.reference (program.spiroPolicy .spiro)
          .spiroNontetrahedralCenters).Observation,
      P93SpiroNontetrahedralSourceCore (program.spiroPolicy .spiro) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | spiroNontetrahedral payload =>
      have ctx : PayloadContext program .spiro source (.spiroNontetrahedral payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      exact ⟨spiroNontetrahedralAuthority program .spiro payload,
        spiroNontetrahedralAuthority_sourceCore_of_included program .spiro source payload
          ctx.toIncluded⟩

theorem entry_fusedCyclophane_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93FusedCyclophaneAuthorityRow}
    (clauseEq : entry.clause = .fusedCyclophane row) :
    ∃ observation :
        (row.reference (program.fusedPolicy .fused) (program.cyclophanePolicy .cyclophane)).Observation,
      row.ProductionJudges (program.fusedPolicy .fused) (program.cyclophanePolicy .cyclophane)
        entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | fusedCyclophane payload =>
      let scope := P93Clause.family (.fusedCyclophane row)
      have ctx : PayloadContext program scope source (.fusedCyclophane payload) := by
        simpa [payloadEq] using program.payloadContext_of_entry entryMem
      have judged := fusedCyclophaneAuthority_productionJudges program scope source payload ctx
      cases row <;> exact ⟨fusedCyclophaneAuthority program scope payload, judged⟩

/-- Exact dependent result of compiling any one admitted entry of the 56-row source program. -/
def EntryProductionWitness
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry) : Prop :=
  match entry.clause with
  | .fullerene row =>
      ∃ observation : (row.reference (program.fullerenePolicy .fullerene)
          program.relationalFullerenePolicy).Observation,
        row.ProductionJudges (program.fullerenePolicy .fullerene)
          program.relationalFullerenePolicy entry.source observation
  | .noncarbon row =>
      ∃ observation : (row.reference (program.noncarbonPolicy .noncarbon)).Observation,
        row.ProductionJudges (program.noncarbonPolicy .noncarbon) entry.source observation
  | .general row =>
      ∃ observation : (row.reference (program.generalPolicy .general)).Observation,
        row.ProductionJudges (program.generalPolicy .general) entry.source observation
  | .monocyclic row =>
      ∃ observation : (row.reference (program.monocyclicPolicy .monocyclic)).Observation,
        row.ProductionJudges (program.monocyclicPolicy .monocyclic) entry.source observation
  | .vonBaeyer row =>
      ∃ observation : (row.reference (program.vonBaeyerPolicy .vonBaeyer)).Observation,
        row.ProductionJudges (program.vonBaeyerPolicy .vonBaeyer) entry.source observation
  | .ringAssembly row =>
      ∃ observation : (row.reference (program.ringAssemblyPolicy .ringAssembly)).Observation,
        row.ProductionJudges (program.ringAssemblyPolicy .ringAssembly) entry.source observation
  | .acyclic row =>
      ∃ observation : (row.reference (program.acyclicPolicy .acyclic)).Observation,
        row.ProductionJudges (program.acyclicPolicy .acyclic) entry.source observation
  | .spiro row =>
      ∃ observation : (row.reference (program.spiroPolicy .spiro)).Observation,
        row.ProductionJudges (program.spiroPolicy .spiro) entry.source observation
  | .spiroNontetrahedral =>
      ∃ observation :
          (Remaining71P93SpiroAuthorityRow.reference (program.spiroPolicy .spiro)
            .spiroNontetrahedralCenters).Observation,
        P93SpiroNontetrahedralSourceCore (program.spiroPolicy .spiro) entry.source observation
  | .fusedCyclophane row =>
      ∃ observation :
          (row.reference (program.fusedPolicy .fused)
            (program.cyclophanePolicy .cyclophane)).Observation,
        row.ProductionJudges (program.fusedPolicy .fused)
          (program.cyclophanePolicy .cyclophane) entry.source observation
  | .coupledRingChain row =>
      ∃ observation : (row.reference program.coupledPolicy).Observation,
        row.ProductionJudges program.coupledPolicy entry.source observation

/-- The clause-indexed payload compiler is total over the full 56-row closed P-93 partition. -/
theorem entry_productionJudges
    (program : P93CanonicalSourceProgram) (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations) :
    program.EntryProductionWitness entry := by
  generalize clauseEq : entry.clause = clause
  cases clause with
  | fullerene row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_fullerene_productionJudges entry entryMem clauseEq
  | noncarbon row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_noncarbon_productionJudges entry entryMem clauseEq
  | general row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_general_productionJudges entry entryMem clauseEq
  | monocyclic row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_monocyclic_productionJudges entry entryMem clauseEq
  | vonBaeyer row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_vonBaeyer_productionJudges entry entryMem clauseEq
  | ringAssembly row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_ringAssembly_productionJudges entry entryMem clauseEq
  | acyclic row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_acyclic_productionJudges entry entryMem clauseEq
  | spiro row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_spiro_productionJudges entry entryMem clauseEq
  | spiroNontetrahedral =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_spiroNontetrahedral_productionJudges entry entryMem clauseEq
  | fusedCyclophane row =>
      simpa [EntryProductionWitness, clauseEq] using
        program.entry_fusedCyclophane_productionJudges entry entryMem clauseEq
  | coupledRingChain row =>
      cases row with
      | configurations =>
          simpa [EntryProductionWitness, clauseEq] using
            program.entry_coupled_productionJudges entry entryMem clauseEq

/-- Every row of the exact 56-clause manifest has an admitted, source-indexed entry whose
clause-specific legacy observation is judged by the compiled production relation.  This is the
package-to-all-rows boundary; freezing concrete source entries is deliberately a separate step. -/
theorem all56_entry_productionJudges
    (program : P93CanonicalSourceProgram) :
    ∀ clause ∈ P93Clause.all,
      ∃ entry ∈ program.observations,
        entry.clause = clause ∧ program.EntryProductionWitness entry := by
  intro clause clauseMem
  rcases program.clausesCovered clause clauseMem with ⟨entry, entryMem, clauseEq⟩
  exact ⟨entry, entryMem, clauseEq, program.entry_productionJudges entry entryMem⟩

end P93CanonicalSourceProgram
end TetraStereo.OneCenter
