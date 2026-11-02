import TetraStereo.OneCenter.IUPACP93RelationalFullereneAuthorityCarrier

set_option autoImplicit false















namespace TetraStereo.OneCenter

open BlueBookP93.Cyclic

/-- One finite audited CIP fact.  `ownerIndex` identifies a complete constitutional addend in the
separately supplied owner list; no chirality classification is carried in this source record. -/
structure P93RelationalFullereneAuditedCIPFact
    (owners : List MolecularFullereneAddend) where
  ownerIndex : Fin owners.length
  unit : P93FullereneSubstituentStereogenicUnit
  citation : P93AuthorityCitationToken
  descriptor : P93FullereneSubstituentCIPDescriptor
  deriving DecidableEq

namespace P93RelationalFullereneAuditedCIPFact

/-- The audited uniqueness key, before resolving the owner index. -/
def key {owners : List MolecularFullereneAddend}
    (fact : P93RelationalFullereneAuditedCIPFact owners) :
    Fin owners.length × P93FullereneSubstituentStereogenicUnit :=
  (fact.ownerIndex, fact.unit)

/-- Resolve one finite source fact into the release-facing whole-addend assignment carrier. -/
def compile {owners : List MolecularFullereneAddend}
    (fact : P93RelationalFullereneAuditedCIPFact owners) :
    P93RelationalFullereneSubstituentCIPAssignment where
  owner := owners.get fact.ownerIndex
  unit := fact.unit
  citation := fact.citation
  descriptor := fact.descriptor

@[simp] theorem compile_owner {owners : List MolecularFullereneAddend}
    (fact : P93RelationalFullereneAuditedCIPFact owners) :
    fact.compile.owner = owners.get fact.ownerIndex := rfl

@[simp] theorem compile_unit {owners : List MolecularFullereneAddend}
    (fact : P93RelationalFullereneAuditedCIPFact owners) :
    fact.compile.unit = fact.unit := rfl

@[simp] theorem compile_citation {owners : List MolecularFullereneAddend}
    (fact : P93RelationalFullereneAuditedCIPFact owners) :
    fact.compile.citation = fact.citation := rfl

@[simp] theorem compile_descriptor {owners : List MolecularFullereneAddend}
    (fact : P93RelationalFullereneAuditedCIPFact owners) :
    fact.compile.descriptor = fact.descriptor := rfl

end P93RelationalFullereneAuditedCIPFact


def materializeP93RelationalFullereneCIPAssignments
    {owners : List MolecularFullereneAddend}
    (facts : List (P93RelationalFullereneAuditedCIPFact owners)) :
    List P93RelationalFullereneSubstituentCIPAssignment :=
  facts.map P93RelationalFullereneAuditedCIPFact.compile

/-- Exact materializer membership: assignments are neither invented nor omitted. -/
theorem mem_materializeP93RelationalFullereneCIPAssignments_iff
    {owners : List MolecularFullereneAddend}
    {facts : List (P93RelationalFullereneAuditedCIPFact owners)}
    {assignment : P93RelationalFullereneSubstituentCIPAssignment} :
    assignment ∈ materializeP93RelationalFullereneCIPAssignments facts ↔
      ∃ fact ∈ facts, fact.compile = assignment := by
  simp [materializeP93RelationalFullereneCIPAssignments]

/-- Resolving owner indices preserves keys when the owner list itself is duplicate-free. -/
private theorem p93RelationalFullereneCompilePairKey_injective
    {owners : List MolecularFullereneAddend}
    (ownersNodup : owners.Nodup) :
    Function.Injective (fun key :
      Fin owners.length × P93FullereneSubstituentStereogenicUnit =>
        (owners.get key.1, key.2)) := by
  rintro ⟨firstIndex, firstUnit⟩ ⟨secondIndex, secondUnit⟩ pairEq
  have ownerEq : owners.get firstIndex = owners.get secondIndex :=
    congrArg Prod.fst pairEq
  have unitEq : firstUnit = secondUnit := congrArg Prod.snd pairEq
  have indexEq : firstIndex = secondIndex := ownersNodup.get_inj_iff.mp ownerEq
  exact Prod.ext indexEq unitEq

/-- Duplicate-free audited `(ownerIndex, unit)` keys compile to duplicate-free
`(whole owner, unit)` keys.  `owners.Nodup` is essential: without it two distinct indices could
resolve to extensionally equal addends. -/
theorem materializeP93RelationalFullereneCIPAssignments_pairNodup
    {owners : List MolecularFullereneAddend}
    {facts : List (P93RelationalFullereneAuditedCIPFact owners)}
    (ownersNodup : owners.Nodup)
    (factKeysNodup :
      (facts.map P93RelationalFullereneAuditedCIPFact.key).Nodup) :
    ((materializeP93RelationalFullereneCIPAssignments facts).map fun assignment =>
      (assignment.owner, assignment.unit)).Nodup := by
  have resolvedKeysNodup :=
    factKeysNodup.map
      (p93RelationalFullereneCompilePairKey_injective ownersNodup)
  simpa [materializeP93RelationalFullereneCIPAssignments,
    P93RelationalFullereneAuditedCIPFact.key,
    P93RelationalFullereneAuditedCIPFact.compile, List.map_map] using resolvedKeysNodup

/-- A fact at every owner index yields a materialized assignment for every listed owner. -/
theorem materializeP93RelationalFullereneCIPAssignments_ownerCovered
    {owners : List MolecularFullereneAddend}
    {facts : List (P93RelationalFullereneAuditedCIPFact owners)}
    (indexCovered : ∀ index : Fin owners.length,
      ∃ fact ∈ facts, fact.ownerIndex = index)
    {owner : MolecularFullereneAddend}
    (ownerMem : owner ∈ owners) :
    ∃ assignment ∈ materializeP93RelationalFullereneCIPAssignments facts,
      assignment.owner = owner := by
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp ownerMem
  obtain ⟨fact, factMem, factIndexEq⟩ := indexCovered index
  refine ⟨fact.compile, ?_, ?_⟩
  · exact mem_materializeP93RelationalFullereneCIPAssignments_iff.mpr
      ⟨fact, factMem, rfl⟩
  · simp only [P93RelationalFullereneAuditedCIPFact.compile_owner, factIndexEq]



theorem materializeP93RelationalFullereneCIPAssignments_eligibleUnitComplete
    {owners : List MolecularFullereneAddend}
    {facts : List (P93RelationalFullereneAuditedCIPFact owners)}
    (Eligible : MolecularFullereneAddend →
      P93FullereneSubstituentStereogenicUnit → Prop)
    (auditComplete : ∀ index : Fin owners.length, ∀ unit,
      Eligible (owners.get index) unit →
        ∃ fact ∈ facts, fact.ownerIndex = index ∧ fact.unit = unit)
    {owner : MolecularFullereneAddend}
    (ownerMem : owner ∈ owners)
    (unit : P93FullereneSubstituentStereogenicUnit)
    (eligible : Eligible owner unit) :
    ∃ assignment ∈ materializeP93RelationalFullereneCIPAssignments facts,
      assignment.owner = owner ∧ assignment.unit = unit := by
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp ownerMem
  have eligibleAtIndex : Eligible (owners.get index) unit := eligible
  obtain ⟨fact, factMem, factIndexEq, factUnitEq⟩ :=
    auditComplete index unit eligibleAtIndex
  refine ⟨fact.compile, ?_, ?_, ?_⟩
  · exact mem_materializeP93RelationalFullereneCIPAssignments_iff.mpr
      ⟨fact, factMem, rfl⟩
  · simp only [P93RelationalFullereneAuditedCIPFact.compile_owner, factIndexEq]
  · exact P93RelationalFullereneAuditedCIPFact.compile_unit fact |>.trans factUnitEq

/-- Build the complete release-facing corpus directly from finite audited facts.  Chirality is
not inferred from those facts: `chiralOwnersInOwners` transports the independently computed
chiral-addend set into the separately audited owner list.  Source authorization of that set
remains an enclosing authority-observation obligation. -/
theorem p93RelationalFullereneSubstituentCIPAssignmentsComplete_of_auditedFacts
    (policy : P93RelationalFullereneAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (owners : List MolecularFullereneAddend)
    (facts : List (P93RelationalFullereneAuditedCIPFact owners))
    (ownersNodup : owners.Nodup)
    (factKeysNodup :
      (facts.map P93RelationalFullereneAuditedCIPFact.key).Nodup)
    (factsValid : ∀ fact ∈ facts,
      fact.compile.ValidFor policy source molecule input)
    (chiralOwnersInOwners : ∀ owner ∈ input.evidence.chiralAddends, owner ∈ owners)
    (chiralOwnerIndicesCovered : ∀ index : Fin owners.length,
      owners.get index ∈ input.evidence.chiralAddends →
        ∃ fact ∈ facts, fact.ownerIndex = index)
    (eligibleFactsComplete : ∀ index : Fin owners.length,
      owners.get index ∈ input.evidence.chiralAddends → ∀ unit,
        policy.SubstituentUnitInAddendEligible source molecule input
          (owners.get index) unit →
          ∃ fact ∈ facts, fact.ownerIndex = index ∧ fact.unit = unit) :
    P93RelationalFullereneSubstituentCIPAssignmentsComplete
      policy source molecule input
      (materializeP93RelationalFullereneCIPAssignments facts) := by
  refine ⟨materializeP93RelationalFullereneCIPAssignments_pairNodup
      ownersNodup factKeysNodup, ?_, ?_, ?_⟩
  · intro assignment assignmentMem
    obtain ⟨fact, factMem, rfl⟩ :=
      mem_materializeP93RelationalFullereneCIPAssignments_iff.mp assignmentMem
    exact factsValid fact factMem
  · intro owner ownerChiral
    have ownerMem := chiralOwnersInOwners owner ownerChiral
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp ownerMem
    have indexChiral : owners.get index ∈ input.evidence.chiralAddends := ownerChiral
    obtain ⟨fact, factMem, factIndexEq⟩ :=
      chiralOwnerIndicesCovered index indexChiral
    refine ⟨fact.compile, ?_, ?_⟩
    · exact mem_materializeP93RelationalFullereneCIPAssignments_iff.mpr
        ⟨fact, factMem, rfl⟩
    · simp only [P93RelationalFullereneAuditedCIPFact.compile_owner, factIndexEq]
  · intro owner ownerChiral unit eligible
    have ownerMem := chiralOwnersInOwners owner ownerChiral
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp ownerMem
    have indexChiral : owners.get index ∈ input.evidence.chiralAddends := ownerChiral
    have eligibleAtIndex :
        policy.SubstituentUnitInAddendEligible source molecule input
          (owners.get index) unit := eligible
    obtain ⟨fact, factMem, factIndexEq, factUnitEq⟩ :=
      eligibleFactsComplete index indexChiral unit eligibleAtIndex
    refine ⟨fact.compile, ?_, ?_, ?_⟩
    · exact mem_materializeP93RelationalFullereneCIPAssignments_iff.mpr
        ⟨fact, factMem, rfl⟩
    · simp only [P93RelationalFullereneAuditedCIPFact.compile_owner, factIndexEq]
    · exact P93RelationalFullereneAuditedCIPFact.compile_unit fact |>.trans factUnitEq

end TetraStereo.OneCenter
