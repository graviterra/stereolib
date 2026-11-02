import TetraStereo.UniversalProof.ExactFramedFamilyFullCollectorProofs.ExactFramedFamilyFullCollector
import TetraStereo.UniversalProof.OccurrenceDepthBatchListLawsProofs.OccurrenceDepthBatchListLaws
import TetraStereo.UniversalProof.NextFrontier.NativeFamilyFramedOccurrenceCaller
import TetraStereo.UniversalProof.NextFrontier.NativeGlobalProfileInventory
import TetraStereo.UniversalProof.NextFrontier.NativeChronologicalGenerationCoverage
import TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
import TetraStereo.OneCenter.ConstitutionAutomorphismSemantics
import TetraStereo.UniversalProof.NativeSecondSphereFamilyReport

set_option autoImplicit false


















































namespace TetraStereo.UniversalProof.FramedPrimaryDescriptorAdapterProofs.FramedPrimaryDescriptorAdapter

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeGlobalProfileInventory
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.ExactFramedFamilyFullCollectorProofs.ExactFramedFamilyFullCollector
open TetraStereo.UniversalProof.OccurrenceDepthBatchListLawsProofs.OccurrenceDepthBatchListLaws
open TetraStereo.UniversalProof.NativeFamilyFramedOccurrenceCaller

/-! ## 1. Preserved helpers: root generation and exact `RawDescriptorFact` projection -/

/-- The canonical center root is genuinely generated at the discovery root equal to that
center (accepted generation base constructor). -/
theorem canonicalCenterRoot_generated (mol : RawMolecule) (center : Nat) :
    CanonicalCenterTreeNode mol center (canonicalCenterRoot center) :=
  CanonicalCenterTreeNode.root

/-- Final assembly shared definitionally by `tetrahedralOccurrenceFactAuthoritative?`. -/
def assemblePrimaryFact (center : Nat) (state : OccurrenceAuxState)
    (fact : OccurrenceAuxFact) : RawDescriptorFact where
  atom := center
  descriptor := fact.descriptor
  uppercase := fact.uppercase
  evidenceSize := max 1 state.length
  decisiveRule? := none
  descriptorDependentPairs := state.length
  priorityPositions := fact.priorityPositions

/-- `tetrahedralOccurrenceFactAuthoritative?` is definitionally the environment build
followed by the root callback, assembled by `assemblePrimaryFact`. -/
theorem tetrahedralOccurrenceFactAuthoritative?_factored
    (mol : RawMolecule) (fuel center : Nat) :
    tetrahedralOccurrenceFactAuthoritative? mol fuel center =
      (do
        let state ← buildOccurrenceAuxStateFullyAuthoritative? mol fuel center
        let fact ← occurrenceFactAuthoritative? mol fuel state (canonicalCenterRoot center)
        some (assemblePrimaryFact center state fact)) := rfl

@[simp] theorem assemblePrimaryFact_atom (center : Nat) (state : OccurrenceAuxState)
    (fact : OccurrenceAuxFact) : (assemblePrimaryFact center state fact).atom = center := rfl

@[simp] theorem assemblePrimaryFact_uppercase (center : Nat) (state : OccurrenceAuxState)
    (fact : OccurrenceAuxFact) :
    (assemblePrimaryFact center state fact).uppercase = fact.uppercase := rfl

@[simp] theorem assemblePrimaryFact_evidenceSize (center : Nat) (state : OccurrenceAuxState)
    (fact : OccurrenceAuxFact) :
    (assemblePrimaryFact center state fact).evidenceSize = max 1 state.length := rfl

@[simp] theorem assemblePrimaryFact_decisiveRule (center : Nat) (state : OccurrenceAuxState)
    (fact : OccurrenceAuxFact) :
    (assemblePrimaryFact center state fact).decisiveRule? = none := rfl

@[simp] theorem assemblePrimaryFact_descriptorDependentPairs
    (center : Nat) (state : OccurrenceAuxState) (fact : OccurrenceAuxFact) :
    (assemblePrimaryFact center state fact).descriptorDependentPairs = state.length := rfl

/-! ## 2. The actual occurrence inventory consumed by the builder -/

/-- The literal filter the authoritative builder applies to its collected nodes. -/
def familyOccurrencePredicate (ps : List TetrahedralInputParity) (root : Nat)
    (node : CanonicalBranchNode) : Bool :=
  node.provenance == CanonicalNodeProvenance.realAtom && node.atom != root &&
    ((familyRaw ps).atomAt? node.atom).any fun spec => spec.tetrahedral?.isSome

/-- The filtered atom-count inventory (before depth sorting). -/
def familyOccurrenceFiltered (ps : List TetrahedralInputParity) (root : Nat) :
    List CanonicalBranchNode :=
  (inventory (familyRaw ps) root (familyRaw ps).atomCount).filter (familyOccurrencePredicate ps root)

/-- The actual descending-depth sorted occurrence inventory the builder consumes.  This is
the real builder expression, not an arbitrary node-inventory premise. -/
def familyOccurrenceList (ps : List TetrahedralInputParity) (root : Nat) :
    List CanonicalBranchNode :=
  sortDescBy (fun left right => left.depth ≥ right.depth) (familyOccurrenceFiltered ps root)

/-- A total fact function derived from the actual empty-state authoritative callback, so
the batch label is state-independent by construction. -/
noncomputable def familyNodeFact (ps : List TetrahedralInputParity)
    (node : CanonicalBranchNode) : OccurrenceAuxFact :=
  (occurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps)) [] node).getD
    { key := canonicalOccurrenceKey node, atom := node.atom, descriptor := .R,
      uppercase := false, priorityPositions := [] }

/-! ## 3. Actual membership, generation and root bounds -/

/-- Every actual maintained tag index is a bounded discovery root of the family. -/
theorem family_tagIndex_lt_atomCount (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    tagIndex i.val < (familyRaw ps).atomCount := by
  rw [familyRaw_atomCount]
  unfold tagIndex
  have := i.isLt
  omega

/-- The builder's filter's tetrahedral clause is exactly `observedTag` being defined. -/
theorem any_tetrahedral_eq_observedTag_isSome (mol : RawMolecule) (k : Nat) :
    (mol.atomAt? k).any (fun spec => spec.tetrahedral?.isSome) =
      (observedTag mol k).isSome := by
  unfold observedTag
  cases mol.atomAt? k <;> simp [Option.any]

/-- Every member of the atom-count inventory is genuinely generated at the root. -/
theorem family_inventory_generated (ps : List TetrahedralInputParity) {root : Nat}
    {node : CanonicalBranchNode}
    (member : node ∈ inventory (familyRaw ps) root (familyRaw ps).atomCount) :
    CanonicalCenterTreeNode (familyRaw ps) root node := by
  have nodeFlat : node ∈ (List.range (familyRaw ps).atomCount).flatMap
      (fun level => frontier (familyRaw ps) root level) := member
  obtain ⟨level, _levelMember, frontierMember⟩ := List.mem_flatMap.mp nodeFlat
  exact frontier_generated frontierMember

/-- The actual sorted occurrence list is a permutation of the filtered inventory. -/
theorem familyOccurrenceList_perm (ps : List TetrahedralInputParity) (root : Nat) :
    (familyOccurrenceList ps root).Perm (familyOccurrenceFiltered ps root) := by
  rw [familyOccurrenceList]
  exact sortDescBy_perm _ _

/-! ## 4. Total label interface from the actual caller (derived, not assumed) -/

/-- For every member of the actual occurrence inventory, the authoritative callback is the
same constant fact at every current state.  Derived from the caller's state-independent
tag fact; the tag index is recovered through `familyRaw_observedTag_iff`. -/
theorem family_occurrence_list_total (ps : List TetrahedralInputParity) (root : Nat)
    (rootBound : root < (familyRaw ps).atomCount) :
    TotalOn
      (fun current node => occurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps)) current node)
      (familyNodeFact ps) (familyOccurrenceList ps root) := by
  refine ⟨?_⟩
  intro node member current
  have filteredMember : node ∈ familyOccurrenceFiltered ps root :=
    (familyOccurrenceList_perm ps root).mem_iff.mp member
  rw [familyOccurrenceFiltered] at filteredMember
  obtain ⟨invMember, passes⟩ := List.mem_filter.mp filteredMember
  have generated := family_inventory_generated ps invMember
  rw [familyOccurrencePredicate] at passes
  rw [Bool.and_eq_true, Bool.and_eq_true] at passes
  obtain ⟨⟨_realEq, _neBool⟩, tagAny⟩ := passes
  have observedSome : (observedTag (familyRaw ps) node.atom).isSome = true := by
    rw [← any_tetrahedral_eq_observedTag_isSome]
    exact tagAny
  obtain ⟨p, hp⟩ : ∃ p, observedTag (familyRaw ps) node.atom = some p := by
    cases h : observedTag (familyRaw ps) node.atom with
    | none => rw [h] at observedSome; simp at observedSome
    | some p => exact ⟨p, rfl⟩
  obtain ⟨j, hjEq, _parity⟩ := (familyRaw_observedTag_iff ps node.atom p).mp hp
  have nodeAtom : node.atom = 1 + 12 * j.val + 5 := by
    rw [hjEq]; unfold tagIndex; omega
  have fuelEq : (analysisFuel (familyRaw ps) - 1) + 1 = analysisFuel (familyRaw ps) :=
    (family_analysisFuel_bounds ps).2.2
  have computed := family_actual_authoritative_occurrence_fact ps j rootBound generated
    nodeAtom current (analysisFuel (familyRaw ps) - 1)
  rw [fuelEq] at computed
  have baseline := family_actual_authoritative_occurrence_fact ps j rootBound generated
    nodeAtom [] (analysisFuel (familyRaw ps) - 1)
  rw [fuelEq] at baseline
  rw [computed]
  simp only [Option.some.injEq]
  unfold familyNodeFact
  rw [baseline]
  rfl

/-! ## 5. Whole-family auxiliary builder success -/

/-- **Main obligation.** For every parity list and every maintained tag index, the actual
fully-authoritative auxiliary builder succeeds at `analysisFuel` from the tag center, and
the returned state has the length of the actual sorted/filtered occurrence inventory. -/
theorem family_auxiliary_build_success (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∃ state,
      buildOccurrenceAuxStateFullyAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) = some state ∧
      state.length = (familyOccurrenceList ps (tagIndex i.val)).length := by
  let root := tagIndex i.val
  have rootBound : root < (familyRaw ps).atomCount := family_tagIndex_lt_atomCount ps i
  have total := family_occurrence_list_total ps root rootBound
  have batch := authoritative_batches_budget_length_succ
    (fun current node => occurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps)) current node)
    (familyNodeFact ps) (familyOccurrenceList ps root) [] total
  refine ⟨(familyOccurrenceList ps root).map (familyNodeFact ps), ?_, ?_⟩
  · unfold buildOccurrenceAuxStateFullyAuthoritative?
    rw [family_collectAuthoritative_analysisFuel ps (root := root) rootBound]
    show discoverOccurrenceAuxBatchesAuthoritative?
      (fun current node => occurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps)) current node)
      ((familyOccurrenceList ps root).length + 1) (familyOccurrenceList ps root) [] =
      some ((familyOccurrenceList ps root).map (familyNodeFact ps))
    simpa only [List.nil_append] using batch
  · simp only [List.length_map]
    rfl

/-- **Final outer fact existence.** The authoritative primary occurrence fact exists at the
tag center, with descriptor `descriptorOfParity (ps.get i) false`, uppercase `true`,
priority positions `[2, 0, 3, 1]`, `evidenceSize = max 1 state.length` and
`descriptorDependentPairs = state.length`.  Derived from the same actual caller and the
root-generation base; the occurrence-count claim is not assumed. -/
theorem family_primary_occurrence_fact_exists (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∃ state,
      buildOccurrenceAuxStateFullyAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) = some state ∧
      tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) =
        some (assemblePrimaryFact (tagIndex i.val) state
          { key := canonicalOccurrenceKey (canonicalCenterRoot (tagIndex i.val))
            atom := (canonicalCenterRoot (tagIndex i.val)).atom
            descriptor := RawMolecule.descriptorOfParity (ps.get i) false
            uppercase := true
            priorityPositions := [2, 0, 3, 1] }) := by
  obtain ⟨state, buildEq, _lengthEq⟩ := family_auxiliary_build_success ps i
  have rootBound := family_tagIndex_lt_atomCount ps i
  have rootGen : CanonicalCenterTreeNode (familyRaw ps) (tagIndex i.val)
      (canonicalCenterRoot (tagIndex i.val)) := canonicalCenterRoot_generated _ _
  have centerAtom : (canonicalCenterRoot (tagIndex i.val)).atom = 1 + 12 * i.val + 5 := by
    change tagIndex i.val = 1 + 12 * i.val + 5
    unfold tagIndex
    omega
  have fuelEq : (analysisFuel (familyRaw ps) - 1) + 1 = analysisFuel (familyRaw ps) :=
    (family_analysisFuel_bounds ps).2.2
  have primaryFact := family_actual_authoritative_occurrence_fact ps i rootBound rootGen
    centerAtom state (analysisFuel (familyRaw ps) - 1)
  rw [fuelEq] at primaryFact
  refine ⟨state, buildEq, ?_⟩
  rw [tetrahedralOccurrenceFactAuthoritative?_factored, buildEq]
  change (occurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
    state (canonicalCenterRoot (tagIndex i.val))).bind
      (fun fact => some (assemblePrimaryFact (tagIndex i.val) state fact)) = _
  rw [primaryFact]
  rfl

/-! ## 6. Exact occurrence count and repaired authoritative raw fact

The exact sorted count is obtained from the accepted collector07
(`family_aux_filter_length`): the builder's literal filtered inventory and the accepted
auxiliary filter are definitionally identical, so the permutation length of
`familyOccurrenceList_perm` composes with the accepted count. -/

/-- The actual sorted occurrence list consumed by the builder has exactly `ps.length - 1`
entries. -/
theorem familyOccurrenceList_length (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (familyOccurrenceList ps (tagIndex i.val)).length = ps.length - 1 := by
  rw [(familyOccurrenceList_perm ps (tagIndex i.val)).length_eq]
  change (familyAuxFiltered ps i).length = ps.length - 1
  exact family_aux_filter_length ps i

/-- The actual fully-authoritative builder returns a state of length exactly
`ps.length - 1` (zero for the singleton/`ps.length = 1` parity). -/
theorem family_auxiliary_build_exact_count (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∃ state,
      buildOccurrenceAuxStateFullyAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) = some state ∧
      state.length = ps.length - 1 := by
  obtain ⟨state, buildEq, lengthEq⟩ := family_auxiliary_build_success ps i
  exact ⟨state, buildEq, by rw [lengthEq, familyOccurrenceList_length ps i]⟩

/-- **Repaired authoritative raw fact.** The outer occurrence fact is the assembled
`RawDescriptorFact` with the exact occurrence count `ps.length - 1` in
`evidenceSize = max 1 (ps.length - 1)` and `descriptorDependentPairs = ps.length - 1`.
The existential states of `family_primary_occurrence_fact_exists` and
`family_auxiliary_build_exact_count` coincide by injectivity of `some` on the matching
actual builder equality; no output premise is assumed. -/
theorem family_repaired_authoritative_raw_fact
    (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
      (tagIndex i.val) =
      some
        { atom := tagIndex i.val
          descriptor := RawMolecule.descriptorOfParity (ps.get i) false
          uppercase := true
          evidenceSize := max 1 (ps.length - 1)
          decisiveRule? := none
          descriptorDependentPairs := ps.length - 1
          priorityPositions := [2, 0, 3, 1] } := by
  obtain ⟨state₁, buildEq₁, factEq⟩ := family_primary_occurrence_fact_exists ps i
  obtain ⟨state₂, buildEq₂, count₂⟩ := family_auxiliary_build_exact_count ps i
  have stateEq : state₁ = state₂ := by
    rw [buildEq₁] at buildEq₂
    simpa only [Option.some.injEq] using buildEq₂
  have count₁ : state₁.length = ps.length - 1 := by
    rw [stateEq]
    exact count₂
  rw [factEq, Option.some.injEq]
  unfold assemblePrimaryFact
  rw [count₁]

/-! ## 7. Runtime/string report agreement (SOURCE-only new join)

These four theorems join the preserved repaired authoritative raw fact (Section 6) to the
installed `NativeSecondSphereFamilyReport` public report.  They prove **outcome agreement**
through `rawDescriptorFactOutcome`, never whole `RawDescriptorFact` equality: the repaired
fact carries `evidenceSize = max 1 (ps.length - 1)` whereas the actual seed fact carries
`evidenceSize = 0`, and that metadata difference is immaterial under the outcome projection
(only `uppercase` and `descriptor` are read).  The report namespace is referenced fully
qualified so `familyState`/`familyFuel`/`familyResult` stay unambiguous.

KERNEL STATUS: OPEN.  The join is SOURCE-only until Root installs and kernel-checks the new
stable logical root `NativeSecondSphereFamilyReport`; the scheduled source model, compiler
and export remain separate and OPEN.

-/

/-- **1.** The repaired authoritative occurrence fact and the actual initial seed fact have
the same projected outcome: both are uppercase tetrahedral with the parity-derived
descriptor.  The differing evidence sizes are ignored by the projection. -/
theorem family_repaired_seed_outcome_agreement
    (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
      (tagIndex i.val)).map rawDescriptorFactOutcome =
      some (rawDescriptorFactOutcome (SecondSphereInitialSeedBridge.seedFact ps i)) := by
  rw [family_repaired_authoritative_raw_fact ps i]
  simp only [Option.map_some, rawDescriptorFactOutcome,
    SecondSphereInitialSeedBridge.seedFact, ↓reduceIte]

/-- **2.** The actual discovered family state fact at every tag agrees, under the outcome
projection, with the repaired authoritative runtime option.  This is the actual computed
discovery (`actual_discovered_tag`), not an independently chosen state. -/
theorem family_repaired_discovered_outcome_agreement
    (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    (tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
      (tagIndex i.val)).map rawDescriptorFactOutcome =
      ((SecondSphereFamilyReportBridge.familyState ps).factAt? (tagIndex i.val)).map
        rawDescriptorFactOutcome := by
  rw [SecondSphereFamilyReportBridge.actual_discovered_tag ps i]
  simpa only [Option.map_some] using family_repaired_seed_outcome_agreement ps i

/-- **3.** The actual String report retains, at every tag, the concrete row whose outcome is
the projected authoritative outcome.  The witness fact is the repaired authoritative record,
the row list is the admitted normalized `certifiedFamily` report, and membership is the
actual public tag membership.  No row-membership premise is supplied and no `≥ 2` guard is
needed (`actual_early_assignment_none` and `actual_string_report` quantify all `ps`). -/
theorem family_repaired_string_report_member
    (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ∃ fact rows,
      tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) = some fact ∧
      analyzeSmiles (SecondSphereNativeBlockParser.nativeFamilyString ps) = Except.ok rows ∧
      ({ unit := .tetrahedral (tagIndex i.val),
         outcome := rawDescriptorFactOutcome fact } : StereoAssignment) ∈ rows := by
  refine ⟨({ atom := tagIndex i.val
             descriptor := RawMolecule.descriptorOfParity (ps.get i) false
             uppercase := true
             evidenceSize := max 1 (ps.length - 1)
             decisiveRule? := none
             descriptorDependentPairs := ps.length - 1
             priorityPositions := [2, 0, 3, 1] } : RawDescriptorFact),
    analyzeNormalized
      ((SecondSphereFamilyValenceInstantiation.certifiedFamily ps).result),
    family_repaired_authoritative_raw_fact ps i,
    SecondSphereFamilyReportBridge.actual_string_report ps, ?_⟩
  have outcomeEq : rawDescriptorFactOutcome
        ({ atom := tagIndex i.val
           descriptor := RawMolecule.descriptorOfParity (ps.get i) false
           uppercase := true
           evidenceSize := max 1 (ps.length - 1)
           decisiveRule? := none
           descriptorDependentPairs := ps.length - 1
           priorityPositions := [2, 0, 3, 1] } : RawDescriptorFact) =
      StereoOutcome.tetrahedral (RawMolecule.descriptorOfParity (ps.get i) false) := by
    simp only [rawDescriptorFactOutcome, ↓reduceIte]
  rw [outcomeEq]
  exact SecondSphereFamilyReportBridge.actual_tag_public_membership ps i

/-- **4.** Concrete whole-family runtime report agreement: every tag's actual computed
outcome agrees with the actual discovered family state, the actual String report equals the
full family row report, and every tag satisfies the actual runtime fact + String member
existential of **3**.  Derived entirely from **1**–**3** and the existing
`actual_string_full_report`.  The scheduled source model, compiler and export are NOT yet
included and remain OPEN. -/
theorem family_runtime_report_agreement (ps : List TetrahedralInputParity) :
    (∀ i : Fin ps.length,
      (tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val)).map rawDescriptorFactOutcome =
        ((SecondSphereFamilyReportBridge.familyState ps).factAt? (tagIndex i.val)).map
          rawDescriptorFactOutcome) ∧
    analyzeSmiles (SecondSphereNativeBlockParser.nativeFamilyString ps) =
      Except.ok (SecondSphereFamilyReportBridge.familyFullRows ps) ∧
    (∀ i : Fin ps.length, ∃ fact rows,
      tetrahedralOccurrenceFactAuthoritative? (familyRaw ps) (analysisFuel (familyRaw ps))
        (tagIndex i.val) = some fact ∧
      analyzeSmiles (SecondSphereNativeBlockParser.nativeFamilyString ps) = Except.ok rows ∧
      ({ unit := .tetrahedral (tagIndex i.val),
         outcome := rawDescriptorFactOutcome fact } : StereoAssignment) ∈ rows) :=
  ⟨fun i => family_repaired_discovered_outcome_agreement ps i,
   SecondSphereFamilyReportBridge.actual_string_full_report ps,
   fun i => family_repaired_string_report_member ps i⟩

end TetraStereo.UniversalProof.FramedPrimaryDescriptorAdapterProofs.FramedPrimaryDescriptorAdapter
