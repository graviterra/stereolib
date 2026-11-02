import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceDescriptor
import TetraStereo.OneCenter.AuthoritativeSemanticParserDiagramRule3Through6Analysis
import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceAlignment

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.Rule6HandednessSemantics






































/-! ## 1. Actual raw written frame and returned occurrence endpoint IDs -/

/-- The actual raw written-neighbour atom-index frame at a transported parser center, in OpenSMILES
written order.  The entries are real parser atom indices, never a caller ordering. -/
def rawWrittenLigandFrame (molecule : RawMolecule) (center : Fin molecule.atomCount) : List Nat :=
  molecule.writtenNeighbors center.val

/-- Actual returned occurrence ligand endpoint IDs (semantic atom indices), retaining the source
carrier order of the returned cursors.  A coordinate-free cursor has `none`. -/
def occurrenceRootIDs (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) : List (Option Nat) :=
  roots.map (cursorAtomID source)

/-- Bounded finite alignment between the actual raw written frame and the actual returned
occurrence endpoint IDs at one recovered source center.  Fail-closed on missing centers, missing
frames, non-four frames, duplicate endpoints and unmatched IDs. -/
noncomputable def occurrenceParserSlotAlignment? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel) : Option (List Nat) := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  findSlotAlignment? (rawWrittenLigandFrame molecule rawCenter) (occurrenceRootIDs source roots)

/-- Independent meaning of a successful alignment, stated directly over the recovered center, the
declarative reroot frame and the actual endpoint-ID correspondence.  It mentions no search, no
success equation and no caller permutation. -/
def OccurrenceParserSlotAlignment (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) (slots : List Nat) : Prop :=
  source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
    source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := target, previous? := none } roots ∧
    ExactSlotAlignment
      (rawWrittenLigandFrame molecule
        (parserIndexOfAromaticCanonicalCenter molecule source agreement center))
      (occurrenceRootIDs source roots) slots

/-- Every successful occurrence alignment is the actual recovered center, the actual declarative
reroot frame, and an actual endpoint-ID correspondence. -/
theorem occurrenceParserSlotAlignment?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel) (slots : List Nat)
    (computed : occurrenceParserSlotAlignment? molecule source agreement target = some slots) :
    ∃ center roots,
      OccurrenceParserSlotAlignment molecule source agreement target center roots slots := by
  unfold occurrenceParserSlotAlignment? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
      | none => simp [centerComputed, rootsComputed] at computed
      | some roots =>
          cases found : findSlotAlignment?
              (rawWrittenLigandFrame molecule
                (parserIndexOfAromaticCanonicalCenter molecule source agreement center))
              (occurrenceRootIDs source roots) with
          | none => simp [centerComputed, rootsComputed, found] at computed
          | some positions =>
              simp [centerComputed, rootsComputed, found] at computed
              subst slots
              exact ⟨center, roots, centerComputed,
                source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots rootsComputed,
                findSlotAlignment?_sound _ _ positions found⟩

/-- The `i`-th returned occurrence endpoint ID is literally the raw written neighbour at the `i`-th
aligned slot: the alignment pins the actual raw written order against the actual returned frame. -/
theorem occurrenceParserSlotAlignment_rawWritten_eq_rootID
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) (slots : List Nat)
    (meaning : OccurrenceParserSlotAlignment molecule source agreement target center roots slots)
    (index : Fin 4) :
    slots[index.val]?.map
        (fun slot =>
          (rawWrittenLigandFrame molecule
            (parserIndexOfAromaticCanonicalCenter molecule source agreement center))[slot]?) =
      (occurrenceRootIDs source roots)[index.val]? := by
  have mapped := congrArg
    (fun values : List (Option Nat) => values[index.val]?) meaning.2.2.2.2.2
  simpa only [List.getElem?_map] using mapped

/-! ## 2. Universal parity transport through the actual slot permutation -/

/-- List-parity transport and the group-theoretic `S₄` reindexing agree whenever the explicit
`S₄` permutation's production list is the slot list. -/
theorem transportSlotParity_eq_reindexTetrahedralInputParity
    (parity : TetrahedralInputParity) (slots : List Nat) (permutation : Equiv.Perm (Fin 4))
    (listEq : finFourPermutationList permutation = slots) :
    transportSlotParity parity slots = reindexTetrahedralInputParity parity permutation := by
  simp [transportSlotParity, reindexTetrahedralInputParity, listEq]

/-- Any genuine four-slot alignment yields one `S₄` permutation whose production list is exactly the
matched slot list, and the transported written-order parity has the exact universal
`descriptorOfFinFourOrdering` meaning for every priority ordering. -/
theorem transportSlotParity_descriptor_universal (parity : TetrahedralInputParity)
    (endpoints : List Nat) (rootIDs : List (Option Nat)) (slots : List Nat)
    (matching : ExactSlotAlignment endpoints rootIDs slots) :
    ∃ permutation : Equiv.Perm (Fin 4),
      finFourPermutationList permutation = slots ∧
        ∀ ordering : Equiv.Perm (Fin 4),
          descriptorOfFinFourOrdering (transportSlotParity parity slots) ordering =
            descriptorOfFinFourOrdering parity (ordering.trans permutation) := by
  let permutation := finFourEquivOfPermutationList slots matching.2.2.1
  have listEq : finFourPermutationList permutation = slots :=
    finFourPermutationList_equivOfPermutationList slots matching.2.2.1
  refine ⟨permutation, listEq, ?_⟩
  intro ordering
  rw [transportSlotParity_eq_reindexTetrahedralInputParity parity slots permutation listEq]
  exact descriptorOfFinFourOrdering_reindex parity permutation ordering

/-- The committed parser final-root channel's canonical reindexing is the same all-`S₄` transport
law, so the occurrence channel and the committed channel share one parity semantics. -/
theorem parserCanonicalTetrahedralParity_descriptor_universal (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (writtenParity : TetrahedralInputParity) (ordering : Equiv.Perm (Fin 4)) :
    descriptorOfFinFourOrdering
        (parserCanonicalTetrahedralParity molecule source agreement writtenExact resolved
          center writtenParity) ordering =
      descriptorOfFinFourOrdering writtenParity
        (ordering.trans (parserWrittenToCanonicalPermutation molecule
          source agreement writtenExact resolved center).symm) :=
  parserCanonicalTetrahedralParity_descriptor molecule source agreement writtenExact resolved
    center writtenParity ordering

/-! ## 3. The parser-only occurrence descriptor channel -/

/-- New source-native parser-only channel at an arbitrary original occurrence target.  It reads the
copied `@`/`@@` annotation at the recovered center, aligns actual raw written slots against the
actual returned occurrence endpoint IDs, transports the parity into the returned order, and runs the
committed Rules-1a--6 backend with the supplied dependency view. The wrapper reads configuration
parity only from the actual raw parser annotation; its delegated priority backend retains existing
Rule-3 spatial queries for ordinary double bonds. -/
noncomputable def occurrenceParserDiagramDescriptor? (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) : Option RS := do
  let center ← source.aromaticCanonicalOccurrenceTetrahedralCenter? target
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let spec ← molecule.atomAt? rawCenter.val
  let writtenParity ← spec.tetrahedral?
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let slots ← findSlotAlignment? (rawWrittenLigandFrame molecule rawCenter)
    (occurrenceRootIDs source roots)
  source.aromaticCanonicalRule3Through6Descriptor? center.1 target view ruleFuel roots
    (transportSlotParity writtenParity slots)

/-- Independent complete meaning of a parser-diagram occurrence emission: the recovered real
occurrence center, the actual raw annotation (which is a member of the source's pinned parser
diagram), the actual declarative reroot frame, the actual raw-write/endpoint alignment, and the
complete Rules-1a--6 judgment in the returned order with the transported written parity. -/
def OccurrenceParserDiagramMeaning (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (_writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat)
    (descriptor : RS) : Prop :=
  ∃ center roots slots spec writtenParity diagram,
    source.aromaticCanonicalOccurrenceTetrahedralCenter? target = some center ∧
      molecule.atomAt?
          (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val = some spec ∧
      spec.tetrahedral? = some writtenParity ∧
      source.diagram? = some diagram ∧
      ({ atom := (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val,
          parity := writtenParity } : DiagramAtomConfiguration) ∈ diagram.atomConfigurations ∧
      source.DeclarativeAromaticCanonicalRerootChildren
        { occurrence := target, previous? := none } roots ∧
      ExactSlotAlignment
        (rawWrittenLigandFrame molecule
          (parserIndexOfAromaticCanonicalCenter molecule source agreement center))
        (occurrenceRootIDs source roots) slots ∧
      source.AromaticCanonicalRule3Through6CompleteDescriptorJudgment center.1 target view ruleFuel
        roots (transportSlotParity writtenParity slots) descriptor

/-- Every parser-only occurrence emission has the complete meaning above: no hidden success branch,
no caller permutation, and no separate diagram. -/
theorem occurrenceParserDiagramDescriptor?_sound (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput) (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (ruleFuel : Nat) (descriptor : RS)
    (computed : occurrenceParserDiagramDescriptor? molecule source agreement writtenExact
      target view ruleFuel = some descriptor) :
    OccurrenceParserDiagramMeaning molecule source agreement writtenExact target view ruleFuel
      descriptor := by
  unfold occurrenceParserDiagramDescriptor? at computed
  cases centerComputed : source.aromaticCanonicalOccurrenceTetrahedralCenter? target with
  | none => simp [centerComputed] at computed
  | some center =>
      cases atomComputed :
          molecule.atomAt?
            (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val with
      | none => simp [centerComputed, atomComputed] at computed
      | some spec =>
          cases parityComputed : spec.tetrahedral? with
          | none => simp [centerComputed, atomComputed, parityComputed] at computed
          | some writtenParity =>
              cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
              | none => simp [centerComputed, rootsComputed] at computed
              | some roots =>
                  cases found : findSlotAlignment?
                      (rawWrittenLigandFrame molecule
                        (parserIndexOfAromaticCanonicalCenter molecule source agreement center))
                      (occurrenceRootIDs source roots) with
                  | none =>
                      simp [centerComputed, atomComputed, rootsComputed, found] at computed
                  | some slots =>
                      have finalComputed :
                          source.aromaticCanonicalRule3Through6Descriptor? center.1 target view
                            ruleFuel roots (transportSlotParity writtenParity slots) =
                              some descriptor := by
                        simpa [centerComputed, atomComputed, parityComputed, rootsComputed,
                          found] using computed
                      obtain ⟨diagram, diagramEq, diagramMember⟩ :=
                        molecule.authoritativeStructureAgreement_diagram_contains_tetrahedral
                          source agreement
                          (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val
                          spec writtenParity atomComputed parityComputed
                      refine ⟨center, roots, slots, spec, writtenParity, diagram,
                        centerComputed, atomComputed, parityComputed, diagramEq, diagramMember,
                        source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots rootsComputed,
                        findSlotAlignment?_sound _ _ slots found, ?_⟩
                      exact source.aromaticCanonicalRule3Through6Descriptor?_sound center.1 target
                        view ruleFuel roots (transportSlotParity writtenParity slots) descriptor
                        finalComputed

/-! ## 4. Concrete closed annotated CFClBrI parser-only witness

The raw molecule is the literal CFClBrI constitution with only the carbon annotation `@@`
(`clockwise`); the semantic molecule is the committed `SingleWedgeSourceRegression.molecule`
(same atoms and interactions).  The source is `toDiagramConfiguration`-exact, has no spatial
channel, and carries an actual `WrittenNeighborExact` certificate. -/

namespace ClosedParserWitness

open SingleWedgeSourceRegression

/-- The annotated raw CFClBrI molecule: carbon with fluorine, chlorine, bromine, iodine and the
literal `@@` (`clockwise`) annotation.  `neighborOrder` is empty, so the written-neighbour view is
the honest bond-list order. -/
def annotatedRawCF : RawMolecule where
  atoms := [{ AtomSpec.aliphatic .C with tetrahedral? := some .clockwise },
    AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I]
  bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩]

/-- Successful conversion lands exactly on the committed CFClBrI semantic molecule. -/
theorem annotatedRawCF_toSemanticMolecule :
    annotatedRawCF.toSemanticMolecule? = some SingleWedgeSourceRegression.molecule := by
  decide +kernel

/-- The parser-only source: the exact conversion semantic molecule plus the literal raw-parser
diagram.  No spatial channel and no independent clean wedge source are introduced. -/
def parserSource : AuthoritativeChemicalInput :=
  { molecule := SingleWedgeSourceRegression.molecule
    diagram? := some annotatedRawCF.toDiagramConfiguration }

/-- The raw molecule's structural agreement with the parser-only source, by construction. -/
theorem parserSource_agreement :
    annotatedRawCF.AuthoritativeStructureAgreement parserSource :=
  ⟨annotatedRawCF_toSemanticMolecule, rfl⟩

/-- The parser-only source has genuinely no spatial channel. -/
theorem parserSource_spatial_none : parserSource.spatial? = none := rfl

/-- The parser source diagram is exactly `raw.toDiagramConfiguration`. -/
theorem parserSource_diagram :
    parserSource.diagram? = some annotatedRawCF.toDiagramConfiguration := rfl

/-- The actual normalized raw record carries the `WrittenNeighborExact` certificate. -/
theorem parserSource_writtenExact : annotatedRawCF.WrittenNeighborExact :=
  (annotatedRawCF.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

/-- The copied `@` annotation is a member of the source's pinned parser diagram. -/
theorem parserSource_diagram_contains_annotation :
    ({ atom := 0, parity := TetrahedralInputParity.clockwise } : DiagramAtomConfiguration) ∈
      annotatedRawCF.toDiagramConfiguration.atomConfigurations := by
  decide +kernel

/-- The true raw written order at the carbon is the actual bond-list order. -/
theorem parserSource_written_endpoints : annotatedRawCF.writtenNeighbors 0 = [1, 2, 3, 4] := by
  decide +kernel

/-- The recovered parser center at the carbon's final occurrence is the committed production
center.  Its raw index is `0`. -/
def parserCenter : parserSource.AromaticCanonicalTetrahedralCenter :=
  SingleWedgeOccurrenceAlignmentRegression.cfclbriProductionCenter

/-- The recovered center transports back to raw parser index `0`. -/
theorem parserCenter_raw_index :
    (parserIndexOfAromaticCanonicalCenter annotatedRawCF parserSource
      parserSource_agreement parserCenter).val = 0 := rfl

/-- The actual official CIP child IDs at the carbon center, computed from the parser-only source. -/
theorem parserSource_official_root_ids :
    officialRootIDs parserSource parserCenter.1 = [some 1, some 2, some 3, some 4] := by
  decide +kernel

/-- Every returned occurrence root list at the carbon center is a permutation of the actual IDs. -/
theorem parserSource_root_ids (fuel : Nat) :
    (finalOccurrenceRootIDs parserSource fuel parserCenter).Perm
      [some 1, some 2, some 3, some 4] := by
  have binding := finalOccurrenceRootIDs_perm_officialRootIDs parserSource fuel parserCenter
  rw [parserSource_official_root_ids] at binding
  exact binding

/-- The parser-only occurrence channel's alignment succeeds at the carbon's original occurrence,
using actual raw written slots and actual returned cursor IDs. -/
theorem parserOccurrence_alignment_exists (fuel : Nat) :
    ∃ slots, occurrenceParserSlotAlignment? annotatedRawCF parserSource parserSource_agreement
      (parserSource.aromaticCanonicalFinalOccurrence fuel parserCenter) = some slots := by
  have recovered := occurrenceTetrahedralCenter?_final parserSource fuel parserCenter
  have frames := finalOccurrenceRoots_are_returned parserSource fuel parserCenter
  have endpoints : rawWrittenLigandFrame annotatedRawCF
      (parserIndexOfAromaticCanonicalCenter annotatedRawCF parserSource
        parserSource_agreement parserCenter) = [1, 2, 3, 4] := by
    unfold rawWrittenLigandFrame
    rw [parserCenter_raw_index]
    exact parserSource_written_endpoints
  have sameIDs :
      (occurrenceRootIDs parserSource (finalOccurrenceRoots parserSource fuel parserCenter)).Perm
        ([1, 2, 3, 4].map some) := by
    have rootPerm := parserSource_root_ids fuel
    simpa [occurrenceRootIDs, finalOccurrenceRootIDs] using rootPerm
  obtain ⟨positions, found⟩ := findSlotAlignment?_exists_of_perm [1, 2, 3, 4] _
    (by decide) (by decide) sameIDs
  refine ⟨positions, ?_⟩
  simp [occurrenceParserSlotAlignment?, recovered, frames, endpoints, found]

/-- The closed witness pins the actual raw written order and the actual returned cursor IDs: the
endpoints are exactly `[1, 2, 3, 4]`, the returned IDs are a permutation of those IDs, and the
channel aligns them. -/
theorem parserOccurrence_witness :
    rawWrittenLigandFrame annotatedRawCF
        (parserIndexOfAromaticCanonicalCenter annotatedRawCF parserSource
          parserSource_agreement parserCenter) = [1, 2, 3, 4] ∧
      (∀ fuel : Nat,
        (occurrenceRootIDs parserSource
          (finalOccurrenceRoots parserSource fuel parserCenter)).Perm
            ([1, 2, 3, 4].map some)) ∧
      (∃ slots, occurrenceParserSlotAlignment? annotatedRawCF parserSource parserSource_agreement
        (parserSource.aromaticCanonicalFinalOccurrence 0 parserCenter) = some slots) := by
  refine ⟨?_, ?_, parserOccurrence_alignment_exists 0⟩
  · unfold rawWrittenLigandFrame
    rw [parserCenter_raw_index]
    exact parserSource_written_endpoints
  · intro fuel
    have rootPerm := parserSource_root_ids fuel
    simpa [occurrenceRootIDs, finalOccurrenceRootIDs] using rootPerm

end ClosedParserWitness

end TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
