import TetraStereo.OneCenter.AuthoritativeSemanticParserRule3Through6Conformance
import TetraStereo.OneCenter.Rule6HandednessCore

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Parser-diagram Rules 1a--6 analysis

The parser-facing authoritative conversion carries OpenSMILES `@`/`@@` evidence as a diagram
atom configuration, not as three-dimensional coordinates.  This module supplies the missing
nonvacuous semantic route.  Its first layer proves the exact finite-group transport from parser
written order to the source-canonical four-ligand order.
-/

open Rule6HandednessSemantics

/-- Reverse the orientation attached to an ordered tetrahedral frame. -/
def reverseTetrahedralInputParity : TetrahedralInputParity → TetrahedralInputParity
  | .clockwise => .anticlockwise
  | .anticlockwise => .clockwise

/-- Transport parity from an old four-slot frame to a new frame.  `newToOld` sends each new
position to the position occupied by the same ligand in the old frame. -/
def reindexTetrahedralInputParity (parity : TetrahedralInputParity)
    (newToOld : Equiv.Perm (Fin 4)) : TetrahedralInputParity :=
  if RawMolecule.permutationIsEven (finFourPermutationList newToOld) then parity
  else reverseTetrahedralInputParity parity

/-- Production inversion parity is multiplicative under composition of genuine `S₄`
permutations: a composite is even exactly when its factors have the same parity. -/
theorem finFourPermutationIsEven_trans
    (first second : Equiv.Perm (Fin 4)) :
    RawMolecule.permutationIsEven (finFourPermutationList (first.trans second)) =
      (RawMolecule.permutationIsEven (finFourPermutationList first) ==
        RawMolecule.permutationIsEven (finFourPermutationList second)) := by
  rw [finFourPermutationIsEven_eq_sign, finFourPermutationIsEven_eq_sign,
    finFourPermutationIsEven_eq_sign, Equiv.Perm.sign_trans]
  rcases Int.units_eq_one_or (Equiv.Perm.sign first) with firstSign | firstSign <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign second) with secondSign | secondSign <;>
      simp [firstSign, secondSign]

/-- Exact frame-transport law.  Computing a descriptor in a reindexed frame is identical to
composing its priority ordering with the new-to-old frame permutation and interpreting the
original parity. -/
theorem descriptorOfFinFourOrdering_reindex
    (parity : TetrahedralInputParity)
    (newToOld ordering : Equiv.Perm (Fin 4)) :
    descriptorOfFinFourOrdering
        (reindexTetrahedralInputParity parity newToOld) ordering =
      descriptorOfFinFourOrdering parity (ordering.trans newToOld) := by
  unfold descriptorOfFinFourOrdering
  rw [finFourPermutationIsEven_trans]
  cases newToOldEven :
      RawMolecule.permutationIsEven (finFourPermutationList newToOld) <;>
    cases orderingEven :
      RawMolecule.permutationIsEven (finFourPermutationList ordering) <;>
    cases parity <;>
      simp [reindexTetrahedralInputParity, reverseTetrahedralInputParity,
        RawMolecule.descriptorOfParity, newToOldEven]

/-- A successful indexed lookup supplies the corresponding entry in the parser's enumerated
atom list. -/
theorem mem_enumerateFrom_of_listGet?
    {α : Type*} (values : List α) (start index : Nat) (value : α)
    (lookup : listGet? values index = some value) :
    (start + index, value) ∈ enumerateFrom start values := by
  induction values generalizing start index with
  | nil => simp [listGet?] at lookup
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          have equality : head = value := by simpa [listGet?] using lookup
          subst value
          simp [enumerateFrom]
      | succ index =>
          have tailLookup : listGet? tail index = some value := by
            simpa [listGet?] using lookup
          have tailMember := inductionHypothesis (start + 1) index tailLookup
          rw [show start + (index + 1) = (start + 1) + index by omega]
          exact List.mem_cons_of_mem (start, head) tailMember

/-- Zero-based form of `mem_enumerateFrom_of_listGet?`. -/
theorem mem_enumerate_of_listGet?
    {α : Type*} (values : List α) (index : Nat) (value : α)
    (lookup : listGet? values index = some value) :
    (index, value) ∈ enumerate values := by
  simpa [enumerate] using mem_enumerateFrom_of_listGet? values 0 index value lookup

/-- Every parser tetrahedral annotation is copied into the exact diagram configuration built by
the public converter. -/
theorem RawMolecule.mem_toDiagramConfiguration_atomConfigurations_of_atomAt?
    (molecule : RawMolecule) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity)
    (atomObserved : molecule.atomAt? index = some spec)
    (parityObserved : spec.tetrahedral? = some parity) :
    ({ atom := index, parity := parity } : DiagramAtomConfiguration) ∈
      molecule.toDiagramConfiguration.atomConfigurations := by
  rw [RawMolecule.toDiagramConfiguration, List.mem_filterMap]
  refine ⟨(index, spec), ?_, ?_⟩
  · exact mem_enumerate_of_listGet? molecule.atoms index spec
      (by simpa [RawMolecule.atomAt?] using atomObserved)
  · simp [parityObserved]

/-- The copied parser annotation is present in every authoritative source that has exactly the
parser's checked semantic structure and diagram, independently of any attached spatial channel. -/
theorem RawMolecule.authoritativeStructureAgreement_diagram_contains_tetrahedral
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (index : Nat) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (atomObserved : molecule.atomAt? index = some spec)
    (parityObserved : spec.tetrahedral? = some parity) :
    ∃ diagram,
      source.diagram? = some diagram ∧
        ({ atom := index, parity := parity } : DiagramAtomConfiguration) ∈
          diagram.atomConfigurations := by
  refine ⟨molecule.toDiagramConfiguration,
    agreement.2, ?_⟩
  exact molecule.mem_toDiagramConfiguration_atomConfigurations_of_atomAt?
    index spec parity atomObserved parityObserved

namespace AuthoritativeChemicalInput

/-- Without a spatial channel, no reroot cursor can acquire a source coordinate. -/
theorem aromaticCanonicalRerootSpatialPoint?_eq_none_of_spatial_none
    (source : AuthoritativeChemicalInput) (noSpatial : source.spatial? = none)
    {carrierFuel : Nat} (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    source.aromaticCanonicalRerootSpatialPoint? cursor = none := by
  unfold aromaticCanonicalRerootSpatialPoint?
  split
  · cases current : cursor.occurrence.1.node.current? with
    | none => simp
    | some atom =>
        simp [aromaticCanonicalSpatialPointAt?, noSpatial]
  · rfl

/-- Consequently, coordinate-frame parity is absent for every root list when the source has no
spatial channel. -/
theorem aromaticCanonicalRerootFrameParity?_eq_none_of_spatial_none
    (source : AuthoritativeChemicalInput) (noSpatial : source.spatial? = none)
    {carrierFuel : Nat}
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel)) :
    source.aromaticCanonicalRerootFrameParity? roots = none := by
  cases roots with
  | nil => rfl
  | cons root roots =>
      simp [aromaticCanonicalRerootFrameParity?, List.mapM_cons,
        source.aromaticCanonicalRerootSpatialPoint?_eq_none_of_spatial_none
          noSpatial root]



theorem aromaticCanonicalScheduledRule3Through6Descriptor?_eq_none_of_spatial_none
    (source : AuthoritativeChemicalInput) (noSpatial : source.spatial? = none)
    {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
      semantics ruleFuel center = none := by
  unfold aromaticCanonicalScheduledRule3Through6Descriptor?
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
  | none => simp [target, rootsComputed]
  | some roots =>
      simp [target, rootsComputed,
        source.aromaticCanonicalRerootFrameParity?_eq_none_of_spatial_none
          noSpatial roots]

/-- The raw parser index corresponding to a semantic source center under exact structural
agreement. -/
def parserIndexOfAromaticCanonicalCenter
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (center : source.AromaticCanonicalTetrahedralCenter) : Fin molecule.atomCount :=
  Fin.cast
    (molecule.toSemanticMolecule?_atomCount source.molecule
      agreement.1)
    center.val

/-- Transporting the raw index back through semantic conversion returns the original source
center exactly. -/
theorem parserIndexOfAromaticCanonicalCenter_converted
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    molecule.convertedAtomIndex source
        agreement.1
        (parserIndexOfAromaticCanonicalCenter molecule source agreement center) =
      center.val := by
  apply Fin.ext
  rfl

/-- Every perceived semantic center corresponds to the independently stated ordinary parser
frame at its exact raw index. -/
theorem parserIndexOfAromaticCanonicalCenter_ordinaryFrame
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    molecule.OrdinaryConnectivityOnlyTetrahedralFrameAt
      (parserIndexOfAromaticCanonicalCenter molecule source agreement center) := by
  apply (molecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_convertedCenter_mem
    source agreement.1
      writtenExact resolved
      (parserIndexOfAromaticCanonicalCenter molecule source agreement center)).mpr
  rw [parserIndexOfAromaticCanonicalCenter_converted]
  exact center.2

/-- The exact four-neighbour length proof extracted from the corresponding ordinary parser
frame. -/
theorem parserIndexOfAromaticCanonicalCenter_four
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter) :
    (molecule.writtenNeighbors
      (parserIndexOfAromaticCanonicalCenter molecule source agreement center).val).length = 4 := by
  rcases (parserIndexOfAromaticCanonicalCenter_ordinaryFrame molecule
    source agreement writtenExact resolved center).1 with
      ⟨_spec, _atomObserved, _eligible, four⟩
  exact four

/-- The uniquely determined written-to-source-canonical frame permutation chosen from the exact
finite-frame bridge. -/
noncomputable def parserWrittenToCanonicalPermutation
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter) : Equiv.Perm (Fin 4) := by
  classical
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let four := parserIndexOfAromaticCanonicalCenter_four molecule
    source agreement writtenExact resolved center
  exact Classical.choose (molecule.exists_convertedWrittenToCanonicalPermutation
    source agreement.1
      writtenExact resolved rawCenter four center
      (parserIndexOfAromaticCanonicalCenter_converted molecule
        source agreement center).symm)

/-- Specification of the chosen frame permutation: every written parser slot is exactly the
canonical semantic ligand at the image position. -/
theorem parserWrittenToCanonicalPermutation_spec
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (position : Fin 4) :
    molecule.convertedWrittenTetrahedralLigandAtom source
        agreement.1 writtenExact
        (parserIndexOfAromaticCanonicalCenter molecule source agreement center)
        (parserIndexOfAromaticCanonicalCenter_four molecule
          source agreement writtenExact resolved center) position =
      source.aromaticCanonicalLigandAtom center
        (parserWrittenToCanonicalPermutation molecule
          source agreement writtenExact resolved center position) := by
  classical
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let four := parserIndexOfAromaticCanonicalCenter_four molecule
    source agreement writtenExact resolved center
  exact Classical.choose_spec (molecule.exists_convertedWrittenToCanonicalPermutation
    source agreement.1
      writtenExact resolved rawCenter four center
      (parserIndexOfAromaticCanonicalCenter_converted molecule
        source agreement center).symm) position

/-- The frame permutation is mathematically unique; the noncomputable choice in
`parserWrittenToCanonicalPermutation` cannot change the result. -/
theorem parserWrittenToCanonicalPermutation_unique
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (first second : Equiv.Perm (Fin 4))
    (firstSpec : ∀ position,
      molecule.convertedWrittenTetrahedralLigandAtom source
          agreement.1 writtenExact
          (parserIndexOfAromaticCanonicalCenter molecule source agreement center)
          (parserIndexOfAromaticCanonicalCenter_four molecule
            source agreement writtenExact resolved center) position =
        source.aromaticCanonicalLigandAtom center (first position))
    (secondSpec : ∀ position,
      molecule.convertedWrittenTetrahedralLigandAtom source
          agreement.1 writtenExact
          (parserIndexOfAromaticCanonicalCenter molecule source agreement center)
          (parserIndexOfAromaticCanonicalCenter_four molecule
            source agreement writtenExact resolved center) position =
        source.aromaticCanonicalLigandAtom center (second position)) :
    first = second := by
  apply Equiv.ext
  intro position
  apply source.aromaticCanonicalLigandAtom_injective center
  exact (firstSpec position).symm.trans (secondSpec position)

/-- Parser parity transported into the source-canonical ligand order. -/
noncomputable def parserCanonicalTetrahedralParity
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (writtenParity : TetrahedralInputParity) : TetrahedralInputParity :=
  reindexTetrahedralInputParity writtenParity
    (parserWrittenToCanonicalPermutation molecule
      source agreement writtenExact resolved center).symm

/-- The transported parity has the exact universal descriptor meaning relative to the original
written frame. -/
theorem parserCanonicalTetrahedralParity_descriptor
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (writtenParity : TetrahedralInputParity)
    (ordering : Equiv.Perm (Fin 4)) :
    descriptorOfFinFourOrdering
        (parserCanonicalTetrahedralParity molecule source agreement writtenExact resolved
          center writtenParity) ordering =
      descriptorOfFinFourOrdering writtenParity
        (ordering.trans (parserWrittenToCanonicalPermutation molecule
          source agreement writtenExact resolved center).symm) := by
  exact descriptorOfFinFourOrdering_reindex writtenParity
    (parserWrittenToCanonicalPermutation molecule
      source agreement writtenExact resolved center).symm ordering

/-- Nonvacuous molecule endpoint for parser diagram parity.  It uses the same causal Rules-3--5
state and the same complete Rules-1a--6 scheduler as the coordinate endpoint, but obtains input
orientation from the copied parser annotation after exact frame reindexing. -/
noncomputable def aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Option RS := do
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let spec ← molecule.atomAt? rawCenter.val
  let writtenParity ← spec.tetrahedral?
  let canonicalParity := parserCanonicalTetrahedralParity molecule source agreement
    writtenExact resolved center writtenParity
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  source.aromaticCanonicalRule3Through6Descriptor? center.1 target
    (source.aromaticCanonicalDependencyView state target) ruleFuel roots canonicalParity

/-- The parser-diagram wrapper has no hidden failure branch: emission is exactly raw annotation
lookup, canonical-root construction, and successful execution of the existing semantic scheduler
with the transported parity. -/
theorem aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?_eq_some_iff
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) :
    source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
        molecule agreement writtenExact resolved carrierFuel ruleFuel center = some descriptor ↔
      let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
      let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      ∃ spec writtenParity roots,
        molecule.atomAt? rawCenter.val = some spec ∧
          spec.tetrahedral? = some writtenParity ∧
          source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
          source.aromaticCanonicalRule3Through6Descriptor? center.1 target
            (source.aromaticCanonicalDependencyView state target) ruleFuel roots
            (parserCanonicalTetrahedralParity molecule source agreement writtenExact resolved
              center writtenParity) = some descriptor := by
  unfold aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  constructor
  · intro computed
    cases atomComputed : molecule.atomAt? rawCenter.val with
    | none => simp [rawCenter, atomComputed] at computed
    | some spec =>
        cases parityComputed : spec.tetrahedral? with
        | none => simp [rawCenter, atomComputed, parityComputed] at computed
        | some writtenParity =>
            cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
            | none =>
                simp [rawCenter, atomComputed, target,
                  rootsComputed] at computed
            | some roots =>
                refine ⟨spec, writtenParity, roots, atomComputed, parityComputed,
                  rootsComputed, ?_⟩
                simpa [rawCenter, atomComputed, parityComputed, target, rootsComputed,
                  semantics, state] using computed
  · rintro ⟨spec, writtenParity, roots, atomComputed, parityComputed,
      rootsComputed, finalComputed⟩
    simpa [rawCenter, atomComputed, parityComputed, target, rootsComputed,
      semantics, state] using finalComputed

/-- Exact consistency of the two independent orientation channels at one source-canonical
center: the parser annotation, transported out of written order, is the determinant parity of
the same canonical ligand-root frame.  This relation can be satisfied by a source produced by
`toAuthoritativeChemicalInputWithSpatial?`; unlike parser-only ingestion it is not vacuous. -/
def AromaticCanonicalParserSpatialParityAgreement
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  ∃ spec writtenParity roots,
    molecule.atomAt? rawCenter.val = some spec ∧
      spec.tetrahedral? = some writtenParity ∧
      source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
      source.aromaticCanonicalRerootFrameParity? roots =
        some (parserCanonicalTetrahedralParity molecule source agreement writtenExact resolved
          center writtenParity)

/-- When exact parser and spatial orientation evidence agree, the coordinate endpoint and the
parser-diagram endpoint are extensionally identical, including every refusal branch of the
shared Rules-1a--6 scheduler. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_eq_parserDiagram_of_agreement
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (consistent : source.AromaticCanonicalParserSpatialParityAgreement molecule agreement
      writtenExact resolved carrierFuel center) :
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel)
        ruleFuel center =
      source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
        molecule agreement writtenExact resolved carrierFuel ruleFuel center := by
  unfold AromaticCanonicalParserSpatialParityAgreement at consistent
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  obtain ⟨spec, writtenParity, roots, atomComputed, parityComputed,
    rootsComputed, spatialParityComputed⟩ := consistent
  unfold aromaticCanonicalScheduledRule3Through6Descriptor?
  unfold aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
  simp [atomComputed, parityComputed, rootsComputed, spatialParityComputed]

/-- In particular, two successful emissions from consistent parser and spatial evidence must
carry the same final descriptor. -/
theorem parserDiagram_descriptor_eq_coordinate_descriptor_of_agreement
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (consistent : source.AromaticCanonicalParserSpatialParityAgreement molecule agreement
      writtenExact resolved carrierFuel center)
    (coordinateDescriptor parserDescriptor : RS)
    (coordinateComputed :
      source.aromaticCanonicalScheduledRule3Through6Descriptor?
          (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
            carrierFuel ruleFuel)
          ruleFuel center = some coordinateDescriptor)
    (parserComputed :
      source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
          molecule agreement writtenExact resolved carrierFuel ruleFuel center =
        some parserDescriptor) :
    coordinateDescriptor = parserDescriptor := by
  have endpointsEqual :=
    source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_parserDiagram_of_agreement
      molecule agreement writtenExact resolved carrierFuel ruleFuel center consistent
  rw [endpointsEqual, parserComputed] at coordinateComputed
  exact Option.some.inj coordinateComputed.symm

/-- Checked joint-evidence endpoint.  It computes parser and exact-coordinate parity in the same
canonical root frame and refuses the center unless they are equal.  Thus conflicting evidence is
not silently resolved in favor of either channel. -/
noncomputable def aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) : Option RS := do
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let spec ← molecule.atomAt? rawCenter.val
  let writtenParity ← spec.tetrahedral?
  let canonicalParity := parserCanonicalTetrahedralParity molecule source agreement
    writtenExact resolved center writtenParity
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let spatialParity ← source.aromaticCanonicalRerootFrameParity? roots
  if spatialParity = canonicalParity then
    let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
      carrierFuel ruleFuel
    let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
    source.aromaticCanonicalRule3Through6Descriptor? center.1 target
      (source.aromaticCanonicalDependencyView state target) ruleFuel roots canonicalParity
  else
    none

/-- Exact success characterization of the checked joint-evidence endpoint. -/
theorem aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?_eq_some_iff
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) :
    source.aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?
        molecule agreement writtenExact resolved carrierFuel ruleFuel center = some descriptor ↔
      let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
      let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      ∃ spec writtenParity roots,
        molecule.atomAt? rawCenter.val = some spec ∧
          spec.tetrahedral? = some writtenParity ∧
          source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
          source.aromaticCanonicalRerootFrameParity? roots =
            some (parserCanonicalTetrahedralParity molecule source agreement writtenExact resolved
              center writtenParity) ∧
          source.aromaticCanonicalRule3Through6Descriptor? center.1 target
            (source.aromaticCanonicalDependencyView state target) ruleFuel roots
            (parserCanonicalTetrahedralParity molecule source agreement writtenExact resolved
              center writtenParity) = some descriptor := by
  unfold aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  constructor
  · intro computed
    cases atomComputed : molecule.atomAt? rawCenter.val with
    | none => simp [rawCenter, atomComputed] at computed
    | some spec =>
        cases parityComputed : spec.tetrahedral? with
        | none => simp [rawCenter, atomComputed, parityComputed] at computed
        | some writtenParity =>
            let canonicalParity := parserCanonicalTetrahedralParity molecule source agreement
              writtenExact resolved center writtenParity
            cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
            | none =>
                simp [rawCenter, atomComputed,
                  target, rootsComputed] at computed
            | some roots =>
                cases spatialComputed : source.aromaticCanonicalRerootFrameParity? roots with
                | none =>
                    simp [rawCenter, atomComputed,
                      target, rootsComputed, spatialComputed] at computed
                | some spatialParity =>
                    have parityEq : spatialParity = canonicalParity := by
                      by_contra different
                      simp [rawCenter, atomComputed, parityComputed, canonicalParity,
                        target, rootsComputed, spatialComputed, different] at computed
                    subst spatialParity
                    refine ⟨spec, writtenParity, roots, atomComputed, parityComputed,
                      rootsComputed, spatialComputed, ?_⟩
                    simpa [rawCenter, atomComputed, parityComputed, canonicalParity,
                      target, rootsComputed, spatialComputed, semantics, state] using computed
  · rintro ⟨spec, writtenParity, roots, atomComputed, parityComputed,
      rootsComputed, spatialComputed, finalComputed⟩
    simpa [rawCenter, atomComputed, parityComputed, target, rootsComputed,
      spatialComputed, semantics, state] using finalComputed

/-- Any successful joint-evidence computation establishes the explicit parser/spatial parity
agreement relation. -/
theorem aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?_agreement
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS)
    (computed :
      source.aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?
        molecule agreement writtenExact resolved carrierFuel ruleFuel center = some descriptor) :
    source.AromaticCanonicalParserSpatialParityAgreement molecule agreement writtenExact
      resolved carrierFuel center := by
  obtain ⟨spec, writtenParity, roots, atomComputed, parityComputed, rootsComputed,
    spatialComputed, _finalComputed⟩ :=
      (source.aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?_eq_some_iff
        molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor).mp computed
  exact ⟨spec, writtenParity, roots, atomComputed, parityComputed, rootsComputed,
    spatialComputed⟩

/-- Independent complete meaning of a descriptor emitted from parser diagram parity. -/
def AromaticCanonicalScheduledRule3Through6ParserDiagramDescriptorJudgment
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) : Prop :=
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  let permutation := parserWrittenToCanonicalPermutation molecule
    source agreement writtenExact resolved center
  let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
    carrierFuel ruleFuel
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  ∃ spec writtenParity canonicalParity roots diagram,
    molecule.atomAt? rawCenter.val = some spec ∧
      spec.tetrahedral? = some writtenParity ∧
      source.diagram? = some diagram ∧
      ({ atom := rawCenter.val, parity := writtenParity } : DiagramAtomConfiguration) ∈
        diagram.atomConfigurations ∧
      canonicalParity = reindexTetrahedralInputParity writtenParity permutation.symm ∧
      (∀ ordering,
        descriptorOfFinFourOrdering canonicalParity ordering =
          descriptorOfFinFourOrdering writtenParity
            (ordering.trans permutation.symm)) ∧
      source.DeclarativeAromaticCanonicalRerootChildren
        { occurrence := target, previous? := none } roots ∧
      source.AromaticCanonicalRule3Through6CompleteDescriptorJudgment center.1 target
        (source.aromaticCanonicalDependencyView state target)
        ruleFuel roots canonicalParity descriptor

/-- Every parser-diagram descriptor emitted by the semantic Rules-1a--6 endpoint satisfies the
complete source rule judgment and the exact universal written-frame parity transport law. -/
theorem aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?_sound
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS)
    (computed : source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
      molecule agreement writtenExact resolved carrierFuel ruleFuel center = some descriptor) :
    source.AromaticCanonicalScheduledRule3Through6ParserDiagramDescriptorJudgment
      molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor := by
  unfold aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram? at computed
  let rawCenter := parserIndexOfAromaticCanonicalCenter molecule source agreement center
  cases atomComputed : molecule.atomAt? rawCenter.val with
  | none => simp [rawCenter, atomComputed] at computed
  | some spec =>
      cases parityComputed : spec.tetrahedral? with
      | none => simp [rawCenter, atomComputed, parityComputed] at computed
      | some writtenParity =>
          let canonicalParity := parserCanonicalTetrahedralParity molecule source agreement
            writtenExact resolved center writtenParity
          let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
          cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
          | none =>
              simp [rawCenter, atomComputed,
                target, rootsComputed] at computed
          | some roots =>
              let semantics :=
                source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
                  carrierFuel ruleFuel
              let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
              have finalComputed :
                  source.aromaticCanonicalRule3Through6Descriptor? center.1 target
                    (source.aromaticCanonicalDependencyView state target)
                    ruleFuel roots canonicalParity = some descriptor := by
                simpa [rawCenter, atomComputed, parityComputed, canonicalParity,
                  target, rootsComputed, semantics, state] using computed
              obtain ⟨diagram, diagramEq, diagramMember⟩ :=
                molecule.authoritativeStructureAgreement_diagram_contains_tetrahedral
                  source agreement rawCenter.val spec writtenParity atomComputed parityComputed
              refine ⟨spec, writtenParity, canonicalParity, roots, diagram,
                atomComputed, parityComputed, diagramEq, diagramMember, rfl, ?_,
                source.aromaticCanonicalOccurrenceLigandFrame?_sound
                  target roots rootsComputed, ?_⟩
              · intro ordering
                exact parserCanonicalTetrahedralParity_descriptor molecule source agreement
                  writtenExact resolved center writtenParity ordering
              · exact source.aromaticCanonicalRule3Through6Descriptor?_sound center.1 target
                  (source.aromaticCanonicalDependencyView state target)
                  ruleFuel roots canonicalParity descriptor finalComputed

/-- Independent meaning of a joint-evidence emission: it is simultaneously justified by the
copied parser annotation, the exact rational coordinate determinant, their canonical-frame
agreement, and the complete Rules-1a--6 judgment. -/
def AromaticCanonicalScheduledRule3Through6ConsistentEvidenceDescriptorJudgment
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS) : Prop :=
  source.AromaticCanonicalScheduledRule3Through6ParserDiagramDescriptorJudgment
      molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor ∧
    source.AromaticCanonicalScheduledRule3Through6DescriptorJudgment
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)
      ruleFuel center descriptor ∧
    source.AromaticCanonicalParserSpatialParityAgreement molecule agreement writtenExact
      resolved carrierFuel center

/-- Every successful checked joint-evidence emission satisfies both independently stated
evidence judgments and their exact canonical-frame consistency relation. -/
theorem aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?_sound
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter) (descriptor : RS)
    (computed :
      source.aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?
        molecule agreement writtenExact resolved carrierFuel ruleFuel center = some descriptor) :
    source.AromaticCanonicalScheduledRule3Through6ConsistentEvidenceDescriptorJudgment
      molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor := by
  obtain ⟨spec, writtenParity, roots, atomComputed, parityComputed, rootsComputed,
    spatialComputed, finalComputed⟩ :=
      (source.aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?_eq_some_iff
        molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor).mp computed
  have parserComputed :
      source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
          molecule agreement writtenExact resolved carrierFuel ruleFuel center =
        some descriptor :=
    (source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?_eq_some_iff
      molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor).mpr
        ⟨spec, writtenParity, roots, atomComputed, parityComputed, rootsComputed, finalComputed⟩
  have coordinateComputed :
      source.aromaticCanonicalScheduledRule3Through6Descriptor?
          (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
            carrierFuel ruleFuel)
          ruleFuel center = some descriptor := by
    unfold aromaticCanonicalScheduledRule3Through6Descriptor?
    simp [rootsComputed, spatialComputed, finalComputed]
  exact ⟨
    source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?_sound
      molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor
        parserComputed,
    source.aromaticCanonicalScheduledRule3Through6Descriptor?_sound
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel)
      ruleFuel center descriptor coordinateComputed,
    source.aromaticCanonicalScheduledRule3Through6DescriptorFromConsistentEvidence?_agreement
      molecule agreement writtenExact resolved carrierFuel ruleFuel center descriptor computed⟩

/-- One source-indexed assignment emitted from parser diagram parity. -/
structure AromaticCanonicalScheduledRule3Through6ParserDiagramAssignment
    (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  descriptor : RS
  deriving DecidableEq

/-- Analyze every perceived ordinary source center using copied parser `@`/`@@` evidence and the
complete semantic Rules-1a--6 scheduler. -/
noncomputable def analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalScheduledRule3Through6ParserDiagramAssignment :=
  source.aromaticCanonicalTetrahedralCenters.filterMap fun center =>
    (source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
      molecule agreement writtenExact resolved carrierFuel ruleFuel center).map fun descriptor =>
        { center, descriptor }

/-- Exact membership characterization of the parser-diagram whole-molecule analyzer. -/
theorem mem_analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram_iff
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6ParserDiagramAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram
        molecule agreement writtenExact resolved carrierFuel ruleFuel ↔
      source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
        molecule agreement writtenExact resolved carrierFuel ruleFuel assignment.center =
          some assignment.descriptor := by
  constructor
  · intro present
    rw [analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram,
      List.mem_filterMap] at present
    obtain ⟨center, _centerPresent, observed⟩ := present
    cases descriptorComputed :
        source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?
          molecule agreement writtenExact resolved carrierFuel ruleFuel center with
    | none => simp [descriptorComputed] at observed
    | some descriptor =>
        simp [descriptorComputed] at observed
        subst assignment
        exact descriptorComputed
  · intro emitted
    rw [analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram,
      List.mem_filterMap]
    refine ⟨assignment.center,
      (source.mem_aromaticCanonicalTetrahedralCenters_iff assignment.center).mpr
        assignment.center.2, ?_⟩
    simp [emitted]

/-- Every whole-molecule parser-diagram assignment satisfies the exact copied-evidence,
frame-transport, and complete semantic Rules-1a--6 judgment. -/
theorem analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram_member_sound
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (agreement : molecule.AuthoritativeStructureAgreement source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6ParserDiagramAssignment)
    (present : assignment ∈
      source.analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram
        molecule agreement writtenExact resolved carrierFuel ruleFuel) :
    source.AromaticCanonicalScheduledRule3Through6ParserDiagramDescriptorJudgment
      molecule agreement writtenExact resolved carrierFuel ruleFuel
        assignment.center assignment.descriptor := by
  apply source.aromaticCanonicalScheduledRule3Through6DescriptorFromParserDiagram?_sound
  exact (source.mem_analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram_iff
    molecule agreement writtenExact resolved carrierFuel ruleFuel assignment).mp present

/-- Successful production normalization proves that every bond in the certified parsed result is
resolved. -/
theorem CertifiedChemistryNormalizationResult.bondsResolved_of_normalizeRawMoleculeCertified?
    (certified : CertifiedChemistryNormalizationResult)
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified) :
    ∀ bond, bond ∈ certified.result.parsed.bonds → bond.kind ≠ .unspecified := by
  have resultEq : certified.result = normalizeRawMolecule raw cycles :=
    normalizeRawMoleculeCertified?_result_eq raw cycles certified normalized
  have parsedEq : certified.result.parsed = raw.normalizeUnspecifiedBonds := by
    rw [resultEq]
    rfl
  intro bond membership
  apply raw.normalizeUnspecifiedBonds_resolved bond
  rw [← parsedEq]
  exact membership

/-- Public analyzer specialized to a successfully certified normalization.  No caller-supplied
written-neighbour or bond-resolution premise remains. -/
noncomputable def analyzeCertifiedAromaticCanonicalRule3Through6FromParserDiagram
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalScheduledRule3Through6ParserDiagramAssignment :=
  source.analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram
    certified.result.parsed
      (certified.result.parsed.authoritativeStructureAgreement_of_toAuthoritativeChemicalInput?
        source ingested)
      certified.writtenNeighborExact
      (CertifiedChemistryNormalizationResult.bondsResolved_of_normalizeRawMoleculeCertified?
        certified raw cycles normalized)
      carrierFuel ruleFuel

/-- Every descriptor emitted by the certified parser-diagram endpoint has the complete semantic
Rules-1a--6 meaning and exact raw diagram-parity provenance. -/
theorem analyzeCertifiedAromaticCanonicalRule3Through6FromParserDiagram_member_sound
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6ParserDiagramAssignment)
    (present : assignment ∈
      analyzeCertifiedAromaticCanonicalRule3Through6FromParserDiagram raw cycles certified
        normalized source ingested carrierFuel ruleFuel) :
    source.AromaticCanonicalScheduledRule3Through6ParserDiagramDescriptorJudgment
      certified.result.parsed
        (certified.result.parsed.authoritativeStructureAgreement_of_toAuthoritativeChemicalInput?
          source ingested)
        certified.writtenNeighborExact
        (CertifiedChemistryNormalizationResult.bondsResolved_of_normalizeRawMoleculeCertified?
          certified raw cycles normalized)
        carrierFuel ruleFuel assignment.center assignment.descriptor := by
  apply source.analyzeAromaticCanonicalScheduledRule3Through6FromParserDiagram_member_sound
  exact present

end AuthoritativeChemicalInput

end TetraStereo.OneCenter
