/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.OrganicStereoJointAuthorityCellMixturesCore

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false























namespace TetraStereo.OneCenter
namespace OrganicStereoJointAuthorityCellMixtures

noncomputable section

open scoped BigOperators

open OrganicStereoJointAuthorityCellAssembly
open OrganicStereoSpatialSupportMolecularAssembly
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoAuthorityMixedSourceAssembly
open OrganicStereoAllAuthorityEntries
open OccurrenceSpatialSupportExperiment

section FixtureArguments

-- The generic parameter tuple of the mixture theory.
variable (P : JointParameterTypes)

-- The caller's actual authority policy record.
variable (policies : AllAuthorityPolicies)

-- The caller's actual ordered raw-entry list at the dependency's witness core and enumeration.
variable (entries : List (RawEntry (V := Fin 3) P.ligandId P.ligandKind P.fragmentId P.fragmentKind
  P.state P.framework P.baseName P.numbering P.locant P.prefix
  policies witnessCore witnessEnumeration))










def f0Case : JointCase P :=
  ⟨3, witnessJointStraight (LigandId := P.ligandId) (LigandKind := P.ligandKind)
    (FragmentId := P.fragmentId) (FragmentKind := P.fragmentKind) (State := P.state)
    (Framework := P.framework) (BaseName := P.baseName) (Numbering := P.numbering)
    (Locant := P.locant) (Prefix := P.prefix) policies entries⟩


def f1Case : JointCase P :=
  ⟨3, witnessJointCurved (LigandId := P.ligandId) (LigandKind := P.ligandKind)
    (FragmentId := P.fragmentId) (FragmentKind := P.fragmentKind) (State := P.state)
    (Framework := P.framework) (BaseName := P.baseName) (Numbering := P.numbering)
    (Locant := P.locant) (Prefix := P.prefix) policies entries⟩

@[simp] theorem f0Case_nat : (f0Case P policies entries).1 = 3 := rfl

@[simp] theorem f1Case_nat : (f1Case P policies entries).1 = 3 := rfl

@[simp] theorem f0Case_spatial :
    (f0Case P policies entries).2.spatial = witnessRequestStraight := rfl

@[simp] theorem f1Case_spatial :
    (f1Case P policies entries).2.spatial = witnessRequestCurved := rfl


theorem f0Case_cells :
    (f0Case P policies entries).2.spatial.cells = [witnessMolecularCellStraight] := by
  rw [f0Case_spatial]
  rfl


theorem f1Case_cells :
    (f1Case P policies entries).2.spatial.cells = [witnessMolecularCellCurved] := by
  rw [f1Case_spatial]
  rfl



theorem f0Case_ne_f1Case : f0Case P policies entries ≠ f1Case P policies entries := by
  intro equal
  have requests : witnessJointStraight (LigandId := P.ligandId)
        (LigandKind := P.ligandKind) (FragmentId := P.fragmentId)
        (FragmentKind := P.fragmentKind) (State := P.state) (Framework := P.framework)
        (BaseName := P.baseName) (Numbering := P.numbering) (Locant := P.locant)
        (Prefix := P.prefix) policies entries =
      witnessJointCurved (LigandId := P.ligandId) (LigandKind := P.ligandKind)
        (FragmentId := P.fragmentId) (FragmentKind := P.fragmentKind) (State := P.state)
        (Framework := P.framework) (BaseName := P.baseName) (Numbering := P.numbering)
        (Locant := P.locant) (Prefix := P.prefix) policies entries :=
    eq_of_heq (Sigma.mk.inj_iff.mp (show
      (⟨3, witnessJointStraight (LigandId := P.ligandId) (LigandKind := P.ligandKind)
        (FragmentId := P.fragmentId) (FragmentKind := P.fragmentKind) (State := P.state)
        (Framework := P.framework) (BaseName := P.baseName) (Numbering := P.numbering)
        (Locant := P.locant) (Prefix := P.prefix) policies entries⟩ : JointCase P) =
      ⟨3, witnessJointCurved (LigandId := P.ligandId) (LigandKind := P.ligandKind)
        (FragmentId := P.fragmentId) (FragmentKind := P.fragmentKind) (State := P.state)
        (Framework := P.framework) (BaseName := P.baseName) (Numbering := P.numbering)
        (Locant := P.locant) (Prefix := P.prefix) policies entries⟩ from equal)).2
  have assembled : assembleJoint (witnessJointStraight (LigandId := P.ligandId)
        (LigandKind := P.ligandKind) (FragmentId := P.fragmentId)
        (FragmentKind := P.fragmentKind) (State := P.state) (Framework := P.framework)
        (BaseName := P.baseName) (Numbering := P.numbering) (Locant := P.locant)
        (Prefix := P.prefix) policies entries) =
      assembleJoint (witnessJointCurved (LigandId := P.ligandId) (LigandKind := P.ligandKind)
        (FragmentId := P.fragmentId) (FragmentKind := P.fragmentKind) (State := P.state)
        (Framework := P.framework) (BaseName := P.baseName) (Numbering := P.numbering)
        (Locant := P.locant) (Prefix := P.prefix) policies entries) :=
    congrArg assembleJoint requests
  have mapped := congrArg (fun representation : JointRepresentation (V := Fin 3) P.ligandId
      P.ligandKind P.fragmentId P.fragmentKind P.state P.framework P.baseName P.numbering
      P.locant P.prefix => representation.cells.map encodedInteriorValue) assembled
  have straightInterior : (assembleJoint (witnessJointStraight (LigandId := P.ligandId)
        (LigandKind := P.ligandKind) (FragmentId := P.fragmentId)
        (FragmentKind := P.fragmentKind) (State := P.state) (Framework := P.framework)
        (BaseName := P.baseName) (Numbering := P.numbering) (Locant := P.locant)
        (Prefix := P.prefix) policies entries)).cells.map encodedInteriorValue =
      [F0Fun Delta.barycentre] :=
    witnessRepresentationStraight_interior
  have curvedInterior : (assembleJoint (witnessJointCurved (LigandId := P.ligandId)
        (LigandKind := P.ligandKind) (FragmentId := P.fragmentId)
        (FragmentKind := P.fragmentKind) (State := P.state) (Framework := P.framework)
        (BaseName := P.baseName) (Numbering := P.numbering) (Locant := P.locant)
        (Prefix := P.prefix) policies entries)).cells.map encodedInteriorValue =
      [F1Fun Delta.barycentre] :=
    witnessRepresentationCurved_interior
  change (assembleJoint (witnessJointStraight (LigandId := P.ligandId)
        (LigandKind := P.ligandKind) (FragmentId := P.fragmentId)
        (FragmentKind := P.fragmentKind) (State := P.state) (Framework := P.framework)
        (BaseName := P.baseName) (Numbering := P.numbering) (Locant := P.locant)
        (Prefix := P.prefix) policies entries)).cells.map encodedInteriorValue =
      (assembleJoint (witnessJointCurved (LigandId := P.ligandId) (LigandKind := P.ligandKind)
        (FragmentId := P.fragmentId) (FragmentKind := P.fragmentKind) (State := P.state)
        (Framework := P.framework) (BaseName := P.baseName) (Numbering := P.numbering)
        (Locant := P.locant) (Prefix := P.prefix) policies entries)).cells.map
      encodedInteriorValue at mapped
  rw [straightInterior, curvedInterior] at mapped
  have pointEqual : F0Fun Delta.barycentre = F1Fun Delta.barycentre := by
    simpa using mapped
  exact F0Fun_barycentre_ne_F1Fun_barycentre pointEqual




def f0f1Support : Set (JointCase P) :=
  {f0Case P policies entries, f1Case P policies entries}

theorem f0Case_mem_f0f1Support : f0Case P policies entries ∈ f0f1Support P policies entries := by
  simp [f0f1Support]

theorem f1Case_mem_f0f1Support : f1Case P policies entries ∈ f0f1Support P policies entries := by
  simp [f0f1Support]


def f0f1PairSample : MixtureSample P :=
  pairSample P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)


def f0f1DiagonalUncertainty : Set (MixtureSample P) :=
  diagonalUncertainty P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)


def f0f1AntidiagonalUncertainty : Set (MixtureSample P) :=
  antidiagonalUncertainty P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)

theorem f0f1PairSample_k : (f0f1PairSample P policies entries).k = 2 := rfl

theorem f0f1PairSample_cases :
    (f0f1PairSample P policies entries).cases (0 : Fin 2) = f0Case P policies entries ∧
      (f0f1PairSample P policies entries).cases (1 : Fin 2) = f1Case P policies entries :=
  ⟨pairSample_cases_zero P (f0f1Support P policies entries) (f0Case P policies entries)
      (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
      (f1Case_mem_f0f1Support P policies entries),
    pairSample_cases_one P (f0f1Support P policies entries) (f0Case P policies entries)
      (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
      (f1Case_mem_f0f1Support P policies entries)⟩

theorem f0f1_same_firstMargin :
    firstMargin P (f0f1DiagonalUncertainty P policies entries) =
      firstMargin P (f0f1AntidiagonalUncertainty P policies entries) :=
  diagonal_antidiagonal_same_firstMargin P (f0f1Support P policies entries)
    (f0Case P policies entries) (f1Case P policies entries)
    (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_same_secondMargin :
    secondMargin P (f0f1DiagonalUncertainty P policies entries) =
      secondMargin P (f0f1AntidiagonalUncertainty P policies entries) :=
  diagonal_antidiagonal_same_secondMargin P (f0f1Support P policies entries)
    (f0Case P policies entries) (f1Case P policies entries)
    (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_different_joint_sets :
    f0f1DiagonalUncertainty P policies entries ≠
      f0f1AntidiagonalUncertainty P policies entries :=
  diagonal_ne_antidiagonal P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries) (f0Case_ne_f1Case P policies entries)

theorem f0f1_same_inner_possible :
    (∀ s ∈ f0f1DiagonalUncertainty P policies entries,
        s.possible = fun _ => f0f1Support P policies entries) ∧
      (∀ s ∈ f0f1AntidiagonalUncertainty P policies entries,
        s.possible = fun _ => f0f1Support P policies entries) :=
  diagonal_antidiagonal_same_inner_possible P (f0f1Support P policies entries)
    (f0Case P policies entries) (f1Case P policies entries)
    (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_unit_amounts :
    (∀ s ∈ f0f1DiagonalUncertainty P policies entries, ∀ i, s.amounts i = 1) ∧
      (∀ s ∈ f0f1AntidiagonalUncertainty P policies entries, ∀ i, s.amounts i = 1) :=
  diagonal_antidiagonal_unit_amounts P (f0f1Support P policies entries)
    (f0Case P policies entries) (f1Case P policies entries)
    (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_encoded_distinct_and_decodes :
    encodeMixtureSet P (f0f1DiagonalUncertainty P policies entries) ≠
        encodeMixtureSet P (f0f1AntidiagonalUncertainty P policies entries) ∧
      decodeMixtureSet P (encodeMixtureSet P (f0f1DiagonalUncertainty P policies entries)) =
        f0f1DiagonalUncertainty P policies entries ∧
      decodeMixtureSet P (encodeMixtureSet P (f0f1AntidiagonalUncertainty P policies entries)) =
        f0f1AntidiagonalUncertainty P policies entries :=
  diagonal_antidiagonal_encoded_distinct_and_decodes P (f0f1Support P policies entries)
    (f0Case P policies entries) (f1Case P policies entries)
    (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)
    (f0Case_ne_f1Case P policies entries)

/-- **The decisive two-constituent statement.**  The diagonal and antidiagonal uncertainty sets
have identical first and second constituent marginals, identical per-constituent inner possibility
channels, and equal positive unit amounts, but different outer joint sets. -/
theorem f0f1_decisive_uncertainty :
    firstMargin P (f0f1DiagonalUncertainty P policies entries) =
        firstMargin P (f0f1AntidiagonalUncertainty P policies entries) ∧
      secondMargin P (f0f1DiagonalUncertainty P policies entries) =
        secondMargin P (f0f1AntidiagonalUncertainty P policies entries) ∧
      f0f1DiagonalUncertainty P policies entries ≠
        f0f1AntidiagonalUncertainty P policies entries ∧
      (∀ s ∈ f0f1DiagonalUncertainty P policies entries,
        s.possible = fun _ => f0f1Support P policies entries) ∧
      (∀ s ∈ f0f1AntidiagonalUncertainty P policies entries,
        s.possible = fun _ => f0f1Support P policies entries) ∧
      (∀ s ∈ f0f1DiagonalUncertainty P policies entries, ∀ i, s.amounts i = 1) ∧
      (∀ s ∈ f0f1AntidiagonalUncertainty P policies entries, ∀ i, s.amounts i = 1) :=
  ⟨f0f1_same_firstMargin P policies entries,
    f0f1_same_secondMargin P policies entries,
    f0f1_different_joint_sets P policies entries,
    (f0f1_same_inner_possible P policies entries).1,
    (f0f1_same_inner_possible P policies entries).2,
    (f0f1_unit_amounts P policies entries).1,
    (f0f1_unit_amounts P policies entries).2⟩



theorem f0f1_decisive_encoding :
    encodeMixtureSet P (f0f1DiagonalUncertainty P policies entries) ≠
        encodeMixtureSet P (f0f1AntidiagonalUncertainty P policies entries) ∧
      decodeMixtureSet P (encodeMixtureSet P (f0f1DiagonalUncertainty P policies entries)) =
        f0f1DiagonalUncertainty P policies entries ∧
      decodeMixtureSet P (encodeMixtureSet P (f0f1AntidiagonalUncertainty P policies entries)) =
        f0f1AntidiagonalUncertainty P policies entries :=
  f0f1_encoded_distinct_and_decodes P policies entries



theorem f0f1_encoded_cells_differ :
    (assembleJointCase P (f0Case P policies entries)).2.cells ≠
      (assembleJointCase P (f1Case P policies entries)).2.cells :=
  assembleJoint_witness_cells_differ (LigandId := P.ligandId)
    (LigandKind := P.ligandKind) (FragmentId := P.fragmentId)
    (FragmentKind := P.fragmentKind) (State := P.state) (Framework := P.framework)
    (BaseName := P.baseName) (Numbering := P.numbering) (Locant := P.locant)
    (Prefix := P.prefix) policies entries





def f0f1CorrelatedForward : MixtureSample P :=
  correlatedForward P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)

/-- The concrete swapped amount-correlated sample: the state/amount pairing is swapped over the
occurrence indices, while the species-level amounts `1` and `3` are preserved. -/
def f0f1CorrelatedSwapped : MixtureSample P :=
  correlatedSwapped P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)



def f0f1AmountCorrelatedUncertainty : Set (MixtureSample P) :=
  amountCorrelatedUncertainty P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_amount_correlated_with_state :
    (f0f1CorrelatedForward P policies entries).cases (0 : Fin 2) = f0Case P policies entries ∧
      (f0f1CorrelatedForward P policies entries).amounts (0 : Fin 2) = 1 ∧
      (f0f1CorrelatedForward P policies entries).cases (1 : Fin 2) = f1Case P policies entries ∧
      (f0f1CorrelatedForward P policies entries).amounts (1 : Fin 2) = 3 ∧
      (f0f1CorrelatedSwapped P policies entries).cases (0 : Fin 2) = f1Case P policies entries ∧
      (f0f1CorrelatedSwapped P policies entries).amounts (0 : Fin 2) = 3 ∧
      (f0f1CorrelatedSwapped P policies entries).cases (1 : Fin 2) = f0Case P policies entries ∧
        (f0f1CorrelatedSwapped P policies entries).amounts (1 : Fin 2) = 1 :=
  amount_correlated_with_state P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_amountCorrelated_members_distinct :
    encodeSample P (f0f1CorrelatedForward P policies entries) ≠
      encodeSample P (f0f1CorrelatedSwapped P policies entries) :=
  amountCorrelated_members_distinct P (f0f1Support P policies entries)
    (f0Case P policies entries) (f1Case P policies entries)
    (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_amountCorrelated_decodes_exact :
    decodeMixtureSet P (encodeMixtureSet P (f0f1AmountCorrelatedUncertainty P policies entries)) =
      f0f1AmountCorrelatedUncertainty P policies entries :=
  amountCorrelated_decode_exact P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)




def f0f1RepeatedCaseSample : MixtureSample P :=
  repeatedCaseSample P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)

theorem f0f1_repeated_cases_equal :
    (f0f1RepeatedCaseSample P policies entries).cases (0 : Fin 2) =
      (f0f1RepeatedCaseSample P policies entries).cases (1 : Fin 2) :=
  repeatedCaseSample_cases_equal P (f0f1Support P policies entries)
    (f0Case P policies entries) (f1Case P policies entries)
    (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)



theorem f0f1_repeated_occurrence_identity :
    speciesWeighted P (f0f1RepeatedCaseSample P policies entries)
        (occurrenceIndicator (f0f1RepeatedCaseSample P policies entries) (0 : Fin 2)) = 1 ∧
      speciesWeighted P (f0f1RepeatedCaseSample P policies entries)
        (occurrenceIndicator (f0f1RepeatedCaseSample P policies entries) (1 : Fin 2)) = 3 :=
  ⟨repeatedCaseSample_occurrence_zero P (f0f1Support P policies entries)
      (f0Case P policies entries) (f1Case P policies entries)
      (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries),
    repeatedCaseSample_occurrence_one P (f0f1Support P policies entries)
      (f0Case P policies entries) (f1Case P policies entries)
      (f0Case_mem_f0f1Support P policies entries) (f1Case_mem_f0f1Support P policies entries)⟩

/-! ## A concrete one-label core, for varying constituent and atom-label counts -/

/-- The empty-interaction graph on one atom label. -/
def smallGraph : FiniteAtomInteractionHypergraph (Fin 1) where
  atomData := fun _ => witnessAtom
  interactions := []
  arity_ge_two := by
    intro edge member
    simp at member
  participants_nodup := by
    intro edge member
    simp at member

/-- The physical evidence on one atom label: no optional coordinates, no paths, no bands, no
roles and no diagram rows.  The path and band channels are empty here independently of the atom
count; an atom count does not determine path or band counts. -/
def smallCore : OrganicMolecularEvidence (Fin 1) where
  graph := smallGraph
  conformation := fun _ => F0Fun (Delta.vertex (d := 2) (0 : Fin 3))
  rationalPositions_valid := by
    intro positions present
    cases present
  electronic_unpaired := by
    intro evidence present
    cases present
  paths_graph_eq := by
    intro family present
    cases present
  paths_conformation_eq := by
    intro family present
    cases present
  bands_graph_eq := by
    intro bands present
    cases present
  bands_conformation_eq := by
    intro bands present
    cases present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  diagram_valid := by
    intro row member
    simp at member

/-- The one-label spatial request: the small core with no cells. -/
def smallSpatial : OrganicSpatialMolecularEvidence (Fin 1) where
  core := smallCore
  cells := []
  occurrence_bound := by
    intro cell member
    simp at member
  anchors_mem := by
    intro cell member
    simp at member
  anchor_value := by
    intro cell member
    simp at member
  role_reference := by
    intro cell member
    simp at member

/-- The explicit atom enumeration of the one-label core. -/
def smallEnumeration : Fin 1 ≃ Fin (Fintype.card (Fin 1)) :=
  Fintype.equivFin (Fin 1)

/-- The reconstructed source of the one-label core is structurally well formed. -/
theorem smallSource_structurallyWellFormed :
    (recoveredSource smallCore smallEnumeration).StructurallyWellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [recoveredSource, recoveredAcyclicSource, coreFiniteSource, smallCore,
      OrganicFiniteSource.encode] using
      smallCore.graph.encode_structurallyWellFormed smallEnumeration
  · simp [recoveredSource, recoveredAcyclicSource, coreFiniteSource, smallCore,
      OrganicFiniteSource.encode, AuthoritativeChemicalInput.SpatialIndicesWellFormed]
  · simp [recoveredSource, recoveredAcyclicSource, coreFiniteSource, smallCore,
      OrganicFiniteSource.encode, AuthoritativeChemicalInput.DiagramIndicesWellFormed]

/-- A concrete joint request with one atom label. -/
def smallRequest : JointRequest (Fin 1) P.ligandId P.ligandKind P.fragmentId P.fragmentKind
    P.state P.framework P.baseName P.numbering P.locant P.prefix where
  policies := policies
  spatial := smallSpatial
  enumeration := smallEnumeration
  source_well_formed := smallSource_structurallyWellFormed
  entries := []

/-- The one-label joint case, with its atom-label count retained as data. -/
def smallCase : JointCase P :=
  ⟨1, smallRequest P policies⟩

@[simp] theorem smallCase_nat : (smallCase P policies).1 = 1 := rfl

theorem smallCase_mem_singleton :
    smallCase P policies ∈ ({smallCase P policies} : Set (JointCase P)) := by
  simp

/-- The one-constituent, one-label sample used to exhibit varying shape. -/
def varyingSmallSample : MixtureSample P :=
  singleCaseSample P (smallCase P policies) {smallCase P policies}
    (smallCase_mem_singleton P policies)

theorem varyingSmallSample_caseCounts :
    caseCounts P (varyingSmallSample P policies) = {1} := by
  change caseCounts P (singleCaseSample P (smallCase P policies) {smallCase P policies}
    (smallCase_mem_singleton P policies)) = {1}
  simp [singleCaseSample_caseCounts, smallCase_nat]

theorem f0f1PairSample_caseCounts :
    caseCounts P (f0f1PairSample P policies entries) = {3} := by
  change caseCounts P (pairSample P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries)) = {3}
  exact pairSample_caseCounts P (f0f1Support P policies entries) (f0Case P policies entries)
    (f1Case P policies entries) (f0Case_mem_f0f1Support P policies entries)
    (f1Case_mem_f0f1Support P policies entries) 3 (f0Case_nat P policies entries)
    (f1Case_nat P policies entries)

theorem f0f1PairSample_constituentCount :
    constituentCount P (f0f1PairSample P policies entries) = 2 := rfl

theorem varyingSmallSample_constituentCount :
    constituentCount P (varyingSmallSample P policies) = 1 := rfl

/-- One outer set containing both a two-constituent sample with three atom labels per occurrence
and a one-constituent sample with one atom label. -/
def varyingShapeSet : Set (MixtureSample P) :=
  {f0f1PairSample P policies entries, varyingSmallSample P policies}

/-- The encoded concrete pair sample. -/
def f0f1EncodedSample : NativeMixtureSample P :=
  encodeSample P (f0f1PairSample P policies entries)

/-- The encoded one-label sample. -/
def varyingSmallEncodedSample : NativeMixtureSample P :=
  encodeSample P (varyingSmallSample P policies)

theorem varyingShape_both_mem :
    f0f1PairSample P policies entries ∈ varyingShapeSet P policies entries ∧
      varyingSmallSample P policies ∈ varyingShapeSet P policies entries := by
  simp [varyingShapeSet]

theorem f0f1_and_small_shape_ne :
    (f0f1PairSample P policies entries).k ≠ (varyingSmallSample P policies).k ∨
      caseCounts P (f0f1PairSample P policies entries) ≠
        caseCounts P (varyingSmallSample P policies) := by
  left
  change constituentCount P (f0f1PairSample P policies entries) ≠
    constituentCount P (varyingSmallSample P policies)
  rw [f0f1PairSample_constituentCount, varyingSmallSample_constituentCount]
  norm_num

/-- The two differently shaped samples remain distinct after encoding and both occur in the encoded
outer set.  This is the varying-`k` and varying-`n` statement inside one outer set. -/
theorem varyingShape_encoded_members_distinct_and_present :
    f0f1EncodedSample P policies entries ∈
        encodeMixtureSet P (varyingShapeSet P policies entries) ∧
      varyingSmallEncodedSample P policies ∈
        encodeMixtureSet P (varyingShapeSet P policies entries) ∧
      f0f1EncodedSample P policies entries ≠ varyingSmallEncodedSample P policies := by
  refine encoded_members_distinct_of_shape_ne P (varyingShapeSet P policies entries) ?_ ?_ ?_
  · simp [varyingShapeSet]
  · simp [varyingShapeSet]
  · exact f0f1_and_small_shape_ne P policies entries

/-- The varying-shape outer set is recovered exactly by decoding. -/
theorem varyingShape_decode_exact :
    decodeMixtureSet P (encodeMixtureSet P (varyingShapeSet P policies entries)) =
      varyingShapeSet P policies entries :=
  decodeMixtureSet_encodeMixtureSet P (varyingShapeSet P policies entries)

end FixtureArguments

end

end OrganicStereoJointAuthorityCellMixtures
end TetraStereo.OneCenter
