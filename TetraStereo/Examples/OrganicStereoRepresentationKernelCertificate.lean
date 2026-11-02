/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoEmbeddedBands
import TetraStereo.OneCenter.OrganicStereoCorrelatedInformation
import TetraStereo.OneCenter.OrganicStereoRingConformationView
import TetraStereo.OneCenter.OrganicStereoMolarComposition
import TetraStereo.OneCenter.OrganicStereoMolecularAutomorphism
import TetraStereo.OneCenter.OrganicStereoCyclicCarrierTransport
import TetraStereo.OneCenter.OrganicStereoAxialFrameEncoding
import TetraStereo.OneCenter.OrganicStereoDonorOccurrenceEncoding
import TetraStereo.OneCenter.OrganicStereoEmbeddedBondPaths
import TetraStereo.OneCenter.OrganicStereoResidueIncidence

set_option autoImplicit false















































namespace TetraStereo
namespace OneCenter

open IUPACDrawing2006.ST6
open OrganicStereoEmbeddedBands
open MolarComposition
open SemanticMolecule
open scoped BigOperators

/-! ## Concrete witnesses used by the examples -/

/-- A concrete carbon atom (atomic number 6). -/
private def carbonAtom : SemanticAtom :=
  { element := { atomicNumber := 6, positive := by norm_num, atMost118 := by norm_num } }

/-- Three carbon atoms joined by the three binary bonds of a triangle. -/
private def ringMolecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom, carbonAtom]
    interactions :=
      [ { participants := [0, 1], kind := .covalent 1 }
      , { participants := [1, 2], kind := .covalent 1 }
      , { participants := [2, 0], kind := .covalent 1 } ] }

private theorem ringMolecule_wellFormed : ringMolecule.StructurallyWellFormed := by
  rw [← SemanticMolecule.structurallyWellFormed?_eq_true_iff]
  rfl

/-- The source input carrying the triangular molecule, with no optional evidence channels. -/
private def ringInput : AuthoritativeChemicalInput :=
  { molecule := ringMolecule, spatial? := none, diagram? := none }

/-- The certified triangular source. -/
private def ringSource : CertifiedAuthoritativeChemicalInput :=
  { input := ringInput
    structurallyWellFormed := by
      refine ⟨ringMolecule_wellFormed, ?_, ?_⟩
      · trivial
      · trivial }

private theorem ringBond_zero_one : P93AuthorityBinaryBond ringInput 0 1 := by
  refine ⟨by decide, ?_⟩
  exact ⟨{ participants := [0, 1], kind := .covalent 1 },
    by simp [ringInput, ringMolecule],
    by simp [P93AuthorityBinaryInteractionKind],
    Or.inl rfl⟩

private theorem ringBond_one_two : P93AuthorityBinaryBond ringInput 1 2 := by
  refine ⟨by decide, ?_⟩
  exact ⟨{ participants := [1, 2], kind := .covalent 1 },
    by simp [ringInput, ringMolecule],
    by simp [P93AuthorityBinaryInteractionKind],
    Or.inl rfl⟩

private theorem ringBond_two_zero : P93AuthorityBinaryBond ringInput 2 0 := by
  refine ⟨by decide, ?_⟩
  exact ⟨{ participants := [2, 0], kind := .covalent 1 },
    by simp [ringInput, ringMolecule],
    by simp [P93AuthorityBinaryInteractionKind],
    Or.inl rfl⟩

private theorem ringPath : P93AuthorityConnectedPath ringInput [0, 1, 2, 0] := by
  refine ⟨ringBond_zero_one, ?_⟩
  refine ⟨ringBond_one_two, ?_⟩
  refine ⟨ringBond_two_zero, ?_⟩
  trivial

private theorem ringAtomsBounded : P93AuthorityAtomsBounded ringInput [0, 1, 2] := by
  intro atom member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

/-- A concrete closed triangular traversal of the certified source. -/
private def ringTraversal : OrganicRingTraversal ringSource :=
  { ringAtoms := [0, 1, 2]
    closedCycle :=
      ⟨by decide, by decide, ringAtomsBounded, ⟨0, [1, 2], rfl, ringPath⟩⟩ }

/-- The all-zero real conformation of the triangular source. -/
private def ringZeroConformation : SourceConformation ringSource := fun _ => 0

/-- The corresponding source-indexed real geometry. -/
private def zeroGeometry : RealSourceGeometry ringSource :=
  RealSourceGeometry.ofConformation ringSource ringZeroConformation

/-- The canonical full real ring-conformation view of the triangular traversal. -/
private def ringView : OrganicRingConformationView ringSource ringTraversal :=
  OrganicRingConformationView.ofGeometry ringSource ringTraversal zeroGeometry

/-- A concrete two-component composition with amounts 1 and 2. -/
private def binaryComposition : Composition (Fin 2) Bool :=
  Composition.binary false true 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- A concrete equimolar racemic pair under `Bool.not`, with equal amounts 1 and 1. -/
private def racemateComposition : Composition (Fin 2) Bool :=
  Composition.binary false true 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- A concrete three-component composition with a repeated species (`false` occurs twice). -/
private def threeComposition : Composition (Fin 3) Bool where
  species i := i.val = 1
  amount i := (i.val : ℝ) + 1
  amount_nonneg i := by positivity
  total_pos := by
    show (0 : ℝ) < ∑ i : Fin 3, ((i.val : ℝ) + 1)
    rw [Fin.sum_univ_three]
    norm_num

private theorem threeComposition_total : threeComposition.total = 6 := by
  show (∑ i : Fin 3, ((i.val : ℝ) + 1)) = 6
  rw [Fin.sum_univ_three]
  norm_num

private theorem racemate_witness :
    Composition.IsRacemate Bool.not false true racemateComposition := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · rfl
  · rfl

/-- A two-atom molecule with no interactions, used for relabelling laws. -/
private def airMolecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom], interactions := [] }

/-- The atom swap of the two indistinguishable atoms. -/
private def swapAtoms : Equiv.Perm (Fin airMolecule.atomCount) :=
  Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩

/-- The product permutation carrying the atom swap and the unique interaction-occurrence
permutation. -/
private def swapCarrier : PermutationCarrier airMolecule := (swapAtoms, 1)

private theorem swapCarrier_isAutomorphism :
    airMolecule.IsAutomorphism swapCarrier := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom
    fin_cases atom <;> rfl
  · intro interaction
    exact Fin.elim0 interaction
  · intro interaction
    exact Fin.elim0 interaction

/-- A constant role colouring, respected by the atom swap. -/
private def constantRoles : RoleAssignment airMolecule Bool Bool :=
  { atomRole := fun _ => true, interactionRole := fun _ => false }

/-- A role colouring that distinguishes the two atoms, hence is not respected by the swap. -/
private def distinguishingRoles : RoleAssignment airMolecule Nat Bool :=
  { atomRole := fun atom => atom.val, interactionRole := fun _ => false }

private theorem swap_constantRoles_compatible :
    constantRoles.Compatible swapCarrier := by
  refine ⟨?_, ?_⟩ <;> intro _ <;> rfl

private theorem swap_distinguishingRoles_not_compatible :
    ¬ distinguishingRoles.Compatible swapCarrier := by
  intro compatible
  have flipped := compatible.1 ⟨0, by decide⟩
  simp [distinguishingRoles, swapCarrier, swapAtoms] at flipped
  have contradiction : (2 : ℕ) = 1 := flipped
  omega

/-- A concrete atom-indexed rational coordinate assignment. -/
private def rationalPositions : AtomAssignment airMolecule ℚ :=
  fun atom => (atom.val : ℚ)

/-! ## OrganicStereoEmbeddedBands -/

/-- For an embedded band, equal strip images are exactly seam-related parameters. -/
example (band : Band) (first second : RibbonDomain) :
    band.strip first = band.strip second ↔ SeamRel band.mode first second :=
  Band.strip_eq_iff_seamRel band first second

/-- A band strip is never injective on the whole parameter square. -/
example (band : Band) : ¬ Function.Injective band.strip :=
  Band.not_injective_strip band

/-- Ambient transport composes. -/
example (band : Band) (first second : real3 ≃ₜ real3) :
    (band.transport first).transport second = band.transport (first.trans second) :=
  Band.transport_transport band first second

/-- Ambient transport respects the identity homeomorphism. -/
example (band : Band) :
    band.transport (Homeomorph.refl real3) = band :=
  Band.transport_refl band

/-- Attached ledger positions coincide exactly when their parameters are seam-related. -/
example {source : CertifiedAuthoritativeChemicalInput} (bandData : CertifiedPartialBand source)
    (first second : Fin bandData.attachmentCount) :
    bandData.geometry.conformation (bandData.atom first) =
        bandData.geometry.conformation (bandData.atom second) ↔
      SeamRel bandData.band.mode (bandData.parameter first) (bandData.parameter second) :=
  bandData.attached_eq_iff_seamRel first second

/-- A partial-band ledger retains the whole source: every atom of the source is still indexed,
including atoms with no ledger entry. -/
example {source : CertifiedAuthoritativeChemicalInput} (bandData : CertifiedPartialBand source)
    {atom : SemanticAtom} (member : atom ∈ source.input.molecule.atoms) :
    ∃ index : CertifiedSourceIndex bandData.sourceOf,
      sourceAtom bandData.sourceOf index = atom :=
  bandData.offband_atom_present member

/-- Transport of a partial band moves the whole supplied source conformation, including every
off-ledger atom, and not merely the attached entries. -/
example {source : CertifiedAuthoritativeChemicalInput} (bandData : CertifiedPartialBand source)
    (motion : real3 ≃ₜ real3) (index : CertifiedSourceIndex source) :
    (bandData.transport motion).geometry.conformation index =
      motion (bandData.geometry.conformation index) :=
  bandData.transport_geometry_conformation motion index

/-- A mode-determined proposition cannot be a reflection-antisymmetric handedness sign. -/
example (band : Band) :
    ¬ ReflectionAntisymmetricSign (fun candidate : Band => candidate.mode = SeamMode.twisted) band :=
  twisted_not_reflectionAntisymmetric band

/-! ## OrganicStereoCorrelatedInformation -/

/-- A diagram with a relative scope and a racemic scope on its two statements. -/
private def sampleDiagram : DiagramConfiguration :=
  { bonds := [{ source := 0, target := 1, style := .plain, scope := .relative 0 }]
    atomConfigurations := [{ atom := 2, parity := .clockwise, scope := .racemic 1 }] }

/-- Joint information attached to that diagram. -/
private def sampleInfo : CorrelatedInformation Unit :=
  CorrelatedInformation.ofDiagram ConfigurationKnowledge.experimentallyUnknown sampleDiagram {()}

/-- Attaching a diagram retains exactly the supplied knowledge tag, the original diagram and the
derived statement-scope summary. -/
example :
    sampleInfo.knowledge = ConfigurationKnowledge.experimentallyUnknown ∧
      sampleInfo.diagram? = some sampleDiagram ∧
      sampleInfo.scopes = sampleDiagram.scopeList :=
  CorrelatedInformation.ofDiagram_recovers _ _ _

/-- Restriction preserves the tag and the scope summary exactly. -/
example (info : CorrelatedInformation Bool) (constraint : Set Bool) :
    (info.restrict constraint).knowledge = info.knowledge ∧
      (info.restrict constraint).scopes = info.scopes ∧
      (info.restrict constraint).diagram? = info.diagram? :=
  CorrelatedInformation.restrict_recovers_metadata info constraint

/-- Successive restrictions combine by intersection. -/
example (info : CorrelatedInformation Bool) (first second : Set Bool) :
    (info.restrict first).restrict second = info.restrict (first ∩ second) :=
  CorrelatedInformation.restrict_restrict_eq info first second

/-- A certified claim survives restriction only when the restricted evidence remains nonempty. -/
example {info : CorrelatedInformation Bool} {property : Bool → Prop} {constraint : Set Bool}
    (certified : info.CertifiedEntails property)
    (nonempty : (info.possible ∩ constraint).Nonempty) :
    (info.restrict constraint).CertifiedEntails property :=
  CorrelatedInformation.certifiedEntails_restrict certified nonempty

/-- A concrete state-type equivalence used for transport examples. -/
private def boolSwap : Bool ≃ Bool := Equiv.swap false true

/-- Transporting by an equivalence and then by its inverse recovers the original joint information
including its exact possible-state set. -/
example (info : CorrelatedInformation Bool) :
    (info.transport boolSwap).transport boolSwap.symm = info :=
  CorrelatedInformation.transport_symm_transport boolSwap info

/-- No function of the two marginals reconstructs an arbitrary joint possible set. -/
example :
    ¬ ∃ reconstruct : Set Bool → Set Bool → Set (Bool × Bool),
        ∀ possible : Set (Bool × Bool),
          reconstruct (TwoCoordinateCorrelation.firstProjection possible)
            (TwoCoordinateCorrelation.secondProjection possible) = possible :=
  TwoCoordinateCorrelation.no_reconstruction_from_projections

/-- The joint representation retains the correlation that marginals lose. -/
example :
    TwoCoordinateCorrelation.diagonalInformation.possible ≠
        TwoCoordinateCorrelation.antiDiagonalInformation.possible ∧
      TwoCoordinateCorrelation.productOfProjections
          TwoCoordinateCorrelation.diagonalInformation.possible =
        TwoCoordinateCorrelation.productOfProjections
          TwoCoordinateCorrelation.antiDiagonalInformation.possible :=
  TwoCoordinateCorrelation.joint_information_retains_correlation

/-- The diagonal joint information entails its coordinate correlation. -/
example :
    TwoCoordinateCorrelation.diagonalInformation.Entails
      (fun point : Bool × Bool => point.1 = point.2) :=
  TwoCoordinateCorrelation.diagonalInformation_entails_correlation

/-- The diagonal joint representation is non-vacuous, so its correlation claim is not vacuous. -/
example : TwoCoordinateCorrelation.diagonalInformation.Consistent :=
  ⟨(true, true), by
    simp [TwoCoordinateCorrelation.diagonalInformation, TwoCoordinateCorrelation.diagonal]⟩

/-! ## OrganicStereoRingConformationView -/

/-- Distinct cycle positions name distinct source atoms. -/
example : Function.Injective ringTraversal.indexAt :=
  ringTraversal.indexAt_injective

/-- Every ring atom's exact full real point occurs in the view, and every viewed point comes from
an actual ring atom. -/
example :
    (∀ (atom : Nat) (member : atom ∈ ringTraversal.ringAtoms),
        ringView.geometry.conformation (ringTraversal.atomIndex atom member) ∈
          ringView.points) ∧
      (∀ point ∈ ringView.points,
        ∃ (atom : Nat) (member : atom ∈ ringTraversal.ringAtoms),
          ringView.geometry.conformation (ringTraversal.atomIndex atom member) = point) :=
  ringView.points_sound_and_complete

/-- A viewed point is the exact three-dimensional real conformation value at the viewed atom, not a
derived scalar torsion or angle summary. -/
example (position : Fin ringTraversal.ringAtoms.length) :
    ringView.point position =
      ringView.geometry.conformation (ringView.atomAt position) :=
  ringView.point_eq_conformation position

/-- The view retains the whole source-indexed real geometry. -/
example :
    ringView.fullGeometry = ringView.geometry :=
  ringView.fullGeometry_eq

/-- A cyclic shift rotates the complete ordered atom enumeration. -/
example (shift : ℕ) :
    (ringView.rotate shift).atomOrder = ringView.atomOrder.rotate shift :=
  ringView.atomOrder_rotate shift

/-- Rotation by a shift and by its complementary shift returns the original complete view. -/
example (shift : ℕ) :
    (ringView.rotate shift).rotate
        (ringTraversal.ringAtoms.length - shift % ringTraversal.ringAtoms.length) =
      ringView :=
  ringView.rotate_inverse shift

/-- An independent atom enumeration can be inverted on the full source-indexed conformation. -/
example :
    MolecularConformation.reindex (Equiv.refl (SourceAtomIndex ringSource)).symm
        (ringView.enumeratedConformation (Equiv.refl (SourceAtomIndex ringSource))) =
      ringView.geometry.conformation :=
  ringView.enumeratedConformation_inverse (Equiv.refl (SourceAtomIndex ringSource))

/-! ## OrganicStereoMolarComposition -/

/-- The binary constructor recovers both species and the total amount. -/
example : binaryComposition.species (0 : Fin 2) = false ∧
    binaryComposition.species (1 : Fin 2) = true ∧
    binaryComposition.total = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Composition.binary_species_zero false true 1 2
      (by norm_num) (by norm_num) (by norm_num)
  · exact Composition.binary_species_one false true 1 2
      (by norm_num) (by norm_num) (by norm_num)
  · change (Composition.binary false true 1 2
      (by norm_num) (by norm_num) (by norm_num)).total = 3
    rw [Composition.binary_total]
    norm_num

/-- Normalized mole fractions sum to one. -/
example : ∑ i : Fin 2, binaryComposition.fraction i = 1 :=
  Composition.sum_fraction_eq_one binaryComposition

/-- Positive rescaling multiplies the total amount but leaves every normalized fraction unchanged. -/
example (i : Fin 2) :
    (Composition.scale 2 (by norm_num) binaryComposition).fraction i =
      binaryComposition.fraction i :=
  Composition.fraction_scale 2 (by norm_num) binaryComposition i

/-- Reindexing components preserves the normalized fraction at every corresponding component. -/
example (i : Fin 2) :
    (Composition.reindex (Equiv.swap (0 : Fin 2) 1) binaryComposition).fraction
        (Equiv.swap (0 : Fin 2) 1 i) = binaryComposition.fraction i :=
  Composition.fraction_reindex (Equiv.swap (0 : Fin 2) 1) binaryComposition i

/-- An odd observable on the supplied mirror pair has zero amount-weighted response in a
racemate. -/
example (observable : Bool → ℝ) (odd : observable true = -observable false) :
    Composition.amountWeighted racemateComposition observable = 0 :=
  Composition.racemate_amountWeighted_eq_zero racemate_witness observable odd

/-- Zero excess alone does not make a racemate when the explicit mirror relation is absent. -/
example : ¬ Composition.IsRacemate id false true racemateComposition := by
  apply Composition.zeroExcess_not_racemate_without_mirror
    (mirror := id) (first := false) (second := true) (c := racemateComposition)
  · simp [racemateComposition]
  · simp [racemateComposition]
  · rfl
  · simp [racemateComposition]

/-- Aggregation on the finite occurring support preserves the total amount. -/
example : (Composition.aggregateOnSupport threeComposition).total = 6 := by
  rw [Composition.total_aggregateOnSupport]
  exact threeComposition_total

/-- Finite-support species aggregation preserves every amount-weighted observable. -/
example (observable : Bool → ℝ) :
    Composition.amountWeighted threeComposition observable =
      Composition.amountWeighted (Composition.aggregateOnSupport threeComposition) observable :=
  Composition.amountWeighted_aggregateOnSupport threeComposition observable

/-! ## OrganicStereoMolecularAutomorphism -/

/-- The two-atom swap is a molecular automorphism. -/
example : swapCarrier ∈ airMolecule.Aut :=
  swapCarrier_isAutomorphism

/-- The automorphism subgroup has identity, composition and inverse laws. -/
example (first second : PermutationCarrier airMolecule)
    (firstMember : first ∈ airMolecule.Aut) (secondMember : second ∈ airMolecule.Aut) :
    (1 : PermutationCarrier airMolecule) ∈ airMolecule.Aut ∧
      first * second ∈ airMolecule.Aut ∧ first⁻¹ ∈ airMolecule.Aut :=
  ⟨(airMolecule.Aut).one_mem, (airMolecule.Aut).mul_mem firstMember secondMember,
    (airMolecule.Aut).inv_mem firstMember⟩

/-- The atom projection is multiplicative. -/
example (first second : airMolecule.Aut) :
    airMolecule.atomPerm (first * second) =
      airMolecule.atomPerm first * airMolecule.atomPerm second :=
  airMolecule.atomPerm_mul first second

/-- Every automorphism preserves every stored atom exactly. -/
example (element : airMolecule.Aut) (atom : Fin airMolecule.atomCount) :
    airMolecule.atoms.get (airMolecule.atomPerm element atom) =
      airMolecule.atoms.get atom :=
  airMolecule.atom_preserving element atom

/-- The atom swap lies in the role-enriched subgroup for a constant colouring. -/
example : swapCarrier ∈ airMolecule.RoleEnrichedAut constantRoles :=
  (SemanticMolecule.mem_roleEnrichedAut_iff airMolecule constantRoles swapCarrier).mpr
    ⟨swapCarrier_isAutomorphism, swap_constantRoles_compatible⟩

/-- Role enrichment only shrinks the automorphism group. -/
example (element : PermutationCarrier airMolecule)
    (member : element ∈ airMolecule.RoleEnrichedAut constantRoles) :
    element ∈ airMolecule.Aut :=
  SemanticMolecule.roleEnrichedAut_le_aut airMolecule constantRoles member

/-- A colouring that distinguishes the two atoms excludes the swap, showing that the role subgroup
is a genuine fixed-colour restriction rather than a relabelling of roles. -/
example : ¬ distinguishingRoles.Compatible swapCarrier :=
  swap_distinguishingRoles_not_compatible

/-- Relabelling coordinates along an atom permutation only moves points between labels; the
occupied point set is unchanged.  This is relabelling, not a rigid motion. -/
example (permutation : Equiv.Perm (Fin airMolecule.atomCount)) :
    Set.range (SemanticMolecule.AtomAssignment.relabel rationalPositions permutation) =
      Set.range rationalPositions :=
  SemanticMolecule.AtomAssignment.range_relabel rationalPositions permutation

end OneCenter
end TetraStereo







-- OrganicStereoEmbeddedBands: conditional band laws and partial-band source retention.
assert_kernel_only TetraStereo.OneCenter.OrganicStereoEmbeddedBands.Band.strip_eq_iff_seamRel
assert_kernel_only TetraStereo.OneCenter.OrganicStereoEmbeddedBands.Band.not_injective_strip
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedBands.CertifiedPartialBand.offband_atom_present

-- OrganicStereoCorrelatedInformation: joint sets, restriction and non-reconstruction.
assert_kernel_only
  TetraStereo.OneCenter.CorrelatedInformation.ofDiagram_recovers
assert_kernel_only
  TetraStereo.OneCenter.TwoCoordinateCorrelation.no_reconstruction_from_projections
assert_kernel_only
  TetraStereo.OneCenter.TwoCoordinateCorrelation.joint_information_retains_correlation

-- OrganicStereoRingConformationView: full three-dimensional points, not a torsion summary.
assert_kernel_only
  TetraStereo.OneCenter.OrganicRingConformationView.points_sound_and_complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicRingConformationView.point_eq_conformation
assert_kernel_only
  TetraStereo.OneCenter.OrganicRingConformationView.rotate_inverse

-- OrganicStereoMolarComposition: finite aggregation and supplied-mirror qualification.
assert_kernel_only
  TetraStereo.OneCenter.MolarComposition.Composition.sum_fraction_eq_one
assert_kernel_only
  TetraStereo.OneCenter.MolarComposition.Composition.racemate_amountWeighted_eq_zero
assert_kernel_only
  TetraStereo.OneCenter.MolarComposition.Composition.zeroExcess_not_racemate_without_mirror

-- OrganicStereoMolecularAutomorphism: group laws and the fixed-colour refinement, not chirality.
assert_kernel_only
  TetraStereo.OneCenter.SemanticMolecule.isAutomorphism_mul
assert_kernel_only
  TetraStereo.OneCenter.SemanticMolecule.roleEnrichedAut_le_aut
assert_kernel_only
  TetraStereo.OneCenter.SemanticMolecule.AtomAssignment.range_relabel

-- OrganicStereoCyclicCarrierTransport: enumeration change and normalized reversal.
assert_kernel_only
  TetraStereo.OneCenter.P93AuthorityAtomReindexing.mapOfEnumerationChange_bound_iff
assert_kernel_only
  TetraStereo.OneCenter.P93AuthorityAtomReindexing.ofEnumerationChange
assert_kernel_only
  TetraStereo.OneCenter.P93AuthorityVonBaeyerSystem.mechanicallyValidFor_renameReversed

-- OrganicStereoAxialFrameEncoding: direct semantic/binary occurrence construction, not a parser
-- bridge; the generic frame does not by itself force an axis bond.
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAxialFrameEncoding.p93AuthorityBinaryBond_of_attached
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAxialFrameEncoding.actualAxialIncidence_iff_frameValidity_and_sourceWitnesses
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoAxialFrameEncoding.genericFrame_not_forces_axisBond

-- OrganicStereoDonorOccurrenceEncoding: recorded denticity, per-occurrence binding, and the
-- explicit non-recovery boundary for donor identities.
assert_kernel_only
  TetraStereo.OneCenter.DonorOccurrenceEncoding.recordedLigandDenticity_eq_card_of_certificate
assert_kernel_only
  TetraStereo.OneCenter.DonorOccurrenceEncoding.DonorLedger.occurrence_preserves_identities
assert_kernel_only
  TetraStereo.OneCenter.DonorOccurrenceEncoding.no_donor_identity_recovery

-- OrganicStereoEmbeddedBondPaths: exact encode/decode recovery and homeomorphism action; the
-- source-only projection is not injective.
assert_kernel_only TetraStereo.OneCenter.BondPathTable.decode_encode
assert_kernel_only TetraStereo.OneCenter.BondPathTable.mapHomeomorph
assert_kernel_only TetraStereo.OneCenter.sourceProjection_not_injective

-- OrganicStereoResidueIncidence: source binding and metadata adapters.
assert_kernel_only TetraStereo.OneCenter.ResidueIncidenceLedger.link_source_correct
assert_kernel_only TetraStereo.OneCenter.RawResidueIncidence.toLedger_resolve_roundtrip
assert_kernel_only TetraStereo.OneCenter.GlycolipidCitationAdapter.Binding.metadata_retained
