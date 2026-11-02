import TetraStereo.OneCenter.P93MolecularFullereneFlagExtension

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

noncomputable section

open P94MolecularRingCycleScheduler

/-!
# Exact numbered fullerene-cage packages

This module is the source-data boundary for the three concrete P-93.5.6 cages.  A package supplies
atoms in source locant order, one canonical undirected edge table, and the face cycles in a
coherent orientation.  Faces are data: this compiler deliberately does not claim that every
chordless five- or six-cycle is facial.

The small executable check below validates only the finite numbered tables and exact agreement of
the edge table with the positive bonds induced by the proposed carrier.  Full molecular and
topological validity is retained as an explicit proof field.  Consequently the compiler never
searches permutations, enumerates flag words, or hides a fullerene-recognition theorem inside a
large decision procedure.
-/

/-- Reusable source-only cage data.  Position `i` in `atomsByLocant` is source locant `i + 1`;
atom identifiers themselves remain the zero-based identifiers of `RawMolecule`.  Every edge is
written once in increasing endpoint order.  `faces` contains the supplied facial cycles with a
chosen global orientation. -/
structure MolecularFullereneNumberedCagePackage where
  atomsByLocant : List ℕ
  edgeTable : List (ℕ × ℕ)
  faces : List (List ℕ)
  deriving DecidableEq, Repr

namespace MolecularFullereneNumberedCagePackage

/-- The physical cage carrier, independent of the source locant ordering. -/
def carrier (package : MolecularFullereneNumberedCagePackage) : Finset ℕ :=
  package.atomsByLocant.toFinset

/-- Attach row-specific substitution and descriptor evidence without copying cage data. -/
def toConfigurationInput
    (package : MolecularFullereneNumberedCagePackage)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence) :
    MolecularFullereneConfigurationInput :=
  { carrier := package.carrier
    faces := package.faces
    substitutionTest := substitutionTest
    descriptorEvidence := descriptorEvidence }

/-- Exact finite table meaning.  Locants and canonical edges contain no duplicates, every listed
edge has bounded increasing endpoints, and the list is exactly the positive molecular bond set
induced by the numbered carrier. -/
def TableJudgment
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage) : Prop :=
  package.atomsByLocant.Nodup ∧
    package.edgeTable.Nodup ∧
    (∀ edge ∈ package.edgeTable,
      edge.1 < edge.2 ∧ edge.1 ∈ package.carrier ∧ edge.2 ∈ package.carrier) ∧
    package.edgeTable.toFinset =
      molecularFullereneCageEdges molecule package.carrier

/-- Memory-bounded executable check for the finite source tables.  It examines the supplied lists
and the `|V|²` induced-pair universe only; it does not enumerate graph permutations or paths. -/
def tableAccepted
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage) : Bool :=
  decide package.atomsByLocant.Nodup &&
    decide package.edgeTable.Nodup &&
    package.edgeTable.all (fun edge => decide
      (edge.1 < edge.2 ∧ edge.1 ∈ package.carrier ∧ edge.2 ∈ package.carrier)) &&
    decide (package.edgeTable.toFinset =
      molecularFullereneCageEdges molecule package.carrier)

/-- The finite table check has no acceptance gap. -/
@[simp] theorem tableAccepted_eq_true_iff
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage) :
    package.tableAccepted molecule = true ↔ package.TableJudgment molecule := by
  simp [tableAccepted, TableJudgment, List.all_eq_true, and_assoc]

/-- A topology-only downstream record used to state the reusable certificate once.  Its Boolean
payloads make no chemical claim and are never emitted; `compile` replaces them with row data. -/
def topologyInput (package : MolecularFullereneNumberedCagePackage) :
    MolecularFullereneConfigurationInput :=
  package.toConfigurationInput
    { parentChiral := false
      originalDerivativeChiral := false
      allSubstituentsReplacedByAchiralTChiral := false
      substitutionPatternWithActualIdentitiesChiral := false
      hasChiralSubstituent := false }
    { cageNumberingKind := none
      cageTurn := none
      everyChiralSubstituentHasCIP := false }

/-- Proof-carrying admission of one numbered cage package.  `oriented` validates the complete
existing carrier judgment: carbon bounds, cubicity, connectivity, supplied chordless 5/6 faces,
face uniqueness and coverage, twelve pentagons, the required hexagon and Euler counts, two faces
per positive cage bond, and opposite traversal of those two faces. -/
structure Certificate
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage) : Prop where
  tableCheck : package.tableAccepted molecule = true
  oriented : OrientedMolecularFullereneFaceMapJudgment molecule package.topologyInput

/-- Construct the proof-carrying boundary from its exact independent meanings. -/
def Certificate.ofJudgments
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (tableJudged : package.TableJudgment molecule)
    (oriented : OrientedMolecularFullereneFaceMapJudgment molecule package.topologyInput) :
    package.Certificate molecule :=
  { tableCheck := (package.tableAccepted_eq_true_iff molecule).2 tableJudged
    oriented := oriented }

/-- Recover the independent table meaning from an accepted certificate. -/
theorem Certificate.tableJudgment
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule) : package.TableJudgment molecule :=
  (package.tableAccepted_eq_true_iff molecule).1 certificate.tableCheck

/-- Compile the shared cage with the row-specific P-93.5.6 payload. -/
def Certificate.compile
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (_certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence) :
    MolecularFullereneConfigurationInput :=
  package.toConfigurationInput substitutionTest descriptorEvidence

/-- Topological admission is independent of the row-specific substitution/descriptor payload. -/
theorem Certificate.compile_oriented
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence) :
    OrientedMolecularFullereneFaceMapJudgment molecule
      (certificate.compile molecule package substitutionTest descriptorEvidence) := by
  rcases certificate.oriented with ⟨carrierJudged, coherent⟩
  refine ⟨?_, ?_⟩
  · exact
      { minimumSize := carrierJudged.minimumSize
        carbonAtoms := carrierJudged.carbonAtoms
        cubic := carrierJudged.cubic
        connected := carrierJudged.connected
        facesNodup := carrierJudged.facesNodup
        facesValid := carrierJudged.facesValid
        facesCover := carrierJudged.facesCover
        twelvePentagons := carrierJudged.twelvePentagons
        hexagonCount := carrierJudged.hexagonCount
        twoFacesPerCageEdge := carrierJudged.twoFacesPerCageEdge
        eulerCharacteristicTwo := carrierJudged.eulerCharacteristicTwo }
  · exact coherent

/-- The compiled cage satisfies the complete pre-existing molecular carrier judgment. -/
theorem Certificate.compile_carrier
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence) :
    MolecularFullereneCarrierJudgment molecule
      (certificate.compile molecule package substitutionTest descriptorEvidence) :=
  (certificate.compile_oriented molecule package substitutionTest descriptorEvidence).1

/-- Every positive compiled cage bond is covered by exactly two supplied faces. -/
theorem Certificate.positiveBond_faceCount
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence)
    (left right : ℕ)
    (leftPresent : left ∈ package.carrier) (rightPresent : right ∈ package.carrier)
    (ordered : left < right) (bond : 0 < molecule.bondOrder left right) :
    package.faces.countP (fun face => decide (IsNamedCycleEdge face left right)) = 2 := by
  exact ((certificate.compile_carrier molecule package substitutionTest descriptorEvidence)
    |>.twoFacesPerCageEdge left leftPresent right rightPresent ordered).mp bond

/-- The two incidences of every positive compiled cage bond traverse it once in each direction. -/
theorem Certificate.positiveBond_oppositeOrientations
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence)
    (left right : ℕ)
    (leftPresent : left ∈ package.carrier) (rightPresent : right ∈ package.carrier)
    (ordered : left < right) (bond : 0 < molecule.bondOrder left right) :
    package.faces.countP
          (fun face => decide (IsForwardNamedCycleEdge face left right)) = 1 ∧
      package.faces.countP
          (fun face => decide (IsForwardNamedCycleEdge face right left)) = 1 := by
  exact (certificate.compile_oriented molecule package substitutionTest descriptorEvidence).2
    left leftPresent right rightPresent ordered bond

/-- Honest flag-spanning projection.  Saturation is an explicit theorem input; this constructor
does not infer it merely from cubicity or spherical face counts. -/
def Certificate.toDeduplicatedFlagSpanningCertificate
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence)
    (source : MolecularFullereneCarrierAtom
        (certificate.compile molecule package substitutionTest descriptorEvidence) ×
      MolecularFullereneCarrierAtom
        (certificate.compile molecule package substitutionTest descriptorEvidence))
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (spanning : MolecularFullereneDeduplicatedFlagSpanningJudgment molecule
      (certificate.compile molecule package substitutionTest descriptorEvidence) source) :
    MolecularFullereneDeduplicatedFlagSpanningCertificate molecule
      (certificate.compile molecule package substitutionTest descriptorEvidence) :=
  { oriented := certificate.compile_oriented molecule package substitutionTest descriptorEvidence
    source := source
    sourceBond := sourceBond
    spanning := spanning }

/-- Checked flag-spanning projection using only the existing deduplicated bonded-dart BFS.  Its
fuel is `molecularFullereneFlagStateBound`, bounded by `|V|²`; no flag-word universe occurs. -/
def Certificate.toDeduplicatedFlagSpanningCertificateOfChecked
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence)
    (source : MolecularFullereneCarrierAtom
        (certificate.compile molecule package substitutionTest descriptorEvidence) ×
      MolecularFullereneCarrierAtom
        (certificate.compile molecule package substitutionTest descriptorEvidence))
    (sourceBond : 0 < molecule.bondOrder source.1.1 source.2.1)
    (accepted : decide (MolecularFullereneDeduplicatedFlagSpanningJudgment molecule
      (certificate.compile molecule package substitutionTest descriptorEvidence) source) = true) :
    MolecularFullereneDeduplicatedFlagSpanningCertificate molecule
      (certificate.compile molecule package substitutionTest descriptorEvidence) :=
  MolecularFullereneDeduplicatedFlagSpanningCertificate.ofChecked molecule
    (certificate.compile molecule package substitutionTest descriptorEvidence)
    (certificate.compile_oriented molecule package substitutionTest descriptorEvidence)
    source sourceBond accepted

/-- The checked boundary retains the already-proved quadratic state bound. -/
theorem Certificate.flagStateBound_le_square
    (molecule : RawMolecule) (package : MolecularFullereneNumberedCagePackage)
    (certificate : package.Certificate molecule)
    (substitutionTest : FullereneSubstitutionTest)
    (descriptorEvidence : FullereneDescriptorEvidence) :
    molecularFullereneFlagStateBound molecule
        (certificate.compile molecule package substitutionTest descriptorEvidence) ≤
      package.carrier.card * package.carrier.card := by
  simpa [Certificate.compile, toConfigurationInput] using
    molecularFullereneFlagStateBound_le_square molecule
      (certificate.compile molecule package substitutionTest descriptorEvidence)

end MolecularFullereneNumberedCagePackage

end

end BlueBookP93.Cyclic
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneNumberedCagePackage.Certificate.compile_oriented
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneNumberedCagePackage.Certificate.positiveBond_oppositeOrientations
assert_kernel_only
  TetraStereo.OneCenter.BlueBookP93.Cyclic.MolecularFullereneNumberedCagePackage.Certificate.toDeduplicatedFlagSpanningCertificate
