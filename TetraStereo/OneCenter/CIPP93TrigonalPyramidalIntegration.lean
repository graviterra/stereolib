import TetraStereo.OneCenter.CIPP93NoncarbonTetrahedralNormalization
import TetraStereo.OneCenter.CIPObservedGeometryAssignmentConformance
import TetraStereo.OneCenter.CIPMoleculeDigraphConformance
import TetraStereo.OneCenter.ProductionCIPTwoViewSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.TrigonalPyramidal

/-!
# P-93.3 trigonal-pyramidal integration

P-93.3.3.2 and P-93.3.4.1 turn a three-coordinate trigonal pyramid into a notional
tetrahedron by adjoining one lowest-priority phantom atom.  A written `@`/`@@` carrier or a typed
TPY-3 geometry observation supplies the spatial evidence; connectivity alone does not.

This module states the main-group written-configuration frame independently, proves that the
production frame is exactly its three physical ligands plus the phantom, connects the P/S oxido
root convention to a proposition rather than an implementation Boolean, and exposes a certified
P-93-normalized graph-plus-observed-geometry entry point.
-/

/-- Main-group elements represented by the written three-coordinate phantom convention.  The
polyhedral observation API itself remains element-independent. -/
def ElementSupportsPhantom : Element → Prop
  | .N | .O | .P | .As | .S | .Se | .Sb | .Te | .Bi => True
  | _ => False

instance elementSupportsPhantomDecidable (element : Element) :
    Decidable (ElementSupportsPhantom element) := by
  cases element <;> simp only [ElementSupportsPhantom] <;> infer_instance

/-- The production element gate is exactly the independently enumerated P-93.3 main-group
phantom family. -/
theorem centreElementUsesLonePair_eq_true_iff (element : Element) :
    RawMolecule.centreElementUsesLonePair element = true ↔
      ElementSupportsPhantom element := by
  cases element <;>
    simp [RawMolecule.centreElementUsesLonePair, ElementSupportsPhantom]

/-- The repository's written lone-pair convention places the P-93.3 phantom at the implicit-H
position relative to the three physical ligands.  Introduction history distinguishes component
roots from ring closures; unknown history retains the legacy fallback.  This ordering carries
syntax parity, not chemical priority, and is not an externally settled OpenSMILES requirement. -/
def writtenPhantomFrame (mol : RawMolecule) (center : Nat) : List Nat :=
  if mol.hydrogenHasPreceding center then
    match mol.writtenNeighbors center with
    | [] => [mol.atomCount]
    | first :: rest => first :: mol.atomCount :: rest
  else
    mol.atomCount :: mol.writtenNeighbors center

/-- Independent applicability evidence for the written-configuration route.  In particular,
`tetrahedral?` is required: the same three bonds without spatial evidence do not establish a
trigonal-pyramidal stereogenic unit. -/
structure WrittenConfigurationFrame (mol : RawMolecule) (center : Nat) where
  atom : AtomSpec
  atom_eq : mol.atomAt? center = some atom
  parity : TetrahedralInputParity
  parity_eq : atom.tetrahedral? = some parity
  element_supported : ElementSupportsPhantom atom.element
  three_physical : (mol.writtenNeighbors center).length = 3

/-- Production materializes exactly the independently specified notional tetrahedral frame. -/
theorem ligandsWithLonePair_eq_writtenPhantomFrame
    (mol : RawMolecule) (center : Nat) (frame : WrittenConfigurationFrame mol center) :
    mol.ligandsWithLonePair center = writtenPhantomFrame mol center := by
  have supported : RawMolecule.centreElementUsesLonePair frame.atom.element = true :=
    (centreElementUsesLonePair_eq_true_iff frame.atom.element).2 frame.element_supported
  unfold RawMolecule.ligandsWithLonePair writtenPhantomFrame
  rw [frame.atom_eq]
  simp [supported, frame.three_physical]
  rfl

/-- The notional frame has the required four positions. -/
theorem writtenPhantomFrame_length
    (mol : RawMolecule) (center : Nat)
    (three : (mol.writtenNeighbors center).length = 3) :
    (writtenPhantomFrame mol center).length = 4 := by
  unfold writtenPhantomFrame
  split
  · cases physical_eq : mol.writtenNeighbors center with
    | nil => simp [physical_eq] at three
    | cons first rest =>
        have rest_length : rest.length = 2 := by
          simpa [physical_eq] using three
        simp [rest_length]
  · simp [three]

/-- The phantom position is present in every notional frame, independently of traversal
direction. -/
theorem atomCount_mem_writtenPhantomFrame (mol : RawMolecule) (center : Nat) :
    mol.atomCount ∈ writtenPhantomFrame mol center := by
  unfold writtenPhantomFrame
  split
  · cases mol.writtenNeighbors center <;> simp
  · simp

/-- Removing the phantom from the notional frame recovers only genuine written neighbours. -/
theorem mem_writtenNeighbors_of_mem_writtenPhantomFrame_of_ne
    (mol : RawMolecule) (center ligand : Nat)
    (member : ligand ∈ writtenPhantomFrame mol center)
    (not_phantom : ligand ≠ mol.atomCount) :
    ligand ∈ mol.writtenNeighbors center := by
  unfold writtenPhantomFrame at member
  split at member
  · cases physical_eq : mol.writtenNeighbors center with
    | nil => simp [physical_eq, not_phantom] at member
    | cons first rest =>
        simp [physical_eq, not_phantom] at member ⊢
        exact member
  · simp [not_phantom] at member
    exact member

/-- Exact written-neighbour admission makes the four-position frame duplicate-free: no physical
atom can equal the out-of-range phantom sentinel. -/
theorem writtenPhantomFrame_nodup
    (mol : RawMolecule) (center : Nat) (frame : WrittenConfigurationFrame mol center)
    (exact : mol.WrittenNeighborExact) :
    (writtenPhantomFrame mol center).Nodup := by
  have center_bound : center < mol.atomCount :=
    listGet?_eq_some_implies_lt mol.atoms center frame.atom
      (by simpa [RawMolecule.atomAt?] using frame.atom_eq)
  have physical_exact := RawMolecule.WrittenNeighborExact.at mol exact
    (⟨center, center_bound⟩ : Fin mol.atomCount)
  have physical_nodup : (mol.writtenNeighbors center).Nodup := physical_exact.1
  have phantom_not_physical : mol.atomCount ∉ mol.writtenNeighbors center := by
    intro member
    have bounded := physical_exact.2.1 mol.atomCount member
    omega
  unfold writtenPhantomFrame
  split
  · cases physical_eq : mol.writtenNeighbors center with
    | nil => simp
    | cons first rest =>
        simp [physical_eq] at physical_nodup phantom_not_physical ⊢
        have first_ne_phantom : first ≠ mol.atomCount := by
          intro equal
          exact phantom_not_physical.1 equal.symm
        exact ⟨⟨first_ne_phantom, physical_nodup.1⟩,
          ⟨phantom_not_physical.2, physical_nodup.2⟩⟩
  · exact List.nodup_cons.mpr ⟨phantom_not_physical, physical_nodup⟩

/-- Complete finite shape certificate for a written P-93.3 center. -/
structure NotionalTetrahedralFrameCertificate
    (mol : RawMolecule) (center : Nat) : Prop where
  production_eq : mol.ligandsWithLonePair center = writtenPhantomFrame mol center
  four_positions : (writtenPhantomFrame mol center).length = 4
  phantom_present : mol.atomCount ∈ writtenPhantomFrame mol center
  no_duplicates : (writtenPhantomFrame mol center).Nodup
  physical_sound : ∀ ligand,
    ligand ∈ writtenPhantomFrame mol center → ligand ≠ mol.atomCount →
      ligand ∈ mol.writtenNeighbors center

theorem writtenConfigurationFrame_certificate
    (mol : RawMolecule) (center : Nat) (frame : WrittenConfigurationFrame mol center)
    (exact : mol.WrittenNeighborExact) :
    NotionalTetrahedralFrameCertificate mol center where
  production_eq := ligandsWithLonePair_eq_writtenPhantomFrame mol center frame
  four_positions := writtenPhantomFrame_length mol center frame.three_physical
  phantom_present := atomCount_mem_writtenPhantomFrame mol center
  no_duplicates := writtenPhantomFrame_nodup mol center frame exact
  physical_sound := fun ligand =>
    mem_writtenNeighbors_of_mem_writtenPhantomFrame_of_ne mol center ligand

/-- The same three-coordinate frame is rejected by descriptor-free connectivity perception.
Thus broadening the explicit-configuration element gate cannot promote a planar three-coordinate
center in the absence of written or geometric stereochemical evidence. -/
theorem connectivityOnlyTetrahedralLigands?_eq_none_of_writtenConfigurationFrame
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (center : Nat)
    (frame : WrittenConfigurationFrame mol center) :
    connectivityOnlyTetrahedralLigands? result mol center = none := by
  cases produced : connectivityOnlyTetrahedralLigands? result mol center with
  | none => rfl
  | some ligands =>
      have admitted :
          (connectivityOnlyTetrahedralLigands? result mol center).isSome := by
        simp [produced]
      have independent :=
        (connectivityOnlyTetrahedralLigands?_isSome_iff_independentFrame
          result mol center).1 admitted
      rcases independent with ⟨_, _, _, _, four_physical⟩
      exfalso
      have impossible : (3 : Nat) = 4 := frame.three_physical.symm.trans four_physical
      omega

/-! ## P/S oxido root edge -/

/-- Independent proposition denoted by the production P/S oxido-root detector. -/
def OxidoRootEdge (mol : RawMolecule) (center oxygen : Nat) : Prop :=
  ∃ centerSpec oxygenSpec,
    mol.atomAt? center = some centerSpec ∧
      mol.atomAt? oxygen = some oxygenSpec ∧
      (centerSpec.element = .P ∨ centerSpec.element = .S) ∧
      oxygenSpec.element = .O ∧
      mol.bondOrder center oxygen = 2

@[simp] theorem isTrigonalPyramidalOxidoRootEdge_eq_true_iff
    (mol : RawMolecule) (center oxygen : Nat) :
    mol.isTrigonalPyramidalOxidoRootEdge center oxygen = true ↔
      OxidoRootEdge mol center oxygen := by
  unfold RawMolecule.isTrigonalPyramidalOxidoRootEdge OxidoRootEdge
  cases center_eq : mol.atomAt? center with
  | none => simp
  | some centerSpec =>
      cases oxygen_eq : mol.atomAt? oxygen with
      | none => simp
      | some oxygenSpec =>
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
          constructor
          · rintro ⟨⟨center_element, oxygen_element⟩, order_eq⟩
            exact ⟨centerSpec, oxygenSpec, rfl, rfl,
              center_element, oxygen_element, order_eq⟩
          · rintro ⟨observedCenter, observedOxygen, observedCenter_eq,
              observedOxygen_eq, center_element, oxygen_element, order_eq⟩
            simp only [Option.some.injEq] at observedCenter_eq observedOxygen_eq
            subst observedCenter
            subst observedOxygen
            exact ⟨⟨center_element, oxygen_element⟩, order_eq⟩

/-- The constitutional hierarchy contains one root ligand edge, not a double-bond duplicate, for
every independently characterized P/S oxido root. -/
theorem canonicalHierarchyBond_eq_one_of_oxidoRootEdge
    (mol : RawMolecule) (center oxygen : Nat)
    (edge : OxidoRootEdge mol center oxygen) :
    mol.canonicalHierarchyBond center oxygen center oxygen = 1 := by
  have detected : mol.isTrigonalPyramidalOxidoRootEdge center oxygen = true :=
    (isTrigonalPyramidalOxidoRootEdge_eq_true_iff mol center oxygen).2 edge
  have distinct : center ≠ oxygen := by
    intro equal
    subst oxygen
    rcases edge with ⟨_, _, _, _, _, _, order_eq⟩
    simp [RawMolecule.bondOrder] at order_eq
  simp [RawMolecule.canonicalHierarchyBond, RawMolecule.IsRootPair, distinct, detected]

/-! ## Certified P-93 graph-plus-geometry entry point -/

open BlueBookP93.NoncarbonTetrahedra.Production

/-- Complete certified P-93 normalization followed by the observed-geometry analyzer. -/
def analyzeCertifiedRawP93WithObservedGeometry
    (mol : RawMolecule) (cycles : List AromaticCycle)
    (admissible : mol.Admissible) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (masses : mol.Rule2MassesKnown)
    (observations : IndexedCIPGeometryObservations) : List StereoAssignment :=
  analyzeCertifiedNormalizedWithObservedGeometry
    (certifyP93 mol cycles admissible writtenExact valence masses) observations

/-- Executable checked entry point when proof arguments are not already in scope. -/
def analyzeRawP93WithObservedGeometry?
    (mol : RawMolecule) (cycles : List AromaticCycle)
    (observations : IndexedCIPGeometryObservations) : Option (List StereoAssignment) :=
  (normalizeRawMoleculeP93Certified? mol cycles).map fun certified =>
    analyzeCertifiedNormalizedWithObservedGeometry certified observations

/-- Inserting the P-93.2 quotient preserves successful admission for a finite source molecule
with valid chemistry and internally consistent source-introduction metadata. -/
theorem analyzeRawP93WithObservedGeometry?_exists
    (mol : RawMolecule) (cycles : List AromaticCycle)
    (admissible : mol.Admissible) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (masses : mol.Rule2MassesKnown)
    (observations : IndexedCIPGeometryObservations)
    (introduction : mol.introductionPredecessorsValid? = true) :
    ∃ assignments,
      analyzeRawP93WithObservedGeometry? mol cycles observations = some assignments := by
  obtain ⟨certified, certified_eq⟩ :=
    normalizeRawMoleculeP93Certified?_exists mol cycles admissible writtenExact valence masses
      introduction
  refine ⟨analyzeCertifiedNormalizedWithObservedGeometry certified observations, ?_⟩
  simp [analyzeRawP93WithObservedGeometry?, certified_eq]

/-- Every assignment emitted by the certified P-93 graph-plus-geometry entry point satisfies the
independent native-or-observed assignment judgment. -/
theorem analyzeCertifiedRawP93WithObservedGeometry_member_judged
    (mol : RawMolecule) (cycles : List AromaticCycle)
    (admissible : mol.Admissible) (writtenExact : mol.WrittenNeighborExact)
    (valence : mol.ValenceOK) (masses : mol.Rule2MassesKnown)
    (observations : IndexedCIPGeometryObservations) (assignment : StereoAssignment)
    (present : assignment ∈ analyzeCertifiedRawP93WithObservedGeometry mol cycles
      admissible writtenExact valence masses observations) :
    IndependentlyJudgedCertifiedGeometryStereoAssignment
      (certifyP93 mol cycles admissible writtenExact valence masses)
      observations assignment := by
  exact analyzeCertifiedNormalizedWithObservedGeometry_member_judged
    (certifyP93 mol cycles admissible writtenExact valence masses)
    observations assignment present

/-- Executable-success form of the same end-to-end soundness theorem. -/
theorem analyzeRawP93WithObservedGeometry?_member_judged
    (mol : RawMolecule) (cycles : List AromaticCycle)
    (observations : IndexedCIPGeometryObservations)
    (assignments : List StereoAssignment) (assignment : StereoAssignment)
    (produced : analyzeRawP93WithObservedGeometry? mol cycles observations = some assignments)
    (present : assignment ∈ assignments) :
    ∃ certified,
      normalizeRawMoleculeP93Certified? mol cycles = some certified ∧
      IndependentlyJudgedCertifiedGeometryStereoAssignment certified observations assignment := by
  unfold analyzeRawP93WithObservedGeometry? at produced
  cases certified_eq : normalizeRawMoleculeP93Certified? mol cycles with
  | none => simp [certified_eq] at produced
  | some certified =>
      have assignments_eq :
          analyzeCertifiedNormalizedWithObservedGeometry certified observations = assignments := by
        simpa [certified_eq] using produced
      refine ⟨certified, rfl, ?_⟩
      exact analyzeCertifiedNormalizedWithObservedGeometry_member_judged certified observations
        assignment (by rw [assignments_eq]; exact present)

end BlueBookP93.TrigonalPyramidal
end TetraStereo.OneCenter
