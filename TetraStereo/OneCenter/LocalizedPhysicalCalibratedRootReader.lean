import TetraStereo.OneCenter.LocalizedPhysicalSparseRootReader
import TetraStereo.OneCenter.LocalizedRootZLabelSignEquivalence
import TetraStereo.OneCenter.TerminalTwinConfigurationGauge
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.MultiCenter.RootedBranchTerminalTwinCompletion
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
















































namespace TetraStereo
namespace OneCenter
namespace CertifiedLocalizedCIPInput

open TetraStereo.OneCenter
open TerminalTwinConfigurationGauge
open RootedTetrahedralBranchSymmetry

/-! ## Center-level physical predicates -/

/-- Physical terminal twins at a distinguished center.  This is exactly the graph-theoretic
`HasTerminalTwins` predicate: two distinct actual atoms whose only neighbour is the center and
which have equal atomic number, mass, formal charge and bond order.  It mentions no frame,
coordinate, label or comparison. -/
def ActualPhysicalTerminalTwinCenter
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (center : m.Center) : Prop :=
  ∃ a b : input.Atom, TerminalTwinConfigurationGauge.TerminalTwinPair m center a b

/-- Physical calibrated-center data in the molecule's own canonical ligand enumeration:
injective ligand atomic numbers, exact source coordinates on those ligands, nonzero oriented volume
of the canonical points, and physical volume sign equal to the configuration sign at the center.
This is the positive root-`Z`-rigid branch.  It contains no frame, slot permutation, label, model or
automorphism sign law. -/
def ActualPhysicalCalibratedCenter
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (center : m.Center) : Prop :=
  ∃ pointAt : Fin 4 → CartesianPoint3,
    Function.Injective (fun i => m.mol.atomZ (m.ligandAtomAt center i)) ∧
      (∀ i, input.spatialPointAt? (m.ligandAtomAt center i) = some (pointAt i)) ∧
        CartesianPoint3.orientedVolume
            (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0 ∧
          rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
            m.configurationSign cfg center

/-- **The global strong physical domain.**  One fixed physical multi-center molecule `m` on the
certified atoms, one fixed configuration `cfg`, and one fixed physical root `root`.  All fields are
propositions: the graph equation and, at every non-root center, a physical twin/calibration
dichotomy.  The root is unconstrained. -/
structure ActualGlobalPhysicalCalibratedDomain
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (cfg : m.Configuration)
    (root : m.Center) : Prop where
  /-- The physical molecule has exactly the certified input graph. -/
  graphEq : m.mol = input.moleculeGraph
  /-- Every non-root center is either a physical terminal twin or a calibrated positive center. -/
  centerCase : ∀ center : m.Center, center ≠ root →
    ActualPhysicalTerminalTwinCenter input m center ∨
      ActualPhysicalCalibratedCenter input m cfg center

/-- In the global domain, a non-root center that is not a physical terminal twin is calibrated. -/
theorem actualPhysicalCalibratedCenter_of_globalDomain
    {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration}
    {root : m.Center}
    (domain : ActualGlobalPhysicalCalibratedDomain input m cfg root)
    {center : m.Center}
    (center_ne_root : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input m center) :
    ActualPhysicalCalibratedCenter input m cfg center := by
  rcases domain.centerCase center center_ne_root with twin | calibrated
  · exact absurd twin notTwin
  · exact calibrated

/-- A calibrated center is never a physical terminal twin: injective ligand atomic numbers
contradict the equal atomic numbers of the twin pair.  This is the center-level form of the fact
that root-`Z` injectivity excludes physical twins. -/
theorem actualPhysicalTerminalTwinCenter_false_of_calibrated
    {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration}
    {center : m.Center}
    (calibrated : ActualPhysicalCalibratedCenter input m cfg center) :
    ¬ ActualPhysicalTerminalTwinCenter input m center := by
  intro twin
  obtain ⟨pointAt, zInjective, _observed, _nonzero, _signEq⟩ := calibrated
  obtain ⟨a, b, pair⟩ := twin
  obtain ⟨slotA, slotAEq⟩ := m.ligandAtomAt_surjective center a pair.adj_ca
  obtain ⟨slotB, slotBEq⟩ := m.ligandAtomAt_surjective center b pair.adj_cb
  have zEq : m.mol.atomZ (m.ligandAtomAt center slotA) =
      m.mol.atomZ (m.ligandAtomAt center slotB) := by
    rw [slotAEq, slotBEq]
    exact pair.z_eq
  have sameSlot : slotA = slotB := zInjective zEq
  have atomsEq : a = b := by
    rw [← slotAEq, ← slotBEq, sameSlot]
  exact pair.ne atomsEq

/-- A physical terminal twin pair is transported by any automorphism of the multi-center
molecule: the images of the two atoms are distinct, have the image center as their unique
neighbour, and carry the same atomic number, mass, charge and bond order. -/
theorem terminalTwinPair_centerPerm
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : MultiCenterMolecule V} {d : m.Center} {a b : V}
    (pair : TerminalTwinConfigurationGauge.TerminalTwinPair m d a b)
    (e : m.Aut) :
    TerminalTwinConfigurationGauge.TerminalTwinPair m (m.centerPerm e d)
      ((e : Equiv.Perm V) a) ((e : Equiv.Perm V) b) := by
  classical
  let eMol : m.mol.Aut :=
    ⟨(e : Equiv.Perm V), MultiCenterMolecule.Aut.mem_molAut m e⟩
  refine
    { ne := ?_
      neighbor_a := ?_
      neighbor_b := ?_
      z_eq := ?_
      mass_eq := ?_
      charge_eq := ?_
      bond_eq := ?_ }
  · intro h
    exact pair.ne ((e : Equiv.Perm V).injective h)
  · ext x
    simp only [MoleculeGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro hx
      have hx' : m.mol.Adj ((e : Equiv.Perm V) a)
          ((e : Equiv.Perm V) ((e⁻¹ : Equiv.Perm V) x)) := by simpa using hx
      have hpre : m.mol.Adj a ((e⁻¹ : Equiv.Perm V) x) :=
        (MoleculeGraph.Aut.adj_iff m.mol eMol a _).1 hx'
      have hmem : ((e⁻¹ : Equiv.Perm V) x) ∈ m.mol.neighborFinset a :=
        (MoleculeGraph.mem_neighborFinset m.mol a _).2 hpre
      rw [pair.neighbor_a, Finset.mem_singleton] at hmem
      calc x = (e : Equiv.Perm V) ((e⁻¹ : Equiv.Perm V) x) := by simp
        _ = (e : Equiv.Perm V) d.1 := by rw [hmem]
        _ = (m.centerPerm e d).1 := rfl
    · intro hx
      have hxval : x = (m.centerPerm e d).1 := hx
      have hadj : m.mol.Adj a d.1 := by
        have hmem : d.1 ∈ m.mol.neighborFinset a := by
          rw [pair.neighbor_a]
          exact Finset.mem_singleton_self d.1
        exact (MoleculeGraph.mem_neighborFinset m.mol a d.1).1 hmem
      have himage : m.mol.Adj ((e : Equiv.Perm V) a) ((e : Equiv.Perm V) d.1) :=
        (MoleculeGraph.Aut.adj_iff m.mol eMol a d.1).2 hadj
      rw [hxval]
      simpa using himage
  · ext x
    simp only [MoleculeGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · intro hx
      have hx' : m.mol.Adj ((e : Equiv.Perm V) b)
          ((e : Equiv.Perm V) ((e⁻¹ : Equiv.Perm V) x)) := by simpa using hx
      have hpre : m.mol.Adj b ((e⁻¹ : Equiv.Perm V) x) :=
        (MoleculeGraph.Aut.adj_iff m.mol eMol b _).1 hx'
      have hmem : ((e⁻¹ : Equiv.Perm V) x) ∈ m.mol.neighborFinset b :=
        (MoleculeGraph.mem_neighborFinset m.mol b _).2 hpre
      rw [pair.neighbor_b, Finset.mem_singleton] at hmem
      calc x = (e : Equiv.Perm V) ((e⁻¹ : Equiv.Perm V) x) := by simp
        _ = (e : Equiv.Perm V) d.1 := by rw [hmem]
        _ = (m.centerPerm e d).1 := rfl
    · intro hx
      have hxval : x = (m.centerPerm e d).1 := hx
      have hadj : m.mol.Adj b d.1 := by
        have hmem : d.1 ∈ m.mol.neighborFinset b := by
          rw [pair.neighbor_b]
          exact Finset.mem_singleton_self d.1
        exact (MoleculeGraph.mem_neighborFinset m.mol b d.1).1 hmem
      have himage : m.mol.Adj ((e : Equiv.Perm V) b) ((e : Equiv.Perm V) d.1) :=
        (MoleculeGraph.Aut.adj_iff m.mol eMol b d.1).2 hadj
      rw [hxval]
      simpa using himage
  · have ha : m.mol.atomZ ((e : Equiv.Perm V) a) = m.mol.atomZ a :=
      MoleculeGraph.Aut.atomZ_eq m.mol eMol a
    have hb : m.mol.atomZ ((e : Equiv.Perm V) b) = m.mol.atomZ b :=
      MoleculeGraph.Aut.atomZ_eq m.mol eMol b
    exact ha.trans (pair.z_eq.trans hb.symm)
  · have ha : m.mol.atomMass ((e : Equiv.Perm V) a) = m.mol.atomMass a :=
      MoleculeGraph.Aut.atomMass_eq m.mol eMol a
    have hb : m.mol.atomMass ((e : Equiv.Perm V) b) = m.mol.atomMass b :=
      MoleculeGraph.Aut.atomMass_eq m.mol eMol b
    exact ha.trans (pair.mass_eq.trans hb.symm)
  · have ha : m.mol.formalCharge ((e : Equiv.Perm V) a) = m.mol.formalCharge a :=
      MoleculeGraph.Aut.formalCharge_eq m.mol eMol a
    have hb : m.mol.formalCharge ((e : Equiv.Perm V) b) = m.mol.formalCharge b :=
      MoleculeGraph.Aut.formalCharge_eq m.mol eMol b
    exact ha.trans (pair.charge_eq.trans hb.symm)
  · have hcenter : (m.centerPerm e d).1 = (e : Equiv.Perm V) d.1 := rfl
    have h1 : m.mol.bond ((e : Equiv.Perm V) d.1) ((e : Equiv.Perm V) a) =
        m.mol.bond d.1 a :=
      MoleculeGraph.Aut.bond_eq m.mol eMol d.1 a
    have h2 : m.mol.bond ((e : Equiv.Perm V) d.1) ((e : Equiv.Perm V) b) =
        m.mol.bond d.1 b :=
      MoleculeGraph.Aut.bond_eq m.mol eMol d.1 b
    rw [hcenter]
    exact h1.trans (pair.bond_eq.trans h2.symm)

/-- Physical terminal twins are invariant under a physical automorphism: `d` has twin terminal
ligands exactly when its image under `e` does. -/
theorem actualPhysicalTerminalTwinCenter_centerPerm_iff
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (e : m.Aut) (d : m.Center) :
    ActualPhysicalTerminalTwinCenter input m (m.centerPerm e d) ↔
      ActualPhysicalTerminalTwinCenter input m d := by
  constructor
  · rintro ⟨a, b, pair⟩
    have transported : TerminalTwinConfigurationGauge.TerminalTwinPair m
        (m.centerPerm (e⁻¹ : m.Aut) (m.centerPerm e d))
        (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) a)
        (((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) b) :=
      terminalTwinPair_centerPerm pair (e⁻¹ : m.Aut)
    have centerEq : m.centerPerm (e⁻¹ : m.Aut) (m.centerPerm e d) = d := by
      apply Subtype.ext
      simp [MultiCenterMolecule.centerPerm]
    refine ⟨((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) a,
      ((e⁻¹ : m.Aut) : Equiv.Perm input.Atom) b, ?_⟩
    simpa [centerEq] using transported
  · rintro ⟨a, b, pair⟩
    exact ⟨(e : Equiv.Perm input.Atom) a, (e : Equiv.Perm input.Atom) b,
      terminalTwinPair_centerPerm pair e⟩

/-- The center-level physical twin predicate is exactly the root-transport completion's
`HasTerminalTwins`. -/
theorem actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (d : m.Center) :
    ActualPhysicalTerminalTwinCenter input m d ↔
      RootedBranchTerminalTwinCompletion.HasTerminalTwins m d :=
  Iff.rfl

/-! ## Source-coordinate lookup and fuel -/


theorem globalCarrierFuel_adequate (input : LocalizedUniversalReference.Input) :
    input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
  dsimp [LocalizedUniversalReference.carrierFuel,
    LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.carrierFuel,
    LocalizedReference.Input.molecule]
  omega

/-! ## Detected multi-center coverage -/

/-- The automatically detected multi-center molecule has exactly the certified graph. -/
theorem detectedMultiCenter_mol (input : CertifiedLocalizedCIPInput) :
    input.detectedMultiCenterMolecule.mol = input.moleculeGraph := rfl

/-- The automatically detected multi-center molecule covers exactly the detected degree-four
candidate set. -/
theorem detectedMultiCenter_centers (input : CertifiedLocalizedCIPInput) :
    input.detectedMultiCenterMolecule.centers = input.tetrahedralCenterSet := rfl

/-- A center of a covering multi-center molecule is an automatically detected tetrahedral
candidate of the certified graph. -/
theorem mem_tetrahedralCenterSet_of_center
    {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom}
    (coverage : m.centers = input.tetrahedralCenterSet)
    (center : m.Center) :
    center.1 ∈ input.tetrahedralCenterSet := by
  rw [← coverage]
  exact center.2

/-- A detected tetrahedral candidate atom belongs to a covering multi-center molecule. -/
theorem mem_centers_of_mem_tetrahedralCenterSet
    {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom}
    (coverage : m.centers = input.tetrahedralCenterSet)
    {atom : input.Atom}
    (candidate : atom ∈ input.tetrahedralCenterSet) :
    atom ∈ m.centers := by
  rw [coverage]
  exact candidate

/-- A covering center is a degree-four center of the certified graph. -/
theorem isTetrahedralCenter_of_center
    {input : CertifiedLocalizedCIPInput}
    {m : MultiCenterMolecule input.Atom}
    (coverage : m.centers = input.tetrahedralCenterSet)
    (center : m.Center) :
    input.moleculeGraph.IsTetrahedralCenter center.1 :=
  (input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp
    (mem_tetrahedralCenterSet_of_center coverage center)

/-- A covering center is an actual real tetrahedral-center node of any occurrence whose current
atom is the center atom.  Provenance is real by the single-bond acyclic carrier theorem. -/
theorem exists_realTetrahedralCenterNode_of_center
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {m : MultiCenterMolecule input.Atom}
    (coverage : m.centers = input.tetrahedralCenterSet)
    (center : m.Center)
    {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetCurrent : target.1.node.current? = some center.1) :
    ∃ center' : input.TetrahedralCenter,
      center'.1 = center.1 ∧ input.RealTetrahedralCenterNode target.1.node center' := by
  refine ⟨⟨center.1, mem_tetrahedralCenterSet_of_center coverage center⟩, rfl, ?_⟩
  exact ⟨input.carrierOccurrence_provenance_real singleBonded acyclic target, targetCurrent⟩

/-- The detected specialization of the global domain.  Both the graph and the coverage fields are
definitional, so only the per-center case remains. -/
def ActualGlobalPhysicalCalibratedDomain.detected
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (centerCase : ∀ center : input.detectedMultiCenterMolecule.Center, center ≠ root →
      ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center ∨
        ActualPhysicalCalibratedCenter input input.detectedMultiCenterMolecule cfg center) :
    ActualGlobalPhysicalCalibratedDomain input input.detectedMultiCenterMolecule cfg root :=
  { graphEq := rfl
    centerCase := centerCase }






abbrev PhysicalCalibratedRootDomain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center) : Prop :=
  ActualGlobalPhysicalCalibratedDomain input input.detectedMultiCenterMolecule cfg root

/-- Constructor for `PhysicalCalibratedRootDomain` from the per-center case. -/
def physicalCalibratedRootDomain_of_centerCase
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (centerCase : ∀ center : input.detectedMultiCenterMolecule.Center, center ≠ root →
      ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule center ∨
        ActualPhysicalCalibratedCenter input input.detectedMultiCenterMolecule cfg center) :
    PhysicalCalibratedRootDomain input cfg root :=
  ActualGlobalPhysicalCalibratedDomain.detected input cfg root centerCase

/-! ## Actual frame, calibration, and spatial reads from one calibrated center -/









theorem exists_frameAndCalibration_of_calibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (calibrated : ActualPhysicalCalibratedCenter input.certified m cfg center) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4))
      (pointAt : Fin 4 → CartesianPoint3),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (m.ligandAtomAt center (alpha i))) ∧
        input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame ∧
        (∀ i, input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
          some (pointAt (alpha i))) ∧
        (∀ i, input.certified.spatialPointAt? (m.ligandAtomAt center i) =
          some (pointAt i)) ∧
        Nonempty (PhysicalFrameCalibration m cfg center alpha (fun i => pointAt (alpha i))) := by
  classical
  obtain ⟨pointAt, zInjective, observed, nonzero, signEq⟩ := calibrated
  obtain ⟨frame, alpha, frameComputed, matchLigand⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
      singleBonded acyclic (globalCarrierFuel_adequate input) target targetCurrent
      m graphEq center rfl
  have separated : input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame := by
    intro left right different equal
    have realLeft : (frame.cursorAt left).occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom :=
      input.certified.carrierOccurrence_provenance_real singleBonded acyclic
        (frame.cursorAt left).occurrence
    have realRight : (frame.cursorAt right).occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom :=
      input.certified.carrierOccurrence_provenance_real singleBonded acyclic
        (frame.cursorAt right).occurrence
    have leftZ : frame.rootAtomicNumberAt input.certified left =
        m.mol.atomZ (m.ligandAtomAt center (alpha left)) := by
      rw [TetraStereo.OneCenter.rootAtomicNumberAt_eq_atomZ_of_real input.certified frame left
        (m.ligandAtomAt center (alpha left)) realLeft (matchLigand left), ← graphEq]
    have rightZ : frame.rootAtomicNumberAt input.certified right =
        m.mol.atomZ (m.ligandAtomAt center (alpha right)) := by
      rw [TetraStereo.OneCenter.rootAtomicNumberAt_eq_atomZ_of_real input.certified frame right
        (m.ligandAtomAt center (alpha right)) realRight (matchLigand right), ← graphEq]
    have atomZEq : m.mol.atomZ (m.ligandAtomAt center (alpha left)) =
        m.mol.atomZ (m.ligandAtomAt center (alpha right)) := by
      rw [← leftZ, ← rightZ]
      exact equal
    exact different (alpha.injective (zInjective atomZEq))
  have spatial : ∀ i : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
        some (pointAt (alpha i)) := by
    intro i
    simp [localizedRerootCursorSpatialPoint?, matchLigand i,
      observed (alpha i)]
  refine ⟨frame, alpha, pointAt, frameComputed, matchLigand, separated, spatial,
    observed, ?_⟩
  exact
    ⟨{ physicalPointAt := pointAt
       calibrated := fun _i => rfl
       nondegenerate := nonzero
       sign_eq := signEq }⟩

/-- **Actual positive chiral reader from a global calibrated center.**

The calibrated center yields the actual frame, canonical slot permutation, root-`Z` separation, a
safe tracked order with zero pseudo comparisons, the actual uppercase chiral reference value, and
the normalized written sign `configurationSign cfg center * permHandedness alpha`. -/
theorem exists_chiral_of_globalCalibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (calibrated : ActualPhysicalCalibratedCenter input.certified m cfg center) :
    ∃ (rs : RS) (tracked : TrackedLocalizedLigandOrder)
      (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4))
      (pointAt : Fin 4 → CartesianPoint3),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
          some (m.ligandAtomAt center (alpha i))) ∧
        input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame ∧
        (∀ i, input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
          some (pointAt (alpha i))) ∧
        (∀ i, input.certified.spatialPointAt? (m.ligandAtomAt center i) =
          some (pointAt i)) ∧
        Nonempty (PhysicalFrameCalibration m cfg center alpha (fun i => pointAt (alpha i))) ∧
        tracked.pseudoComparisons = 0 ∧
        LocalizedUniversalReference.referenceState input target = some (.chiral rs) ∧
        rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointAt (alpha 0)) (pointAt (alpha 1))
            (pointAt (alpha 2)) (pointAt (alpha 3))) =
          m.configurationSign cfg center * permHandedness alpha := by
  classical
  obtain ⟨frame, alpha, pointAt, frameComputed, matchLigand, separated, spatial,
    observed, calibrationNonempty⟩ :=
    exists_frameAndCalibration_of_calibratedCenter input singleBonded acyclic m cfg graphEq
      center target targetCurrent calibrated
  obtain ⟨calibration⟩ := calibrationNonempty
  let pointsAt : Fin 4 → CartesianPoint3 := fun index => pointAt (alpha index)
  have writtenNondegenerate : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 :=
    calibration.written_nondegenerate
  have writtenParity :
      AuthoritativeChemicalInput.RationalTetrahedralInputParity
        [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3]
        (TetraStereo.OneCenter.parityOfVolumeSign
          (TetraStereo.OneCenter.rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)))) :=
    TetraStereo.OneCenter.rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) writtenNondegenerate
  have tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter center.1 :=
    input.certified.isTetrahedralCenter_of_physicalLigandEquiv m graphEq center
  have memCenter : center.1 ∈ input.certified.tetrahedralCenterSet :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet center.1).mpr tetrahedral
  let centerF : input.certified.TetrahedralCenter := ⟨center.1, memCenter⟩
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node centerF :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      targetCurrent⟩
  obtain ⟨tracked, _trackedComputed, pseudoZero, state⟩ :=
    referenceState_reader_eq_chiral_of_physicalFrame
      input noDouble target frame
      (input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed)
      separated centerF centerReal pointsAt spatial
      (TetraStereo.OneCenter.parityOfVolumeSign
        (TetraStereo.OneCenter.rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3))))
      writtenParity
  have signNormalized :
      rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (pointAt (alpha 0)) (pointAt (alpha 1))
          (pointAt (alpha 2)) (pointAt (alpha 3))) =
        m.configurationSign cfg center * permHandedness alpha := by
    simpa [pointsAt] using calibration.sign_eq_configurationSign_mul
  exact ⟨_, tracked, frame, alpha, pointAt, frameComputed, matchLigand, separated,
    spatial, observed, ⟨calibration⟩, pseudoZero, state, signNormalized⟩

/-! ## Terminal-twin refusal at a global center -/

/-- **Physical terminal twins at a global non-root center read `none`.**

The twin pair is read through the physical molecule's graph and moved to the certified graph via
`graphEq`.  The stored root of the occurrence must be a detected tetrahedral center; for a strict
dependency of the top final occurrence this is the fixed global root. -/
theorem referenceState_eq_none_of_globalTwinCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root)
    (twin : ActualPhysicalTerminalTwinCenter input.certified m center) :
    LocalizedUniversalReference.referenceState input target = none := by
  obtain ⟨leftAtom, rightAtom, pair⟩ := twin
  have tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter center.1 :=
    input.certified.isTetrahedralCenter_of_physicalLigandEquiv m graphEq center
  have leftNeighbors : input.certified.moleculeGraph.neighborFinset leftAtom = {center.1} := by
    rw [← graphEq]
    exact pair.neighbor_a
  have rightNeighbors : input.certified.moleculeGraph.neighborFinset rightAtom = {center.1} := by
    rw [← graphEq]
    exact pair.neighbor_b
  have zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom := by
    rw [← graphEq]
    exact pair.z_eq
  have massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom := by
    rw [← graphEq]
    exact pair.mass_eq
  have rootNeLeft : target.1.root ≠ leftAtom :=
    root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral leftNeighbors
  have rootNeRight : target.1.root ≠ rightAtom :=
    root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral rightNeighbors
  exact referenceState_eq_none_of_physical_terminalTwinLeaves
    input singleBonded acyclic noDouble target center.1 leftAtom rightAtom targetCurrent
    tetrahedral leftNeighbors rightNeighbors pair.ne rootNeLeft rootNeRight zEq massEq







theorem actualCandidateCenter_referenceState_none_iff_twin
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (center : m.Center)
    (center_ne_root : center ≠ root)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root) :
    LocalizedUniversalReference.referenceState input target = none ↔
      ActualPhysicalTerminalTwinCenter input.certified m center := by
  constructor
  · intro noneEq
    by_contra notTwin
    have calibrated : ActualPhysicalCalibratedCenter input.certified m cfg center :=
      actualPhysicalCalibratedCenter_of_globalDomain domain center_ne_root notTwin
    obtain ⟨_rs, _tracked, _frame, _alpha, _pointAt, _frameComputed, _match, _separated,
      _spatial, _observed, _calibration, _pseudo, someEq, _sign⟩ :=
      exists_chiral_of_globalCalibratedCenter input singleBonded acyclic noDouble m cfg
        domain.graphEq center target targetCurrent calibrated
    rw [noneEq] at someEq
    cases someEq
  · intro twin
    exact referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble m
      domain.graphEq center target targetCurrent rootTetrahedral twin

/-- **Exact candidate-center dichotomy: actual positive chiral iff no physical terminal twins.**

At the same candidate center, the generated reference state is an actual chiral value exactly when
the center is not a physical terminal twin.  No frame, slot permutation, positivity or desired
label is supplied. -/
theorem actualCandidateCenter_referenceState_chiral_iff_notTwin
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (center : m.Center)
    (center_ne_root : center ≠ root)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter target.1.root) :
    (∃ rs : RS, LocalizedUniversalReference.referenceState input target = some (.chiral rs)) ↔
      ¬ ActualPhysicalTerminalTwinCenter input.certified m center := by
  constructor
  · rintro ⟨_rs, someEq⟩ twin
    have noneEq := referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble
      m domain.graphEq center target targetCurrent rootTetrahedral twin
    rw [noneEq] at someEq
    cases someEq
  · intro notTwin
    have calibrated : ActualPhysicalCalibratedCenter input.certified m cfg center :=
      actualPhysicalCalibratedCenter_of_globalDomain domain center_ne_root notTwin
    obtain ⟨rs, _tracked, _frame, _alpha, _pointAt, _frameComputed, _match, _separated,
      _spatial, _observed, _calibration, _pseudo, state, _sign⟩ :=
      exists_chiral_of_globalCalibratedCenter input singleBonded acyclic noDouble m cfg
        domain.graphEq center target targetCurrent calibrated
    exact ⟨rs, state⟩


theorem actualPhysicalTerminalTwinLeaves_of_globalTwinCenter
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (twin : ActualPhysicalTerminalTwinCenter input.certified m center) :
    ActualPhysicalTerminalTwinLeaves input target := by
  obtain ⟨leftAtom, rightAtom, pair⟩ := twin
  have tetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter center.1 :=
    input.certified.isTetrahedralCenter_of_physicalLigandEquiv m graphEq center
  have leftNeighbors : input.certified.moleculeGraph.neighborFinset leftAtom = {center.1} := by
    rw [← graphEq]
    exact pair.neighbor_a
  have rightNeighbors : input.certified.moleculeGraph.neighborFinset rightAtom = {center.1} := by
    rw [← graphEq]
    exact pair.neighbor_b
  have zEq : input.certified.moleculeGraph.atomZ leftAtom =
      input.certified.moleculeGraph.atomZ rightAtom := by
    rw [← graphEq]
    exact pair.z_eq
  have massEq : input.certified.moleculeGraph.atomMass leftAtom =
      input.certified.moleculeGraph.atomMass rightAtom := by
    rw [← graphEq]
    exact pair.mass_eq
  have chargeEq : input.certified.moleculeGraph.formalCharge leftAtom =
      input.certified.moleculeGraph.formalCharge rightAtom := by
    rw [← graphEq]
    exact pair.charge_eq
  exact ⟨center.1, leftAtom, rightAtom, targetCurrent, tetrahedral, leftNeighbors,
    rightNeighbors, pair.ne, zEq, massEq, chargeEq⟩

/-! ## Strong classification of actual strict dependencies -/
















theorem actualStrictDependency_classification
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = root.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    (ActualPhysicalNoncandidate input cursor.occurrence ∧
        LocalizedUniversalReference.referenceState input cursor.occurrence = none) ∨
      (ActualPhysicalTerminalTwinLeaves input cursor.occurrence ∧
        LocalizedUniversalReference.referenceState input cursor.occurrence = none) ∨
        (∃ (center : m.Center) (rs : RS) (tracked : TrackedLocalizedLigandOrder)
            (frame : input.certified.LocalizedOccurrenceFourLigandFrame
              (LocalizedUniversalReference.carrierFuel input))
            (alpha : Equiv.Perm (Fin 4))
            (pointAt : Fin 4 → CartesianPoint3),
          cursor.occurrence.1.node.current? = some center.1 ∧
            ¬ ActualPhysicalTerminalTwinCenter input.certified m center ∧
            input.certified.localizedOccurrenceFourLigandFrame? cursor.occurrence =
              some frame ∧
            (∀ i, (frame.cursorAt i).occurrence.1.node.current? =
              some (m.ligandAtomAt center (alpha i))) ∧
            input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame ∧
            (∀ i, input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
              some (pointAt (alpha i))) ∧
            (∀ i, input.certified.spatialPointAt? (m.ligandAtomAt center i) =
              some (pointAt i)) ∧
            Nonempty (PhysicalFrameCalibration m cfg center alpha (fun i => pointAt (alpha i))) ∧
            tracked.pseudoComparisons = 0 ∧
            LocalizedUniversalReference.referenceState input cursor.occurrence =
              some (.chiral rs) ∧
            rationalVolumeSign
              (CartesianPoint3.orientedVolume
                (pointAt (alpha 0)) (pointAt (alpha 1))
                (pointAt (alpha 2)) (pointAt (alpha 3))) =
              m.configurationSign cfg center * permHandedness alpha) := by
  classical
  obtain ⟨currentAtom, currentEq⟩ :=
    input.certified.localizedRerootCursor_current_exists cursor
  have finalRoot : cursor.occurrence.1.root = topCenter.1 := by
    rw [dependency.1]
    exact AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
      (LocalizedUniversalReference.carrierFuel input) topCenter
  have rootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter cursor.occurrence.1.root := by
    rw [finalRoot]
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet topCenter.1).mp topCenter.2
  by_cases candidate : currentAtom ∈ m.centers
  · let center : m.Center := ⟨currentAtom, candidate⟩
    have centerAt : cursor.occurrence.1.node.current? = some center.1 := currentEq
    have center_ne_root : center ≠ root := by
      intro centerEqRoot
      have valueEq : center.1 = root.1 := congrArg Subtype.val centerEqRoot
      have atomEqRoot : currentAtom = root.1 := valueEq
      have atomEqTop : currentAtom = topCenter.1 := atomEqRoot.trans topAt.symm
      have currentTop : cursor.occurrence.1.node.current? = some topCenter.1 := by
        rw [currentEq, atomEqTop]
      exact dependency_current_ne_topAtom_of_finalOccurrence input singleBonded acyclic
        topCenter cursor dependency currentTop
    rcases domain.centerCase center center_ne_root with twin | calibrated
    · exact Or.inr (Or.inl
        ⟨actualPhysicalTerminalTwinLeaves_of_globalTwinCenter input m domain.graphEq
            center cursor.occurrence centerAt twin,
          referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble m
            domain.graphEq center cursor.occurrence centerAt rootTetrahedral twin⟩)
    · obtain ⟨rs, tracked, frame, alpha, pointAt, frameComputed, matchLigand, separated,
        spatial, observed, calibration, pseudoZero, state, signNormalized⟩ :=
        exists_chiral_of_globalCalibratedCenter input singleBonded acyclic noDouble m cfg
          domain.graphEq center cursor.occurrence centerAt calibrated
      exact Or.inr (Or.inr
        ⟨center, rs, tracked, frame, alpha, pointAt, centerAt,
          actualPhysicalTerminalTwinCenter_false_of_calibrated calibrated,
          frameComputed, matchLigand, separated, spatial, observed, calibration,
          pseudoZero, state, signNormalized⟩)
  · have notCandidate : currentAtom ∉ input.certified.tetrahedralCenterSet := by
      intro detected
      exact candidate (mem_centers_of_mem_tetrahedralCenterSet coverage detected)
    have noncandidate : ActualPhysicalNoncandidate input cursor.occurrence :=
      ⟨currentAtom, currentEq, notCandidate⟩
    exact Or.inl
      ⟨noncandidate,
        referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble
          cursor.occurrence noncandidate⟩





theorem actualStrictDependency_referenceState_none_or_chiral
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = root.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    LocalizedUniversalReference.referenceState input cursor.occurrence = none ∨
      ∃ rs : RS,
        LocalizedUniversalReference.referenceState input cursor.occurrence = some (.chiral rs) := by
  rcases actualStrictDependency_classification input singleBonded acyclic noDouble m cfg root
    domain coverage topCenter topAt cursor dependency with
    ⟨_noncandidate, noneEq⟩ | ⟨_twins, noneEq⟩ | ⟨_center, rs, _tracked, _frame, _alpha,
      _pointAt, _current, _notTwin, _frameComputed, _match, _separated, _spatial, _observed,
      _calibration, _pseudo, state, _sign⟩
  · exact Or.inl noneEq
  · exact Or.inl noneEq
  · exact Or.inr ⟨rs, state⟩






def ActualLocalSignLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (mirror : Bool) (d : m.Center) : Prop :=
  m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
    (if mirror then (-1 : ℝ) else 1) * m.configurationSign cfg (m.centerPerm e d)











theorem actual_referenceState_automorphism_sign_iff
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (d : m.Center) (e : m.Aut) (mirror : Bool)
    (d_ne_root : d ≠ root)
    (image_ne_root : m.centerPerm e d ≠ root)
    (d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d)
    (image_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d))
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some d.1)
    (uCurrent : u.1.node.current? = some (m.centerPerm e d).1) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) ↔
      ActualLocalSignLaw m cfg e mirror d := by
  have calibratedD : ActualPhysicalCalibratedCenter input.certified m cfg d :=
    actualPhysicalCalibratedCenter_of_globalDomain domain d_ne_root d_notTwin
  have calibratedImage : ActualPhysicalCalibratedCenter input.certified m cfg (m.centerPerm e d) :=
    actualPhysicalCalibratedCenter_of_globalDomain domain image_ne_root image_notTwin
  obtain ⟨frameT, alphaT, pointAtT, frameTComputed, matchT, separatedT, spatialT,
    observedT, calibrationTNonempty⟩ :=
    exists_frameAndCalibration_of_calibratedCenter input singleBonded acyclic m cfg
      domain.graphEq d t tCurrent calibratedD
  obtain ⟨frameU, alphaU, pointAtU, frameUComputed, matchU, separatedU, spatialU,
    observedU, calibrationUNonempty⟩ :=
    exists_frameAndCalibration_of_calibratedCenter input singleBonded acyclic m cfg
      domain.graphEq (m.centerPerm e d) u uCurrent calibratedImage
  obtain ⟨calibrationT⟩ := calibrationTNonempty
  obtain ⟨calibrationU⟩ := calibrationUNonempty
  let matchFrameT : ActualFrameLigandMatch input m frameT d alphaT :=
    { real := fun index =>
        input.certified.carrierOccurrence_provenance_real singleBonded acyclic
          (frameT.cursorAt index).occurrence
      atom := matchT }
  let matchFrameU : ActualFrameLigandMatch input m frameU (m.centerPerm e d) alphaU :=
    { real := fun index =>
        input.certified.carrierOccurrence_provenance_real singleBonded acyclic
          (frameU.cursorAt index).occurrence
      atom := matchU }
  have memD : d.1 ∈ input.certified.tetrahedralCenterSet :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet d.1).mpr
      (input.certified.isTetrahedralCenter_of_physicalLigandEquiv m domain.graphEq d)
  have memImage : (m.centerPerm e d).1 ∈ input.certified.tetrahedralCenterSet :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet (m.centerPerm e d).1).mpr
      (input.certified.isTetrahedralCenter_of_physicalLigandEquiv m domain.graphEq
        (m.centerPerm e d))
  let centerT : input.certified.TetrahedralCenter := ⟨d.1, memD⟩
  let centerU : input.certified.TetrahedralCenter := ⟨(m.centerPerm e d).1, memImage⟩
  have centerRealT : input.certified.RealTetrahedralCenterNode t.1.node centerT :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic t, tCurrent⟩
  have centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic u, uCurrent⟩
  have framesEq := referenceState_rootZAutomorphism_label_sign_iff
    (input := input) (noDouble := noDouble) (m := m) (molEq := domain.graphEq)
    (cfg := cfg) (d := d) (e := e) (mirror := mirror) (t := t) (u := u)
    (F := frameT) (G := frameU)
    (derivedF := input.certified.localizedOccurrenceFourLigandFrame?_sound t frameT
      frameTComputed)
    (derivedG := input.certified.localizedOccurrenceFourLigandFrame?_sound u frameU
      frameUComputed)
    (separatedF := separatedT) (separatedG := separatedU)
    (centerF := centerT) (centerU := centerU)
    (centerRealF := centerRealT) (centerRealU := centerRealU)
    (centerF_at := rfl) (centerU_at := rfl)
    (alphaF := alphaT) (alphaG := alphaU)
    (matchF := matchFrameT) (matchG := matchFrameU)
    (pointsF := fun index => pointAtT (alphaT index))
    (pointsU := fun index => pointAtU (alphaU index))
    (spatialF := spatialT) (spatialU := spatialU)
    (calibrationF := calibrationT) (calibrationU := calibrationU)
  simpa [ActualLocalSignLaw] using framesEq

/-- The paired corollary in the packaged local-sign-law form used by the branch transport
consumer signatures. -/
theorem actual_referenceState_automorphism_sign_iff_localSignLaw
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (d : m.Center) (e : m.Aut) (mirror : Bool)
    (d_ne_root : d ≠ root)
    (image_ne_root : m.centerPerm e d ≠ root)
    (d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d)
    (image_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d))
    (t u : LocalizedUniversalReference.Occurrence input)
    (tCurrent : t.1.node.current? = some d.1)
    (uCurrent : u.1.node.current? = some (m.centerPerm e d).1) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) ↔
      ActualLocalSignLaw m cfg e mirror d :=
  actual_referenceState_automorphism_sign_iff input noDouble singleBonded acyclic m cfg root
    domain d e mirror d_ne_root image_ne_root d_notTwin image_notTwin t u tCurrent uCurrent







def ActualBranchReaderSignInventory
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (e : m.Aut) (mirror : Bool)
    (occurrenceAt : (d : m.Center) → LocalizedUniversalReference.Occurrence input) : Prop :=
  ∀ d : m.Center,
    LocalizedUniversalReference.referenceState input (occurrenceAt (m.centerPerm e d)) =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input (occurrenceAt d))






theorem actualLocalSignLaw_of_branchReaderInventory
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (e : m.Aut) (mirror : Bool)
    (occurrenceAt : (d : m.Center) → LocalizedUniversalReference.Occurrence input)
    (inventory : ActualBranchReaderSignInventory input m e mirror occurrenceAt)
    (d : m.Center)
    (d_ne_root : d ≠ root)
    (image_ne_root : m.centerPerm e d ≠ root)
    (d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d)
    (image_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d))
    (currentAt : ∀ c : m.Center, (occurrenceAt c).1.node.current? = some c.1) :
    ActualLocalSignLaw m cfg e mirror d := by
  have stateEq := inventory d
  have iff :=
    actual_referenceState_automorphism_sign_iff input noDouble singleBonded acyclic m cfg root
      domain d e mirror d_ne_root image_ne_root d_notTwin image_notTwin
      (occurrenceAt d) (occurrenceAt (m.centerPerm e d)) (currentAt d) (currentAt (m.centerPerm e d))
  exact iff.mp stateEq





theorem actualBranchLocalSignLaws_of_branchReaderInventory
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root c : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (e : m.Aut) (mirror : Bool)
    (occurrenceAt : (d : m.Center) → LocalizedUniversalReference.Occurrence input)
    (inventory : ActualBranchReaderSignInventory input m e mirror occurrenceAt)
    (i : Fin 4)
    (currentAt : ∀ d : m.Center, (occurrenceAt d).1.node.current? = some d.1) :
    ∀ d : m.Center, LigandBranchReaches m c i d.1 → d ≠ root →
      m.centerPerm e d ≠ root →
        ¬ ActualPhysicalTerminalTwinCenter input.certified m d →
          ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) →
            ActualLocalSignLaw m cfg e mirror d := by
  intro d _reaches d_ne_root image_ne_root d_notTwin image_notTwin
  exact actualLocalSignLaw_of_branchReaderInventory input noDouble singleBonded acyclic m cfg
    root domain e mirror occurrenceAt inventory d d_ne_root image_ne_root d_notTwin
    image_notTwin currentAt












theorem branchTransport_of_branchReaderInventory
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (root : m.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg root)
    (e : m.Aut) (mirror : Bool) (i j : Fin 4)
    (fixesRoot : m.centerPerm e root = root)
    (slot : m.ligandPermAt e root i = j)
    (occurrenceAt : (d : m.Center) → LocalizedUniversalReference.Occurrence input)
    (inventory : ActualBranchReaderSignInventory input m e mirror occurrenceAt)
    (currentAt : ∀ d : m.Center, (occurrenceAt d).1.node.current? = some d.1) :
    BranchTransport m cfg root i j mirror := by
  rw [RootedBranchTerminalTwinCompletion.branchTransport_iff_orientationAtNonTwinCenters]
  refine ⟨e, fixesRoot, slot, ?_⟩
  intro d reaches notTwin
  have d_ne_root : d ≠ root := by
    intro hEq
    exact RootedBranchTerminalTwinCompletion.ligandBranchReaches_ne_root m root i reaches
      (congrArg Subtype.val hEq)
  have image_ne_root : m.centerPerm e d ≠ root := by
    intro hEq
    have hperm : m.centerPerm e d = m.centerPerm e root := hEq.trans fixesRoot.symm
    exact d_ne_root ((m.centerPerm e).injective hperm)
  have d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d := by
    intro twin
    exact notTwin
      ((actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins input.certified m d).mp twin)
  have image_notTwin :
      ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) := by
    intro twin
    exact d_notTwin
      ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mp twin)
  exact actualLocalSignLaw_of_branchReaderInventory input noDouble singleBonded acyclic m cfg
    root domain e mirror occurrenceAt inventory d d_ne_root image_ne_root d_notTwin
    image_notTwin currentAt

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalTerminalTwinCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualPhysicalCalibratedCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualGlobalPhysicalCalibratedDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalCalibratedCenter_of_globalDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_false_of_calibrated
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.terminalTwinPair_centerPerm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_centerPerm_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.globalCarrierFuel_adequate
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.detectedMultiCenter_mol
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.detectedMultiCenter_centers
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_tetrahedralCenterSet_of_center
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_centers_of_mem_tetrahedralCenterSet
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.isTetrahedralCenter_of_center
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_realTetrahedralCenterNode_of_center
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualGlobalPhysicalCalibratedDomain.detected
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.PhysicalCalibratedRootDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalCalibratedRootDomain_of_centerCase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_frameAndCalibration_of_calibratedCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_chiral_of_globalCalibratedCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.referenceState_eq_none_of_globalTwinCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualCandidateCenter_referenceState_none_iff_twin
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualCandidateCenter_referenceState_chiral_iff_notTwin
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinLeaves_of_globalTwinCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualStrictDependency_classification
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualStrictDependency_referenceState_none_or_chiral
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualLocalSignLaw
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actual_referenceState_automorphism_sign_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actual_referenceState_automorphism_sign_iff_localSignLaw
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualBranchReaderSignInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualLocalSignLaw_of_branchReaderInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualBranchLocalSignLaws_of_branchReaderInventory
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.branchTransport_of_branchReaderInventory

end CertifiedLocalizedCIPInput

end OneCenter
end TetraStereo
