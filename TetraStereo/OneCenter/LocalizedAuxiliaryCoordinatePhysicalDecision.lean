import TetraStereo.OneCenter.AuxiliaryBranchTerminalTwinCompletion
import TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.OneCenter.LocalizedContextFrameCompilation
import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureAuxiliaryLetter
import TetraStereo.OneCenter.LocalizedAuxiliaryPhysicalSearchChecks
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! Executable auxiliary physical queries on the actual input coordinates. The query takes atom
identifiers and the actual retained history, never a noncomputably detected frame or a supplied
physical configuration. -/

namespace TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision

open FiniteAuxiliaryBranchTransport
open AuxiliaryBranchTerminalTwinCompletion
open LocalizedActualPhysicalBranchDecision
open LocalizedRecursiveAuxiliaryPhysicalDomain
open RetainedCoherentSymmetry
open RootedTetrahedralBranchSymmetry
open CertifiedLocalizedCIPInput
open TerminalTwinConfigurationGauge
open LocalizedRecursiveAuxiliaryPhysicalCorrectness
open DeclarativeCIP

private def fixtureAtom (i : Fin 9) :
    LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.Atom := i

/-- Executable actual-coordinate query over every input atom, with the exact history-deleted
residual-component semantics of the finite generic engine. -/
def decideCoordinateAuxiliaryTransport (input : CertifiedLocalizedCIPInput)
    (history : List input.Atom) (source target : input.Atom) (mirror : Bool) : Bool :=
  FiniteAuxiliaryBranchTransport.decideAuxiliaryComponentTransport
    (actualCanonicalMolecule input) (coordinateCfg input) history source target mirror
    (List.finRange input.certified.input.molecule.atomCount)

theorem decideCoordinateAuxiliaryTransport_iff (input : CertifiedLocalizedCIPInput)
    (history : List input.Atom) (source target : input.Atom) (mirror : Bool) :
    decideCoordinateAuxiliaryTransport input history source target mirror = true ↔
      AuxiliaryComponentTransport (actualCanonicalMolecule input) (coordinateCfg input)
        history source target mirror := by
  unfold decideCoordinateAuxiliaryTransport
  exact FiniteAuxiliaryBranchTransport.decideAuxiliaryComponentTransport_iff _ _ _ _ _ _
    (List.finRange input.certified.input.molecule.atomCount) (List.nodup_finRange _) (by intro v; exact List.mem_finRange v)

/-- The accepted root-arm occurrence really retains the ordered two-atom history `[2, 0]` used
by the executable nine-atom controls below. -/
theorem nineAtomRootArm_history :
    LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmTarget.1.node.history =
      [fixtureAtom 2, fixtureAtom 0] := by
  have rootReal :
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTarget.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom :=
    LocalizedRuleMajorReference.finalOccurrence_provenance_real
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.fixtureReference
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTetra
  have simpleBonded :
      LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.moleculeGraph.SimpleBonded := by
    change LocalizedRecursiveCyclicSymmetricFixture.graph.SimpleBonded
    exact LocalizedRecursiveCyclicSymmetricFixture.simple_bonded
  have cursorEq := LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    simpleBonded LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames rfl
    rootReal LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot
  have rootCenterAtom :
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center.1 = fixtureAtom 0 := by
    rw [LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.centerEq]
    simp [LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootUnit,
      LocalizedRuleMajorReference.finalCenterUnit, DeclarativeCIP.OccurrenceUnit.atom,
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTetra, fixtureAtom]
    apply Fin.ext
    rfl
  change (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.frame.cursorAt
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot).occurrence.1.node.history = _
  rw [cursorEq]
  have ligandEq :
      LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.canonicalLigandAtom
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center
          (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.canonicalLigandReindex
            LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center
            (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.detectedLigandPermutation
              LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot)) =
        fixtureAtom 2 := by
    exact (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.canonicalLigandReindex_spec
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center
      (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.detectedLigandPermutation
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot)).symm.trans
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot_atom
  change [LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.canonicalLigandAtom
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center
      (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.canonicalLigandReindex
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center
        (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.detectedLigandPermutation
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot)),
    LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center.1] =
      [fixtureAtom 2, fixtureAtom 0]
  rw [ligandEq, rootCenterAtom]

/-- Coordinate signs and a calibrated-or-twin physical configuration have the same retained
transport relation. At residual twin centers the history-relative gauge completes precisely the
missing signs. The configuration `cfg` lives in the reindexed detected model; it is not a supplied
coordinate sign law. -/
theorem coordinateAuxiliaryComponentTransport_iff_reindexed
    (input : CertifiedLocalizedCIPInput)
    (τ : (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4))
    (cfg : ((actualCanonicalMolecule input).reindexFrames τ).Configuration)
    (root : ((actualCanonicalMolecule input).reindexFrames τ).Center)
    (cases : ∀ d : ((actualCanonicalMolecule input).reindexFrames τ).Center,
      d ≠ root →
        ActualPhysicalTerminalTwinCenter input ((actualCanonicalMolecule input).reindexFrames τ) d ∨
        ActualPhysicalCalibratedCoordinates input
          ((actualCanonicalMolecule input).reindexFrames τ) cfg d)
    (history : List input.Atom) (source target : input.Atom) (mirror : Bool)
    (rootMem : root.1 ∈ history)
    (historyLeafAvoid : ∀ d : (actualCanonicalMolecule input).Center,
      InComponent (actualCanonicalMolecule input).mol history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair
        (actualCanonicalMolecule input) d a b → a ∉ history ∧ b ∉ history)
    (sourceLeafAvoid : ∀ d : (actualCanonicalMolecule input).Center,
      InComponent (actualCanonicalMolecule input).mol history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair
        (actualCanonicalMolecule input) d a b → source ≠ a ∧ source ≠ b) :
    AuxiliaryComponentTransport (actualCanonicalMolecule input) (coordinateCfg input)
      history source target mirror ↔
    AuxiliaryComponentTransport ((actualCanonicalMolecule input).reindexFrames τ) cfg
      history source target mirror := by
  let m := actualCanonicalMolecule input
  let cfgC : m.Configuration := fun d => cfg d * τ d
  have hcfg : m.reindexConfiguration τ cfgC = cfg := by
    funext d
    simp [cfgC, MultiCenterMolecule.reindexConfiguration_apply]
  have nonTwinIff :
      AuxiliaryNonTwinComponentTransport m (coordinateCfg input) history source target mirror ↔
        AuxiliaryNonTwinComponentTransport m cfgC history source target mirror := by
    constructor
    · rintro ⟨E, hfixed, hsent, hlaw⟩
      refine ⟨E, hfixed, hsent, ?_⟩
      intro d hd hnotTwin
      have dNotHistory := RetainedCoherentSymmetry.inComponent_not_mem m.mol hd
      have dNeRoot : d ≠ root := by
        intro h
        exact dNotHistory (h ▸ rootMem)
      let dR : (m.reindexFrames τ).Center := d
      have caseD := cases dR dNeRoot
      have notTwinD : ¬ ActualPhysicalTerminalTwinCenter input (m.reindexFrames τ) dR := by
        intro twin
        have twinM : ActualPhysicalTerminalTwinCenter input m d :=
          @CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_congr_mol
            input (m.reindexFrames τ) m dR d rfl (by rfl) twin
        exact hnotTwin ((CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins
          input m d).mpr twinM)
      obtain ⟨points, observed, nonzero, sign⟩ := (Or.resolve_left caseD notTwinD)
      have coordD := coordinateSign_of_reindexedCalibration input τ cfg dR
        ⟨points, observed, nonzero, sign⟩
      let Eτ : (m.reindexFrames τ).Aut := m.autReindex τ E
      have dImage : (m.reindexFrames τ).centerPerm Eτ dR = m.centerPerm E d :=
        MultiCenterMolecule.reindexFrames_centerPerm m τ E d
      have imageNeRoot : (m.reindexFrames τ).centerPerm Eτ dR ≠ root := by
        intro heq
        have hperm : (E : Equiv.Perm input.Atom) d.1 = root.1 := by
          have hcenter : m.centerPerm E d = root := dImage.symm.trans heq
          have hval : (m.centerPerm E d).1 = root.1 := congrArg Subtype.val hcenter
          simpa [MultiCenterMolecule.centerPerm] using hval
        have rootFixed : (E : Equiv.Perm input.Atom) root.1 = root.1 := hfixed root.1 rootMem
        have same : (E : Equiv.Perm input.Atom) d.1 =
            (E : Equiv.Perm input.Atom) root.1 := hperm.trans rootFixed.symm
        have atoms : d.1 = root.1 := (E : Equiv.Perm input.Atom).injective same
        exact dNotHistory (atoms ▸ rootMem)
      have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input
          (m.reindexFrames τ) ((m.reindexFrames τ).centerPerm Eτ dR) := by
        intro twinImage
        have twinD := (CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_centerPerm_iff
          input (m.reindexFrames τ) Eτ dR).mp twinImage
        exact notTwinD twinD
      obtain ⟨imagePoints, imageObserved, imageNonzero, imageSign⟩ :=
        Or.resolve_left (cases ((m.reindexFrames τ).centerPerm Eτ dR) imageNeRoot) imageNotTwin
      have coordImage := coordinateSign_of_reindexedCalibration input τ cfg
        ((m.reindexFrames τ).centerPerm Eτ dR)
        ⟨imagePoints, imageObserved, imageNonzero, imageSign⟩
      have signD : m.configurationSign (coordinateCfg input) d =
          m.configurationSign cfgC d := by
        rw [coordD]
        simp [cfgC, dR, MultiCenterMolecule.configurationSign, permHandedness_mul]
      have signImage : m.configurationSign (coordinateCfg input) (m.centerPerm E d) =
          m.configurationSign cfgC (m.centerPerm E d) := by
        calc
          m.configurationSign (coordinateCfg input) (m.centerPerm E d) =
              m.configurationSign (coordinateCfg input)
                ((m.reindexFrames τ).centerPerm Eτ dR) := by rw [dImage]
          _ = permHandedness (cfg ((m.reindexFrames τ).centerPerm Eτ dR)) *
                permHandedness (τ ((m.reindexFrames τ).centerPerm Eτ dR)) := coordImage
          _ = m.configurationSign cfgC (m.centerPerm E d) := by
                simp [cfgC, dImage, MultiCenterMolecule.configurationSign, permHandedness_mul]
      rw [← signD, ← signImage]
      exact hlaw d hd hnotTwin
    · rintro ⟨E, hfixed, hsent, hlaw⟩
      refine ⟨E, hfixed, hsent, ?_⟩
      intro d hd hnotTwin
      have dNotHistory := RetainedCoherentSymmetry.inComponent_not_mem m.mol hd
      have dNeRoot : d ≠ root := by
        intro h
        exact dNotHistory (h ▸ rootMem)
      let dR : (m.reindexFrames τ).Center := d
      have caseD := cases dR dNeRoot
      have notTwinD : ¬ ActualPhysicalTerminalTwinCenter input (m.reindexFrames τ) dR := by
        intro twin
        have twinM : ActualPhysicalTerminalTwinCenter input m d :=
          @CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_congr_mol
            input (m.reindexFrames τ) m dR d rfl (by rfl) twin
        exact hnotTwin ((CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins
          input m d).mpr twinM)
      obtain ⟨points, observed, nonzero, sign⟩ := Or.resolve_left caseD notTwinD
      have coordD := coordinateSign_of_reindexedCalibration input τ cfg dR
        ⟨points, observed, nonzero, sign⟩
      let Eτ : (m.reindexFrames τ).Aut := m.autReindex τ E
      have dImage : (m.reindexFrames τ).centerPerm Eτ dR = m.centerPerm E d :=
        MultiCenterMolecule.reindexFrames_centerPerm m τ E d
      have imageNeRoot : (m.reindexFrames τ).centerPerm Eτ dR ≠ root := by
        intro heq
        have hperm : (E : Equiv.Perm input.Atom) d.1 = root.1 := by
          have hcenter : m.centerPerm E d = root := dImage.symm.trans heq
          have hval : (m.centerPerm E d).1 = root.1 := congrArg Subtype.val hcenter
          simpa [MultiCenterMolecule.centerPerm] using hval
        have rootFixed : (E : Equiv.Perm input.Atom) root.1 = root.1 := hfixed root.1 rootMem
        have atoms : d.1 = root.1 := (E : Equiv.Perm input.Atom).injective
          (hperm.trans rootFixed.symm)
        exact dNotHistory (atoms ▸ rootMem)
      have imageNotTwin : ¬ ActualPhysicalTerminalTwinCenter input
          (m.reindexFrames τ) ((m.reindexFrames τ).centerPerm Eτ dR) := by
        intro twinImage
        exact notTwinD ((CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_centerPerm_iff
          input (m.reindexFrames τ) Eτ dR).mp twinImage)
      obtain ⟨imagePoints, imageObserved, imageNonzero, imageSign⟩ :=
        Or.resolve_left (cases ((m.reindexFrames τ).centerPerm Eτ dR) imageNeRoot) imageNotTwin
      have coordImage := coordinateSign_of_reindexedCalibration input τ cfg
        ((m.reindexFrames τ).centerPerm Eτ dR)
        ⟨imagePoints, imageObserved, imageNonzero, imageSign⟩
      have signD : m.configurationSign (coordinateCfg input) d =
          m.configurationSign cfgC d := by
        rw [coordD]
        simp [cfgC, dR, MultiCenterMolecule.configurationSign, permHandedness_mul]
      have signImage : m.configurationSign (coordinateCfg input) (m.centerPerm E d) =
          m.configurationSign cfgC (m.centerPerm E d) := by
        calc
          m.configurationSign (coordinateCfg input) (m.centerPerm E d) =
              m.configurationSign (coordinateCfg input)
                ((m.reindexFrames τ).centerPerm Eτ dR) := by rw [dImage]
          _ = permHandedness (cfg ((m.reindexFrames τ).centerPerm Eτ dR)) *
                permHandedness (τ ((m.reindexFrames τ).centerPerm Eτ dR)) := coordImage
          _ = m.configurationSign cfgC (m.centerPerm E d) := by
                simp [cfgC, dImage, MultiCenterMolecule.configurationSign, permHandedness_mul]
      rw [signD, signImage]
      exact hlaw d hd hnotTwin
  have gaugeCoord := auxiliaryComponentTransport_iff_nonTwin m (coordinateCfg input)
    history source target mirror historyLeafAvoid sourceLeafAvoid
  have gaugeCfgC := auxiliaryComponentTransport_iff_nonTwin m cfgC
    history source target mirror historyLeafAvoid sourceLeafAvoid
  have frameIff := FiniteAuxiliaryBranchTransport.auxiliaryComponentTransport_reindexFrames_iff
    m τ cfgC history source target mirror
  have result := gaugeCoord.trans (nonTwinIff.trans (gaugeCfgC.symm.trans frameIff.symm))
  simpa [hcfg] using result


private theorem calibratedCoordinates_congr
    {input : CertifiedLocalizedCIPInput}
    {m n : MultiCenterMolecule input.Atom} (h : m = n)
    (cfg : m.Configuration) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) center) := by
  cases h
  exact coordinates

private theorem terminalTwinPair_congr_mol
    {V : Type} [Fintype V] [DecidableEq V] {m n : MultiCenterMolecule V}
    {c : m.Center} {d : n.Center} {a b : V}
    (hmol : m.mol = n.mol) (hcenter : c.1 = d.1)
    (pair : TerminalTwinConfigurationGauge.TerminalTwinPair m c a b) :
    TerminalTwinConfigurationGauge.TerminalTwinPair n d a b := by
  refine ⟨pair.ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hmol, ← hcenter]
    exact pair.neighbor_a
  · rw [← hmol, ← hcenter]
    exact pair.neighbor_b
  · rw [← hmol]
    exact pair.z_eq
  · rw [← hmol]
    exact pair.mass_eq
  · rw [← hmol]
    exact pair.charge_eq
  · rw [← hmol, ← hcenter]
    exact pair.bond_eq

/-- Pull the original calibrated-or-terminal-twin domain back along the accepted canonical to
 detected frame reindexing. The reindexing witness is chosen inside the proof, so callers supply
 only the original domain. -/
theorem originalDomain_gives_reindexedCases
    (input : CertifiedLocalizedCIPInput)
    (τ : (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4))
    (hτ : (actualCanonicalMolecule input).reindexFrames τ =
      input.detectedMultiCenterMolecule)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : RecursiveAuxiliaryPhysicalDomain input cfg root) :
    let m := actualCanonicalMolecule input
    let cfgR : (m.reindexFrames τ).Configuration := Eq.mpr
      (congrArg MultiCenterMolecule.Configuration hτ) cfg
    let rootR : (m.reindexFrames τ).Center := Eq.mpr
      (congrArg MultiCenterMolecule.Center hτ) root
    ∀ d : (m.reindexFrames τ).Center, d ≠ rootR →
      ActualPhysicalTerminalTwinCenter input (m.reindexFrames τ) d ∨
      ActualPhysicalCalibratedCoordinates input (m.reindexFrames τ) cfgR d := by
  dsimp
  intro d dNeRoot
  let m := actualCanonicalMolecule input
  have hτm : m.reindexFrames τ = input.detectedMultiCenterMolecule := hτ
  let cfgR : (m.reindexFrames τ).Configuration := Eq.mpr
    (congrArg MultiCenterMolecule.Configuration hτ) cfg
  let rootR : (m.reindexFrames τ).Center := Eq.mpr
    (congrArg MultiCenterMolecule.Center hτ) root
  let dD : input.detectedMultiCenterMolecule.Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center hτ) d
  have dD_ne : dD ≠ root := by
    intro same
    apply dNeRoot
    have castBack : d = Eq.mpr (congrArg MultiCenterMolecule.Center hτ) dD := by
      simp [dD]
    rw [castBack, same]
    rfl
  rcases domain.centerCase dD dD_ne with twin | calibrated
  · left
    exact @CertifiedLocalizedCIPInput.actualPhysicalTerminalTwinCenter_congr_mol
      input input.detectedMultiCenterMolecule (m.reindexFrames τ) dD d
      (congrArg MultiCenterMolecule.mol hτm).symm rfl twin
  · right
    have moved := calibratedCoordinates_congr (input := input) hτ.symm cfg dD calibrated
    have cfgCast : Eq.mp (congrArg MultiCenterMolecule.Configuration hτ.symm) cfg = cfgR := by
      simp [cfgR]
    have centerCast : Eq.mp (congrArg MultiCenterMolecule.Center hτ.symm) dD = d := by
      simp [dD]
    simpa [cfgCast, centerCast] using moved

/-- The executable coordinate query is equivalent to the original detected-molecule
`AuxiliaryComponentTransport` under exactly the original calibrated-or-terminal-twin domain.
The source may lie in history: the finite reach set is empty in that case, and every relation
statement here keeps that exact vacuous-component behavior. -/
theorem decideCoordinateAuxiliaryTransport_exact_of_originalDomain
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : RecursiveAuxiliaryPhysicalDomain input cfg root)
    (history : List input.Atom) (source target : input.Atom) (mirror : Bool)
    (rootMem : root.1 ∈ history)
    (historyLeafAvoid : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair
        input.detectedMultiCenterMolecule d a b → a ∉ history ∧ b ∉ history)
    (sourceLeafAvoid : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph history source d.1 →
      ∀ a b, TerminalTwinConfigurationGauge.TerminalTwinPair
        input.detectedMultiCenterMolecule d a b → source ≠ a ∧ source ≠ b) :
    decideCoordinateAuxiliaryTransport input history source target mirror = true ↔
      AuxiliaryComponentTransport input.detectedMultiCenterMolecule cfg
        history source target mirror := by
  obtain ⟨τ, hτ⟩ := exists_canonical_reindex input
  let m := actualCanonicalMolecule input
  have hmol : m.mol = input.detectedMultiCenterMolecule.mol := by
    simpa using congrArg MultiCenterMolecule.mol hτ
  let cfgR : (m.reindexFrames τ).Configuration := Eq.mpr
    (congrArg MultiCenterMolecule.Configuration hτ) cfg
  let rootR : (m.reindexFrames τ).Center := Eq.mpr
    (congrArg MultiCenterMolecule.Center hτ) root
  have cases := originalDomain_gives_reindexedCases input τ hτ cfg root domain
  have rootMemR : rootR.1 ∈ history := by
    have centerEq : rootR.1 = root.1 := by simp [rootR]
    simpa [centerEq] using rootMem
  have coordinateRelation := coordinateAuxiliaryComponentTransport_iff_reindexed
    input τ cfgR rootR cases history source target mirror rootMemR
    (by
      intro d hd a b pair
      let dD : input.detectedMultiCenterMolecule.Center :=
        Eq.mp (congrArg MultiCenterMolecule.Center hτ) d
      have hdD : InComponent input.moleculeGraph history source dD.1 := by
        simpa [dD] using hd
      have pairD : TerminalTwinConfigurationGauge.TerminalTwinPair
          input.detectedMultiCenterMolecule dD a b := by
        exact terminalTwinPair_congr_mol hmol (by simp [dD]) pair
      exact historyLeafAvoid dD hdD a b pairD)
    (by
      intro d hd a b pair
      let dD : input.detectedMultiCenterMolecule.Center :=
        Eq.mp (congrArg MultiCenterMolecule.Center hτ) d
      have hdD : InComponent input.moleculeGraph history source dD.1 := by
        simpa [dD] using hd
      have pairD : TerminalTwinConfigurationGauge.TerminalTwinPair
          input.detectedMultiCenterMolecule dD a b := by
        exact terminalTwinPair_congr_mol hmol (by simp [dD]) pair
      exact sourceLeafAvoid dD hdD a b pairD)
  have decisionRelation := decideCoordinateAuxiliaryTransport_iff
    input history source target mirror
  have cfgEq : Eq.mp
      (congrArg (fun n : MultiCenterMolecule input.Atom => n.Configuration) hτ) cfgR = cfg := by
    simp [cfgR]
  have modelRelation := FiniteAuxiliaryBranchTransport.auxiliaryComponentTransport_congr
    (m₁ := m.reindexFrames τ) (m₂ := input.detectedMultiCenterMolecule) hτ cfgR cfg cfgEq
    history (source₁ := source) (source₂ := source)
    (target₁ := target) (target₂ := target) rfl rfl mirror
  exact decisionRelation.trans (coordinateRelation.trans modelRelation)

/-- Original-domain coordinate decision at an actual retained occurrence and compiled outgoing
frame. The path and frame data derive the terminal-leaf avoidance facts; the only source-level
physical assumptions are the existing recursive calibrated-or-terminal-twin domain and the
simple-bonded path condition used by the accepted occurrence-path bridge. -/
theorem decideActualContextAuxiliaryTransport_exact
    (input : LocalizedRuleMajorReference.Input)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (frames : LocalizedRuleMajorReference.ContextFrameCompilation input target unit targetUnit)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (rootEq : root.1 = target.1.root)
    (domain : RecursiveAuxiliaryPhysicalDomain input.certified cfg root)
    (a b : Fin 4) (mirror : Bool)
    (real : target.1.node.provenance = .realAtom) :
    decideCoordinateAuxiliaryTransport input.certified target.1.node.history
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation a))
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation b)) mirror = true ↔
    ∃ σ : input.certified.moleculeGraph.Aut,
      AuxiliaryBranchTransport frames σ cfg a b mirror := by
  let current := frames.center.1
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node frames.center :=
    (input.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff target frames.center).mp
      frames.centerComputed
  have currentObserved : target.1.node.current? = some current := centerReal.2
  have historyFacts :=
    LocalizedActualBoundaryObservationReadback.occurrence_history_facts
      input.certified target real
  have currentMember : current ∈ target.1.node.history := by
    apply List.mem_of_head?_eq_some
    exact historyFacts.2.symm.trans currentObserved
  have currentDetected : current ∈ input.certified.detectedMultiCenterMolecule.centers := by
    apply (input.certified.moleculeGraph.mem_detectedMultiCenterMolecule_centers_iff current).2
    exact (input.certified.moleculeGraph.mem_tetrahedralCenterSet current).1 frames.center.2
  have centerEq : frames.center.1 = unit.1.atom := frames.centerEq
  have path := input.certified.simpleOccurrencePath_of_carrier_real singleBonded target real
  have pathReal := input.certified.simpleOccurrencePath_realPathNode path
  have historyHead : target.1.node.history.head? = some current := by
    exact historyFacts.2.symm.trans currentObserved
  have rootLast := input.certified.realPathNode_history_getLast pathReal
  have unitCurrent : unit.1.atom = current := by
    calc
      unit.1.atom = (input.certified.molecularFrameUnit target.1).atom :=
        (congrArg DeclarativeCIP.OccurrenceUnit.atom targetUnit).symm
      _ = current := input.certified.molecularFrameUnit_atom_eq_current target.1
        historyHead rootLast
  have sourceAdjacent (slot : Fin 4) : input.certified.moleculeGraph.Adj current
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation slot)) := by
    change input.certified.moleculeGraph.Adj frames.center.1
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
        (frames.detectedLigandPermutation slot))
    exact input.certified.detectedMultiCenterMolecule.ligandAtomAt_adj frames.center
      (frames.detectedLigandPermutation slot)
  have avoidance := AuxiliaryBranchTerminalTwinCompletion.actualOccurrence_terminalTwinLeafAvoidance
    input.certified singleBonded target real currentObserved currentMember
    (by simpa [rootEq] using root.2) currentDetected (sourceAdjacent a)
  have rootMem : root.1 ∈ target.1.node.history := by
    simpa [rootEq] using
      LocalizedRecursiveAuxiliaryPhysicalCorrectness.root_mem_history target
  have componentIff := decideCoordinateAuxiliaryTransport_exact_of_originalDomain
    input.certified cfg root domain target.1.node.history
    (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation a))
    (input.certified.detectedMultiCenterMolecule.ligandAtomAt frames.center
      (frames.detectedLigandPermutation b)) mirror rootMem avoidance.1 avoidance.2
  exact componentIff.trans
    (FiniteAuxiliaryBranchTransport.auxiliaryComponentTransport_iff_auxiliaryBranchTransport
      frames cfg a b mirror)

/-- The accepted source pipeline supplies a real compiled frame whenever its actual frame
construction hypotheses hold. This separates frame availability from the exact decision theorem
above, whose caller takes a typed `ContextFrameCompilation` as data. -/
theorem actualContextFrameCompilation_nonempty
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (real : target.1.node.provenance = .realAtom) :
    Nonempty (LocalizedRuleMajorReference.ContextFrameCompilation input target unit targetUnit) :=
  LocalizedRuleMajorReference.exists_cyclicContextFrameCompilation input singleBonded
    target real unit targetUnit

/-- The nine-atom accepted fixture at the retained atom-2 occurrence is an original-domain
specialization: root atom 0 belongs to its full history `[2, 0]`, and the physical domain is the
existing detected calibrated-or-twin domain. The endpoint atoms are read from its actual compiled
context frame. -/
theorem nineAtomRootArmCoordinateDecision_exact
    (a b : Fin 4) (mirror : Bool) :
    decideCoordinateAuxiliaryTransport
        LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmTarget.1.node.history
        (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
          (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation a))
        (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
          (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation b))
        mirror = true ↔
      ∃ σ : LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.moleculeGraph.Aut,
        AuxiliaryBranchTransport
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames σ
          LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg a b mirror := by
  let input := LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.fixtureReference
  let target := LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmTarget
  let frames := LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames
  let root := LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.center
  have rootTargetEq : LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTarget.1.root =
      root.1 := by
    have targetRoot : LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTarget.1.root =
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTetra.1 := by
      simp [LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTarget]
    have frameRoot : root.1 =
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTetra.1 := by
      rw [LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.centerEq]
      simp [LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootUnit,
        LocalizedRuleMajorReference.finalCenterUnit, DeclarativeCIP.OccurrenceUnit.atom,
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTetra]
    exact targetRoot.trans frameRoot.symm
  have armRootEq : target.1.root =
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTarget.1.root := by
    have h := (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified).localizedOccurrenceFourLigandFrame_cursor_root
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTarget
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.frame
      (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames)
      (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.frame.cursorAt
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot)
      (List.get_mem
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.frame.cursors
        (Fin.cast
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootFrames.frame.length_eq.symm
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmSlot))
    simpa [target, LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmTarget] using h
  have rootEq : root.1 = target.1.root := rootTargetEq.symm.trans armRootEq.symm
  have domain := LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedDomainAtEveryRoot root
  have simpleBonded :
      LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.moleculeGraph.SimpleBonded := by
    change LocalizedRecursiveCyclicSymmetricFixture.graph.SimpleBonded
    exact LocalizedRecursiveCyclicSymmetricFixture.simple_bonded
  simpa [input, target, frames, root] using
    decideActualContextAuxiliaryTransport_exact input target
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmUnit rfl frames
      simpleBonded
      LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg root rootEq domain a b mirror
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmCursor_real

/-- Every distinct pair among the actual four context slots is refused by the original-domain
coordinate query, for both physical mirror flags. The relation obstruction is the already
accepted whole-molecule atom-label/history argument. -/
theorem nineAtomRootArmCoordinateDecision_false_of_distinct
    (a b : Fin 4) (mirror : Bool) (different : a ≠ b) :
    decideCoordinateAuxiliaryTransport
        LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified
        LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmTarget.1.node.history
        (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
          (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation a))
        (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
          (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation b))
        mirror = false := by
  let query := decideCoordinateAuxiliaryTransport
    LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified
    LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmTarget.1.node.history
    (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
      (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation a))
    (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
      LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
      (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation b))
    mirror
  change query = false
  cases hquery : query with
  | false => rfl
  | true =>
      have queryTrue : decideCoordinateAuxiliaryTransport
          LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified
          LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmTarget.1.node.history
          (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
            LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
            (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation a))
          (LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt
            LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.center
            (LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames.detectedLigandPermutation b))
          mirror = true := by simpa [query] using hquery
      have transport := (nineAtomRootArmCoordinateDecision_exact a b mirror).mp queryTrue
      exact False.elim (LocalizedAuxiliaryPhysicalSearchChecks.noDistinctAuxiliaryBranchTransport
        LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg a b mirror different transport)

/-- Executable control over the twelve directed distinct-neighbor atom pairs at the actual
retained history. These `#eval` controls exercise the Boolean query; the proposition theorems
above separately prove its exact original-domain meaning. -/
def nineAtomRootArmCoordinateQueriesRefused (mirror : Bool) : Bool :=
  LocalizedAuxiliaryPhysicalSearchChecks.armDistinctDirectedPairs.all fun pair =>
    decideCoordinateAuxiliaryTransport
      LocalizedRecursiveCyclicSymmetricFixture.symmetricCertified
      ([⟨2, by decide⟩, ⟨0, by decide⟩] : List (Fin 9))
      pair.1 pair.2 mirror == false

/-- info: true -/
#guard_msgs in
#eval nineAtomRootArmCoordinateQueriesRefused false

/-- info: true -/
#guard_msgs in
#eval nineAtomRootArmCoordinateQueriesRefused true

assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.decideCoordinateAuxiliaryTransport_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.nineAtomRootArm_history
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.coordinateAuxiliaryComponentTransport_iff_reindexed
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.originalDomain_gives_reindexedCases
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.decideCoordinateAuxiliaryTransport_exact_of_originalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.decideActualContextAuxiliaryTransport_exact
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.actualContextFrameCompilation_nonempty
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.nineAtomRootArmCoordinateDecision_exact
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.nineAtomRootArmCoordinateDecision_false_of_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision.nineAtomRootArmCoordinateQueriesRefused

end TetraStereo.OneCenter.LocalizedAuxiliaryCoordinatePhysicalDecision
