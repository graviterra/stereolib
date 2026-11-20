import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionStep
import TetraStereo.OneCenter.LocalizedChemicalRingComponentExchangeProperness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
**The rank loop over one actual correction witness.**

`CorrectionWitness.step` handles one correction and keeps four invariants as premises: boundary
fixation, low-rank fixation, higher-rank properness and fixation of every accumulated reference. Here those four are
discharged once, by descending induction on the rank bound. What remains is one statement about a
single refused witness center, `CorrectionOracle`: an odd automorphism supported strictly above
that center's rank, fixing the history and every accumulated reference, proper at the later source centers.

`sourceProper_of_oracle` then returns one automorphism for the whole source component: it fixes the
history and every accumulated reference, sends the tied entry to its partner and is proper at every source
center. `localCorrection_of_support` is the adapter from the support shape produced by component
re-extension.

The oracle is not constructed here. This module does not prove that refusal yields a correction.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionLoop

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRankedCorrectionTransport LocalizedChemicalRingRankedReconstruction
open LocalizedChemicalRingJointPreparedCorrectionWitness
open LocalizedChemicalRingJointPreparedCorrectionStep
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedChemicalRingComponentExchangeProperness (inComponent_map)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  {references : List input.Atom} {a b : input.Atom}
  (W : CorrectionWitness input mol c node data (inputGeometry input) references a b)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

/-- An odd correction at one witness center: it fixes the history, every atom of rank at most that
center's, and every accumulated reference; it is negative at the center and proper at later source centers. -/
def LocalCorrection (d : input.detectedMultiCenterMolecule.Center)
    (g : input.detectedMultiCenterMolecule.Aut) : Prop :=
  (∀ atom ∈ data.target.1.node.history, (g : Equiv.Perm input.Atom) atom = atom) ∧
  (∀ atom, W.rank atom ≤ W.rank d.1 → (g : Equiv.Perm input.Atom) atom = atom) ∧
  (∀ reference ∈ references, (g : Equiv.Perm input.Atom) reference = reference) ∧
  relativeSign input.detectedMultiCenterMolecule cfg g d = -1 ∧
  ∀ other : input.detectedMultiCenterMolecule.Center,
    InComponent input.moleculeGraph data.target.1.node.history.reverse a other.1 →
    W.rank d.1 < W.rank other.1 →
    relativeSign input.detectedMultiCenterMolecule cfg g other = 1

/-- Every refused witness of the rank shape returned by `CorrectionWitness.step` has a local
correction. The refusal is the actual descriptor call at the exact remaining budget. -/
def CorrectionOracle : Prop :=
  ∀ (d : input.detectedMultiCenterMolecule.Center)
    (p : {p : List input.Atom //
      ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse a p}),
    InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
    pathTerminal p.1 p.2.nonempty = d.1 →
    (∀ y ∈ p.1.dropLast, W.rank y < W.rank d.1) →
    (∀ y, InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.1.dropLast)
      d.1 y → y ≠ d.1 → W.rank d.1 < W.rank y) →
    preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol node + node.history.length -
        (rawPathNode data.target.1.root (boundaryPath data.target p.1)).history.length)
      (inputGeometry input) [] (references.map Fin.val)
      (rawPathNode data.target.1.root (boundaryPath data.target p.1)) = none →
    ∃ g, LocalCorrection input mol c node data W cfg d g

/-- A correction with component support below the witness center is a local correction. The rank
order turns the support into fixation of every atom not later than the center. -/
theorem localCorrection_of_support (d : input.detectedMultiCenterMolecule.Center)
    (p : List input.Atom)
    (prefixLower : ∀ y ∈ p.dropLast, W.rank y < W.rank d.1)
    (higher : ∀ y, InComponent input.moleculeGraph (data.target.1.node.history.reverse ++ p.dropLast)
      d.1 y → y ≠ d.1 → W.rank d.1 < W.rank y)
    (outside : d.1 ∉ data.target.1.node.history.reverse ++ p.dropLast)
    (g : input.detectedMultiCenterMolecule.Aut) (left right : input.Atom)
    (edgeL : input.moleculeGraph.Adj d.1 left) (edgeR : input.moleculeGraph.Adj d.1 right)
    (fixed : ∀ x ∈ (data.target.1.node.history.reverse ++ p.dropLast) ++ [d.1],
      (g : Equiv.Perm input.Atom) x = x)
    (support : ∀ x,
      ¬ InComponent input.moleculeGraph ((data.target.1.node.history.reverse ++ p.dropLast) ++ [d.1])
        left x →
      ¬ InComponent input.moleculeGraph ((data.target.1.node.history.reverse ++ p.dropLast) ++ [d.1])
        right x → (g : Equiv.Perm input.Atom) x = x)
    (referenceFixed : ∀ reference ∈ references, (g : Equiv.Perm input.Atom) reference = reference)
    (negative : relativeSign input.detectedMultiCenterMolecule cfg g d = -1)
    (properOff : ∀ other : input.detectedMultiCenterMolecule.Center,
      other.1 ∉ (data.target.1.node.history.reverse ++ p.dropLast) ++ [d.1] →
      relativeSign input.detectedMultiCenterMolecule cfg g other = 1) :
    LocalCorrection input mol c node data W cfg d g := by
  refine ⟨?_, ?_, referenceFixed, negative, ?_⟩
  · intro atom present
    exact fixed atom (List.mem_append_left _ (List.mem_append_left _ (List.mem_reverse.mpr present)))
  · exact support_fixes_low input.moleculeGraph
      (data.target.1.node.history.reverse ++ p.dropLast) W.rank d.1 left right outside edgeL edgeR
      higher g support
  · intro other inSource later
    apply properOff
    intro present
    rcases List.mem_append.mp present with inBoundary | isCenter
    · rcases List.mem_append.mp inBoundary with inHistory | inPrefix
      · exact inComponent_not_mem input.moleculeGraph inSource inHistory
      · have lower := prefixLower other.1 inPrefix
        omega
    · have same : other.1 = d.1 := List.mem_singleton.mp isCenter
      rw [same] at later
      exact Nat.lt_irrefl _ later

include agreement admissible supported single reached calibrated in
private theorem loop (oracle : CorrectionOracle input mol c node data W cfg) :
    ∀ (k : Nat) (correction : input.detectedMultiCenterMolecule.Aut),
      (∀ atom ∈ data.target.1.node.history, (correction : Equiv.Perm input.Atom) atom = atom) →
      (∀ atom, W.rank atom < k → (correction : Equiv.Perm input.Atom) atom = atom) →
      (∀ d : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
        k ≤ W.rank d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * correction) d = 1) →
      (∀ reference ∈ references, (correction : Equiv.Perm input.Atom) reference = reference) →
      (correction : Equiv.Perm input.Atom) a = a →
      ∃ final : input.detectedMultiCenterMolecule.Aut,
        (∀ atom ∈ data.target.1.node.history, (final : Equiv.Perm input.Atom) atom = atom) ∧
        (∀ reference ∈ references, (final : Equiv.Perm input.Atom) reference = reference) ∧
        (final : Equiv.Perm input.Atom) a = a ∧
        ∀ d : input.detectedMultiCenterMolecule.Center,
          InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
          relativeSign input.detectedMultiCenterMolecule cfg (W.symmetry * final) d = 1 := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih correction boundary low high referenceFixed entryFixed
  cases k with
  | zero =>
      exact ⟨correction, boundary, referenceFixed, entryFixed,
        fun d member => high d member (Nat.zero_le _)⟩
  | succ j =>
      rcases step input mol agreement admissible supported single c node data reached W cfg
          calibrated correction j boundary (fun atom h => low atom (Nat.lt_succ_of_le h))
          (fun d member h => high d member (Nat.succ_le_of_lt h)) referenceFixed with
        allProper |
        ⟨d, p, member, terminal, negative, pending, prefixLower, higher, maximalProper, refused⟩
      · exact ⟨correction, boundary, referenceFixed, entryFixed, allProper⟩
      · obtain ⟨g, gBoundary, gLow, gReference, gNegative, gHigh⟩ :=
          oracle d p member terminal prefixLower higher refused
        have entryRank : W.rank a ≤ W.rank d.1 :=
          witness_member_rank_le W.rank p.1 p.2.nonempty d.1 terminal prefixLower a
            (List.mem_of_mem_head? (Option.mem_def.mpr p.2.head))
        have gEntry : (g : Equiv.Perm input.Atom) a = a := gLow a entryRank
        apply ih (W.rank d.1) (Nat.lt_succ_of_le pending) (correction * g)
        · intro atom present
          change (correction : Equiv.Perm input.Atom) ((g : Equiv.Perm input.Atom) atom) = atom
          rw [gBoundary atom present, boundary atom present]
        · intro atom lower
          change (correction : Equiv.Perm input.Atom) ((g : Equiv.Perm input.Atom) atom) = atom
          rw [gLow atom (Nat.le_of_lt lower)]
          exact low atom (by omega)
        · intro other inSource later
          rw [← mul_assoc]
          by_cases same : other = d
          · rw [same]
            exact correct_current input.detectedMultiCenterMolecule cfg (W.symmetry * correction) g d
              (gLow d.1 (Nat.le_refl _)) negative gNegative
          · have strict : W.rank d.1 < W.rank other.1 := by
              apply Nat.lt_of_le_of_ne later
              intro equal
              exact same (Subtype.ext (W.rankInjective equal).symm)
            let graphAut : input.moleculeGraph.Aut :=
              ⟨g, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule g⟩
            have moved := inComponent_map input.moleculeGraph data.target.1.node.history.reverse
              graphAut (fun x present => gBoundary x (List.mem_reverse.mp present)) inSource
            have entryG : (graphAut : Equiv.Perm input.Atom) a = a := gEntry
            rw [entryG] at moved
            rw [relativeSign_mul, gHigh other inSource strict, mul_one]
            exact maximalProper (input.detectedMultiCenterMolecule.centerPerm g other) moved
              (higher_image W.rank (W.rank d.1) g gLow other.1 strict)
        · intro reference member
          change (correction : Equiv.Perm input.Atom) ((g : Equiv.Perm input.Atom) reference) =
            reference
          rw [gReference reference member, referenceFixed reference member]
        · change (correction : Equiv.Perm input.Atom) ((g : Equiv.Perm input.Atom) a) = a
          rw [gEntry, entryFixed]

include agreement admissible supported single reached calibrated in
/-- **From a local correction oracle to one source-proper automorphism.** The four invariants of
the correction step are derived by the rank induction; none is a premise. -/
theorem sourceProper_of_oracle (oracle : CorrectionOracle input mol c node data W cfg) :
    ∃ F : input.detectedMultiCenterMolecule.Aut,
      (∀ atom ∈ data.target.1.node.history, (F : Equiv.Perm input.Atom) atom = atom) ∧
      (F : Equiv.Perm input.Atom) a = b ∧
      (∀ reference ∈ references, (F : Equiv.Perm input.Atom) reference = reference) ∧
      ∀ d : input.detectedMultiCenterMolecule.Center,
        InComponent input.moleculeGraph data.target.1.node.history.reverse a d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg F d = 1 := by
  obtain ⟨final, boundary, referenceFixed, entryFixed, proper⟩ :=
    loop input mol agreement admissible supported single c node data reached W cfg calibrated oracle
      (Finset.univ.sup W.rank + 1) 1 (fun _ _ => rfl) (fun _ _ => rfl)
      (fun d _ large => absurd (Finset.le_sup (f := W.rank) (Finset.mem_univ d.1)) (by omega))
      (fun _ _ => rfl) rfl
  refine ⟨W.symmetry * final, ?_, ?_, ?_, proper⟩
  · intro atom present
    change (W.symmetry : Equiv.Perm input.Atom) ((final : Equiv.Perm input.Atom) atom) = atom
    rw [boundary atom present, W.fixedHistory atom present]
  · change (W.symmetry : Equiv.Perm input.Atom) ((final : Equiv.Perm input.Atom) a) = b
    rw [entryFixed, W.entry]
  · intro reference member
    change (W.symmetry : Equiv.Perm input.Atom) ((final : Equiv.Perm input.Atom) reference) =
      reference
    rw [referenceFixed reference member, W.fixedReferences reference member]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionLoop

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionLoop.localCorrection_of_support
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedCorrectionLoop.sourceProper_of_oracle
