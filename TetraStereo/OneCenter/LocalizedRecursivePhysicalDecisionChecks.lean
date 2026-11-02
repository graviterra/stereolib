import TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliarySuccessfulObstruction
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysicalReport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Integration checks of the executable physical branch decision

**Actual-coordinate results** (the executable composition
`computedPairCount (actualCanonicalMolecule input) (coordinateCfg input)`, joined to accepted
source calibration by `computedPairCount_coordinateCfg_eq_physical`; no state, carrier or
factorial evaluation):

* 21-atom decorated cage: count `0` (`decorated_coordinate_count_zero`). The actual returned root
  descriptor is lowercase, so it **fails** this executable criterion
  (`decorated_returned_fails_coordinate_criterion`).
* 9-atom cyclic fixture: count `1` at every detected centre (`symmetric_coordinate_count_one`), and
  **every** descriptor in the actual report is lowercase and passes it
  (`symmetric_every_reported_passes_coordinate`).

**Generic detected-configuration results** (the decision applied, at proof level, to the accepted
noncomputable `detectedMultiCenterMolecule` with its accepted `detectedCfg`):
`decorated_computed_zero`, `decorated_returned_fails_computed_criterion`, `symmetric_computed_one`,
`symmetric_every_reported_passes`.

**By execution** (`#eval`, demonstration only, not used as proof): the full exhaustive search on a
5-atom explicit ring graph (`5! = 120` candidates); and, on the actual 21-atom source, the
executable branch reach set and the single arm-swap candidate. That candidate fails jointly only
at the hidden-parity cage centres.
-/

namespace TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks

open FinitePhysicalBranchTransport LocalizedActualPhysicalBranchDecision
open LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput (LocalizedAuxiliaryLabel)

/-! ## The decorated cage: an actual successful lowercase fails the computed criterion -/

section Decorated

open LocalizedRecursiveAuxiliaryParityDecoration LocalizedRecursiveAuxiliarySuccessfulObstruction

theorem decorated_computed_zero :
    computedPairCount decoratedCertified.detectedMultiCenterMolecule detectedCfg decRoot = 0 :=
  (computedPairCount_eq _ _ _).trans detectedPairCount

theorem decorated_returned_fails_computed_criterion :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      referenceState decReference decTarget = some descriptor ∧ descriptor.IsLowercase ∧
        ¬ (descriptor.IsLowercase ↔
          computedPairCount decoratedCertified.detectedMultiCenterMolecule detectedCfg decRoot =
            1) := by
  obtain ⟨descriptor, returned⟩ := root_returns
  have lower := root_returned_isLowercase returned
  refine ⟨descriptor, returned, lower, fun criterion => ?_⟩
  have count := criterion.mp lower
  rw [decorated_computed_zero] at count
  exact absurd count (by decide)

/-- **Executable actual-coordinate count, 21-atom input: `0`.** Derived from the accepted
original-domain calibration (`detectedDomain`) through `computedPairCount_coordinateCfg_eq_physical`
and the accepted physical count; no evaluation. -/
theorem decorated_coordinate_count_zero :
    computedPairCount (actualCanonicalMolecule decoratedCertified)
      (coordinateCfg decoratedCertified) decRoot = 0 :=
  (computedPairCount_coordinateCfg_eq_physical decoratedCertified detectedCfg decRoot
    detectedDomain).trans detectedPairCount

/-- **The actual returned lowercase fails the executable coordinate criterion.** -/
theorem decorated_returned_fails_coordinate_criterion :
    ∃ descriptor : LocalizedAuxiliaryLabel,
      referenceState decReference decTarget = some descriptor ∧ descriptor.IsLowercase ∧
        ¬ (descriptor.IsLowercase ↔
          computedPairCount (actualCanonicalMolecule decoratedCertified)
            (coordinateCfg decoratedCertified) decRoot = 1) := by
  obtain ⟨descriptor, returned⟩ := root_returns
  have lower := root_returned_isLowercase returned
  refine ⟨descriptor, returned, lower, fun criterion => ?_⟩
  have count := criterion.mp lower
  rw [decorated_coordinate_count_zero] at count
  exact absurd count (by decide)

end Decorated

/-! ## The nine-atom cyclic fixture: every reported descriptor passes -/

section Symmetric

open LocalizedRecursiveCyclicSymmetricFixture
open LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels (fixtureReference)

theorem symmetric_computed_one
    (center : symmetricCertified.detectedMultiCenterMolecule.Center) :
    computedPairCount symmetricCertified.detectedMultiCenterMolecule
        LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg center = 1 :=
  (computedPairCount_eq _ _ _).trans
    (LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedPairCountAtEveryRoot center)

theorem symmetric_every_reported_passes :
    ∀ (center : symmetricCertified.TetrahedralCenter) (descriptor : LocalizedAuxiliaryLabel),
      (center.1.val, some descriptor) ∈ analyze fixtureReference →
        descriptor.IsLowercase ∧
          (descriptor.IsLowercase ↔
            computedPairCount symmetricCertified.detectedMultiCenterMolecule
              LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg center = 1) := by
  intro center descriptor member
  obtain ⟨witness, witnessMember, witnessCase, _⟩ :=
    LocalizedRecursiveCyclicSymmetricFixturePhysicalReport.every_detected_report_entry_has_physical_reading
      center
  obtain ⟨c1, c1atom, c1state⟩ := (mem_analyze_iff fixtureReference _ _).mp member
  obtain ⟨c2, c2atom, c2state⟩ := (mem_analyze_iff fixtureReference _ _).mp witnessMember
  have c1eq : c1 = center := Subtype.ext (Fin.ext c1atom)
  have c2eq : c2 = center := Subtype.ext (Fin.ext c2atom)
  rw [c1eq] at c1state
  rw [c2eq] at c2state
  have same : descriptor = witness := Option.some.inj (c1state.symm.trans c2state)
  subst same
  have criterion : descriptor.IsLowercase ↔
      computedPairCount symmetricCertified.detectedMultiCenterMolecule
        LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg center = 1 := by
    rw [computedPairCount_eq]
    exact witnessCase
  exact ⟨criterion.mpr (symmetric_computed_one center), criterion⟩

/-- **Executable actual-coordinate count, 9-atom input: `1` at every detected centre.** Derived
from the accepted original-domain calibration (`detectedDomainAtEveryRoot`) and accepted counts. -/
theorem symmetric_coordinate_count_one (center : symmetricCertified.TetrahedralCenter) :
    computedPairCount (actualCanonicalMolecule symmetricCertified)
      (coordinateCfg symmetricCertified) center = 1 :=
  (computedPairCount_coordinateCfg_eq_physical symmetricCertified
    LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg center
    (LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedDomainAtEveryRoot center)).trans
    (LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedPairCountAtEveryRoot center)

/-- **Every actual reported descriptor passes the executable coordinate criterion.** -/
theorem symmetric_every_reported_passes_coordinate :
    ∀ (center : symmetricCertified.TetrahedralCenter) (descriptor : LocalizedAuxiliaryLabel),
      (center.1.val, some descriptor) ∈ analyze fixtureReference →
        descriptor.IsLowercase ∧
          (descriptor.IsLowercase ↔
            computedPairCount (actualCanonicalMolecule symmetricCertified)
              (coordinateCfg symmetricCertified) center = 1) := by
  intro center descriptor member
  obtain ⟨lower, _⟩ := symmetric_every_reported_passes center descriptor member
  exact ⟨lower, iff_of_true lower (symmetric_coordinate_count_one center)⟩

end Symmetric

/-! ## Executable demonstration on a 5-atom ring graph

Atoms `0` (root C), `1` (N), `2` (O), `3`, `4` (C). Bonds: `0-{1,2,3,4}`, `3-4`, `3-{1,2}`,
`4-{1,2}`. Centres `0, 3, 4`; the root branch of ligand `3` reaches both other centres (a ring).
The only root-fixing automorphism exchanging `3, 4` is the transposition, with identity local
frames. -/

def toyEdges : List (Fin 5 × Fin 5) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (3, 4), (3, 1), (3, 2), (4, 1), (4, 2)]

def toyBond (u v : Fin 5) : ℕ := if (u, v) ∈ toyEdges ∨ (v, u) ∈ toyEdges then 1 else 0

def toyGraph : MoleculeGraph (Fin 5) where
  atomZ := ![6, 7, 8, 6, 6]
  bond := toyBond
  bond_symm := by decide
  bond_self := by decide

def toyCenters : Finset (Fin 5) := {0, 3, 4}

def toyLig (c : Fin 5) : Fin 4 → Fin 5 :=
  if c = 0 then ![1, 2, 3, 4] else if c = 3 then ![0, 1, 2, 4] else ![0, 1, 2, 3]

private theorem toy_adj : ∀ c : Fin 5, c ∈ toyCenters → ∀ i : Fin 4, toyGraph.Adj c (toyLig c i) := by
  decide

private theorem toy_inj : ∀ c : Fin 5, c ∈ toyCenters → ∀ a b : Fin 4,
    toyLig c a = toyLig c b → a = b := by
  decide

private theorem toy_surj : ∀ c : Fin 5, c ∈ toyCenters → ∀ v : Fin 5,
    toyGraph.Adj c v → ∃ i : Fin 4, toyLig c i = v := by
  decide

def toyMol : MultiCenterMolecule (Fin 5) where
  mol := toyGraph
  centers := toyCenters
  ligandAtom := fun c _ => toyLig c
  ligandAtom_adj := toy_adj
  ligandAtom_injective := fun c hc a b h => toy_inj c hc a b h
  ligandAtom_surjective := toy_surj

def toyRoot : toyMol.Center := ⟨0, by decide⟩

/-- Opposite frames at the two ring centres. -/
def toyCfgOpp : toyMol.Configuration := fun d => if d.1 = 3 then Equiv.swap 0 1 else 1

/-- Equal frames at the two ring centres. -/
def toyCfgSame : toyMol.Configuration := fun _ => 1

/-- info: true -/
#guard_msgs in
#eval decideMirrorTransport toyMol toyCfgOpp toyRoot 2 3

/-- info: false -/
#guard_msgs in
#eval decideProperTransport toyMol toyCfgOpp toyRoot 2 3

/-- info: 1 -/
#guard_msgs in
#eval computedPairCount toyMol toyCfgOpp toyRoot

/-- info: 0 -/
#guard_msgs in
#eval computedPairCount toyMol toyCfgSame toyRoot

/-- info: 4 -/
#guard_msgs in
#eval (branchReachSet toyMol toyRoot 2).card

/-! ## Bounded executable checks on the actual 21-atom source -/

section DecoratedExecution

open LocalizedRecursiveAuxiliaryParityDecoration

def decoratedRoot : (actualCanonicalMolecule decoratedCertified).Center :=
  ⟨(0 : Fin 21), (degree_four_iff 0).mpr (Or.inl rfl)⟩

-- Arm A's deleted-root branch: `C*A`, its H and F, `C1A`, the three bridges, `C3A` and its H.
/-- info: 9 -/
#guard_msgs in
#eval (branchReachSet (actualCanonicalMolecule decoratedCertified) decoratedRoot 2).card

-- The arm swap is not a mirror transport for the coordinate configuration.
/-- info: false -/
#guard_msgs in
#eval candidateOK (actualCanonicalMolecule decoratedCertified) (coordinateCfg decoratedCertified)
  decoratedRoot 2 3 true armSwapPerm

-- Reached centres where the arm swap violates the mirror sign law (atom indices): only the far
-- bridgehead `C3A`; the mirror law holds at `C*A` and `C1A`.
/-- info: {11} -/
#guard_msgs in
#eval ((Finset.univ : Finset (actualCanonicalMolecule decoratedCertified).Center).filter
    (fun d => d.1 ∈ branchReachSet (actualCanonicalMolecule decoratedCertified) decoratedRoot 2 ∧
      signOK (actualCanonicalMolecule decoratedCertified) (coordinateCfg decoratedCertified) true
        armSwapPerm d = false)).val.map (fun d => d.1.val)

-- Reached centres where it violates the proper sign law: `C*A` and `C1A`.
/-- info: {3, 6} -/
#guard_msgs in
#eval ((Finset.univ : Finset (actualCanonicalMolecule decoratedCertified).Center).filter
    (fun d => d.1 ∈ branchReachSet (actualCanonicalMolecule decoratedCertified) decoratedRoot 2 ∧
      signOK (actualCanonicalMolecule decoratedCertified) (coordinateCfg decoratedCertified) false
        armSwapPerm d = false)).val.map (fun d => d.1.val)

end DecoratedExecution

end TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.decorated_computed_zero
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.decorated_returned_fails_computed_criterion
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.symmetric_computed_one
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.symmetric_every_reported_passes
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.decorated_coordinate_count_zero
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.decorated_returned_fails_coordinate_criterion
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.symmetric_coordinate_count_one
assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursivePhysicalDecisionChecks.symmetric_every_reported_passes_coordinate
