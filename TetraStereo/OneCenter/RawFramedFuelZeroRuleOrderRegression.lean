import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! # Fuel-zero Rule-2/Rule-1a precedence regression

`FrameRuntime.compareBranch?` at fuel `0` reads only the immediate labels of the paired branch
roots (`throughLabels?`: Rule 1a, then framed Rule 1b, then Rule 2) and never expands a deeper
sphere.  Consequently a successful fuel-zero comparison can decide on Rule 2 (isotopic mass)
*after* a Rule-1a tie at the first sphere, even though an exhaustive Rule-1a pass over the next
sphere would already find a difference.

This module records one actual, finite, acyclic, all-tetrahedral-frame regression witness built
from the real parser:

* source: `[C@H]([13CH2]C)(CF)Br`
* expanded with `withExplicitHydrogens`;
* compared branches: the `13C` ethyl arm (atom `1`) against the isotope-unspecified fluoromethyl arm
  (atom `3`).

At fuel `0` the immediate labels tie under Rule 1a (both carbon), tie under framed Rule 1b
(both distance `1`), and then Rule 2 strictly orders the specified isotope above the unspecified-isotope carbon, giving `Ordering.gt`.
At fuel `1` the exhaustive Rule-1a sphere compares the ethyl arm's deeper `CH3` carbon against the fluoromethyl arm's `F`, giving `Ordering.lt`.

The regression target is deliberately *not* a claim about the final public descriptor: the two
bounded comparisons merely have different successful results.  It shows that an unqualified
"successful fuel monotonicity" law for `compareBranch?` is false, because the fuel-zero branch
reaches a successful but premature Rule-2 answer.  A correct monotonicity statement needs an
derived adequacy condition. `FuelStableFrom` below merely names the desired eventual stability;
it does not derive such a condition. A zero-case guard removes this witness but does not prove
the general law. -/

namespace TetraStereo.OneCenter

open RawMolecule
open TetraStereo.OneCenter.FrameRuntime

namespace RawFramedFuelZeroRuleOrderRegression

/-! ### The actual source, parser output, and explicit-hydrogen expansion -/

/-- Real OpenSMILES input: a stereogenic carbon carrying H, an isotopically labelled ethyl arm,
a fluoromethyl arm, and bromine. -/
def source : String := "[C@H]([13CH2]C)(CF)Br"

/-- Exact parser output for `source`, written as a concrete constructor so that the parse
equality and every later runtime fact are checkable by the kernel. -/
def parsedMolecule : RawMolecule where
  atoms :=
    [ { element := Element.C
        explicitHydrogens? := some 1
        tetrahedral? := some TetrahedralInputParity.anticlockwise },
      { element := Element.C
        isotope? := some 13
        explicitHydrogens? := some 2 },
      AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.C,
      AtomSpec.aliphatic Element.F,
      AtomSpec.aliphatic Element.Br ]
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single },
      { source := 1, target := 2, kind := ParsedBondKind.single },
      { source := 0, target := 3, kind := ParsedBondKind.single },
      { source := 3, target := 4, kind := ParsedBondKind.single },
      { source := 0, target := 5, kind := ParsedBondKind.single } ]
  neighborOrder := [[1, 3, 5], [0, 2], [1], [0, 4], [3], [0]]
  introductionPredecessors := [none, some 0, some 1, some 0, some 3, some 0]

/-- The actual parser accepts the source string and returns exactly the written constructor. -/
theorem parsedMolecule_parse : parseOpenSMILES source = .ok parsedMolecule := by
  rfl

/-- The source molecule with every implicit hydrogen materialised as a real atom. -/
def expandedMolecule : RawMolecule := parsedMolecule.withExplicitHydrogens

/-! ### The shared profile and the two first-sphere branch cursors -/

def rootNode : CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

/-- First atom of the ethyl arm: the isotopically labelled `[13CH2]` carbon. -/
def ethylNode : CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom }

/-- First atom of the fluoromethyl arm: the `CH2` carbon attached to `F`. -/
def fluoromethylNode : CanonicalBranchNode :=
  { atom := 3, parent := 0, history := [3, 0], provenance := .realAtom }

def ethylCursor : CanonicalRerootCursor :=
  { node := ethylNode, previous? := some rootNode }

def fluoromethylCursor : CanonicalRerootCursor :=
  { node := fluoromethylNode, previous? := some rootNode }

def ethyl : Cursor := .actual ethylCursor

def fluoromethyl : Cursor := .actual fluoromethylCursor

/-- The actual shared profile returned for the expanded molecule at the stereogenic root. -/
def profileOption : Option Profile := profile? expandedMolecule rootNode

def fallbackProfile : Profile :=
  { center := rootNode, frame := { originHistory := [0] }, generated := [] }

/-- The actually computed shared profile (the fallback is unreachable; `profile_success` proves
the option is `some`). -/
def profile : Profile := profileOption.getD fallbackProfile

/-- The actual `profile?` call succeeds on the expanded molecule. -/
theorem profile_success : profileOption = some profile := by
  decide

/-- Both compared first-sphere nodes are members of the generated shared-profile tree. -/
theorem ethyl_mem_generated : ethylNode ∈ profile.generated := by
  decide

theorem fluoromethyl_mem_generated : fluoromethylNode ∈ profile.generated := by
  decide

/-- Both actual cursors validate against the shared profile at framed distance `1`. -/
theorem ethyl_cursor_valid : cursor? expandedMolecule profile ethyl = some 1 := by
  decide

theorem fluoromethyl_cursor_valid : cursor? expandedMolecule profile fluoromethyl = some 1 := by
  decide

/-! ### Immediate labels: Rule 1a tie, framed Rule 1b tie, Rule 2 orders the specified isotope above the unspecified isotope -/

theorem immediate_rule1a_eq :
    label? expandedMolecule profile true .rule1a ethyl fluoromethyl = some .eq := by
  decide

theorem immediate_rule1b_eq :
    label? expandedMolecule profile true .rule1b ethyl fluoromethyl = some .eq := by
  decide

theorem immediate_rule2_gt :
    label? expandedMolecule profile true .rule2 ethyl fluoromethyl = some .gt := by
  decide

theorem through_labels_rule2_gt :
    throughLabels? expandedMolecule profile true .rule2 ethyl fluoromethyl = some .gt := by
  decide

/-! ### The fuel-zero answer and the exhaustive Rule-1a answer -/

/-- Fuel `0`, stage `.rule2`: the successful bounded comparison is the Rule-2 isotope result. -/
theorem zero_fuel_compare_gt :
    compareBranch? expandedMolecule profile true 0 .rule2 ethyl fluoromethyl = some .gt := by
  decide

/-- Fuel `1`, stage `.rule2`: exhaustive Rule 1a reaches the deeper `CH3` carbon versus `F` sphere and
returns `lt`, contradicting the fuel-zero answer. -/
theorem one_fuel_compare_lt :
    compareBranch? expandedMolecule profile true 1 .rule2 ethyl fluoromethyl = some .lt := by
  decide

/-- The fuel-one Rule-1a pass itself is the decisive exhaustive comparison. -/
theorem exhaustive_rule1a_one_fuel_lt :
    compareRule? expandedMolecule profile true
      (compareBranch? expandedMolecule profile true 0 .rule2) .rule1a 1
      [(ethyl, fluoromethyl)] = some .lt := by
  decide

/-- First deeper pair behind the Rule-1a decision: the ethyl `CH3` carbon against the
fluoromethyl `F` atom. -/
def deeperEthylCursor : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 1, history := [2, 1, 0], provenance := .realAtom }
    previous? := some ethylNode }

def deeperFluoromethylCursor : CanonicalRerootCursor :=
  { node := { atom := 4, parent := 3, history := [4, 3, 0], provenance := .realAtom }
    previous? := some fluoromethylNode }

theorem deeper_rule1a_label_lt :
    label? expandedMolecule profile true .rule1a
      (.actual deeperEthylCursor) (.actual deeperFluoromethylCursor) = some .lt := by
  decide

/-! ### The failed unconditional monotonicity law and the required qualification -/

/-- The unqualified statement "a successful fuel-`n` comparison has the same result at fuel
`n + 1`" is false for `compareBranch?`. -/
theorem unqualified_successful_fuel_monotonicity_false :
    ¬ (∀ (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
        (stage : CanonicalRuleStage) (fuel : Nat) (left right : Cursor) (ord : Ordering),
        compareBranch? mol profile authoritative fuel stage left right = some ord →
        compareBranch? mol profile authoritative (fuel + 1) stage left right = some ord) := by
  intro monotone
  have step := monotone expandedMolecule profile true .rule2 0 ethyl fluoromethyl .gt
    zero_fuel_compare_gt
  rw [one_fuel_compare_lt] at step
  exact absurd step (by decide)

/-- The desired eventual-stability property, named for stating the remaining obligation.
This definition does not provide an independently derived structural adequacy condition. -/
def FuelStableFrom (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (base : Nat) (left right : Cursor) (ord : Ordering) : Prop :=
  ∀ fuel, base ≤ fuel →
    compareBranch? mol profile authoritative fuel stage left right = some ord

/-- Direct unpacking of eventual stability; this does not establish an adequacy threshold. -/
theorem monotone_of_fuelStableFrom
    (mol : RawMolecule) (profile : Profile) (authoritative : Bool)
    (stage : CanonicalRuleStage) (base fuel : Nat) (left right : Cursor) (ord : Ordering)
    (stable : FuelStableFrom mol profile authoritative stage base left right ord)
    (bound : base ≤ fuel) :
    compareBranch? mol profile authoritative fuel stage left right = some ord ∧
      compareBranch? mol profile authoritative (fuel + 1) stage left right = some ord :=
  ⟨stable fuel bound, stable (fuel + 1) (Nat.le_succ_of_le bound)⟩

/-- The witness itself shows that the fuel-zero result is not stable: `gt` at fuel `0` is `lt`
at fuel `1`. -/
theorem zero_fuel_gt_not_stable :
    ¬ FuelStableFrom expandedMolecule profile true .rule2 0 ethyl fluoromethyl .gt := by
  intro stable
  have step := stable 1 (by decide)
  rw [one_fuel_compare_lt] at step
  exact absurd step (by decide)

end RawFramedFuelZeroRuleOrderRegression

end TetraStereo.OneCenter

/-! Kernel-authority guards for every declaration in this regression module. -/

assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.source
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.parsedMolecule
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.parsedMolecule_parse
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.expandedMolecule
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.rootNode
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.ethylNode
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.fluoromethylNode
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.ethylCursor
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.fluoromethylCursor
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.ethyl
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.fluoromethyl
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.profileOption
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.fallbackProfile
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.profile
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.profile_success
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.ethyl_mem_generated
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.fluoromethyl_mem_generated
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.ethyl_cursor_valid
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.fluoromethyl_cursor_valid
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.immediate_rule1a_eq
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.immediate_rule1b_eq
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.immediate_rule2_gt
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.through_labels_rule2_gt
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.zero_fuel_compare_gt
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.one_fuel_compare_lt
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.exhaustive_rule1a_one_fuel_lt
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.deeperEthylCursor
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.deeperFluoromethylCursor
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.deeper_rule1a_label_lt
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.unqualified_successful_fuel_monotonicity_false
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.FuelStableFrom
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.monotone_of_fuelStableFrom
assert_kernel_only TetraStereo.OneCenter.RawFramedFuelZeroRuleOrderRegression.zero_fuel_gt_not_stable
