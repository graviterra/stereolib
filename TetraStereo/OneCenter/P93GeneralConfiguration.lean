import TetraStereo.OneCenter.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent IUPAC P-93.1 configuration semantics

This module transcribes the mathematical content of P-93.1.1--P-93.1.4 independently of the
production descriptor pipeline.  It distinguishes:

* an absolute located configuration;
* a relative configuration, which is the global-enantiomer equivalence class of one absolute
  representative;
* a racemate, which is an equimolar mixture of a distinct enantiomeric pair; and
* an `ambo` mixture, which contains a named configuration and its epimer at one stated unit in
  non-equimolar proportions.

The module deliberately does not choose locants, perceive stereogenic units, or assign local CIP
descriptors.  Those are separate conformance obligations.

## Global mirror versus local epimer inversion

Two different operations act on `Descriptor`:

* `Descriptor.enantiomer` is the **global molecular mirror**.  It exchanges everyday handed
  descriptors such as `R`/`S` and `M`/`P`, but it fixes the lower-case pseudoasymmetric/relative
  descriptors `r`/`s` (P-91.2.1.1).  A whole-molecule reflection therefore does not change an
  `r`/`s` designation.
* `Descriptor.invert` is the **local epimer inversion at one stated unit**.  Inverting a single
  stereogenic unit exchanges *every* enantiomorphic pair, including `r ↔ s`, while leaving the
  descriptors at all other units untouched.

Using one operation for both purposes is a source defect: it either makes a global mirror change
`r`/`s`, or makes an `ambo` inversion at one unit leave `r`/`s` unchanged.  The two operations
below are therefore kept separate, and `invertedAt` uses the local one.
-/

namespace BlueBookP93.GeneralConfiguration

/-- Enantiomorphic local descriptors used by the general configuration clauses.  This vocabulary
is intentionally about configuration sense, not typographical scope (`rel`, `rac`, or a star). -/
inductive Descriptor where
  | capitalR
  | capitalS
  | lowercaseR
  | lowercaseS
  | axialR
  | axialS
  | capitalM
  | capitalP
  deriving DecidableEq, Repr

namespace Descriptor

def symbol : Descriptor → String
  | .capitalR => "R"
  | .capitalS => "S"
  | .lowercaseR => "r"
  | .lowercaseS => "s"
  | .axialR => "Ra"
  | .axialS => "Sa"
  | .capitalM => "M"
  | .capitalP => "P"

/-- Global molecular enantiomer (the mirror image of the whole molecular entity).  Handed
descriptors are exchanged; the lower-case `r`/`s` descriptors are pseudoasymmetric/relative and
are fixed by a global reflection, as required by P-91.2.1.1.

This operation is *not* the local epimer action at one unit; use `invert` for that. -/
def enantiomer : Descriptor → Descriptor
  | .capitalR => .capitalS
  | .capitalS => .capitalR
  | .lowercaseR => .lowercaseR
  | .lowercaseS => .lowercaseS
  | .axialR => .axialS
  | .axialS => .axialR
  | .capitalM => .capitalP
  | .capitalP => .capitalM

/-- Local epimer inversion at one stated stereogenic unit.  Unlike the global molecular mirror
`enantiomer`, this exchanges every enantiomorphic pair, including `lowercaseR ↔ lowercaseS`. -/
def invert : Descriptor → Descriptor
  | .capitalR => .capitalS
  | .capitalS => .capitalR
  | .lowercaseR => .lowercaseS
  | .lowercaseS => .lowercaseR
  | .axialR => .axialS
  | .axialS => .axialR
  | .capitalM => .capitalP
  | .capitalP => .capitalM

@[simp] theorem enantiomer_capitalR : Descriptor.capitalR.enantiomer = .capitalS := rfl

@[simp] theorem enantiomer_capitalS : Descriptor.capitalS.enantiomer = .capitalR := rfl

@[simp] theorem enantiomer_lowercaseR :
    Descriptor.lowercaseR.enantiomer = .lowercaseR := rfl

@[simp] theorem enantiomer_lowercaseS :
    Descriptor.lowercaseS.enantiomer = .lowercaseS := rfl

@[simp] theorem enantiomer_axialR : Descriptor.axialR.enantiomer = .axialS := rfl

@[simp] theorem enantiomer_axialS : Descriptor.axialS.enantiomer = .axialR := rfl

@[simp] theorem enantiomer_capitalM : Descriptor.capitalM.enantiomer = .capitalP := rfl

@[simp] theorem enantiomer_capitalP : Descriptor.capitalP.enantiomer = .capitalM := rfl

@[simp] theorem invert_capitalR : Descriptor.capitalR.invert = .capitalS := rfl

@[simp] theorem invert_capitalS : Descriptor.capitalS.invert = .capitalR := rfl

@[simp] theorem invert_lowercaseR : Descriptor.lowercaseR.invert = .lowercaseS := rfl

@[simp] theorem invert_lowercaseS : Descriptor.lowercaseS.invert = .lowercaseR := rfl

@[simp] theorem invert_axialR : Descriptor.axialR.invert = .axialS := rfl

@[simp] theorem invert_axialS : Descriptor.axialS.invert = .axialR := rfl

@[simp] theorem invert_capitalM : Descriptor.capitalM.invert = .capitalP := rfl

@[simp] theorem invert_capitalP : Descriptor.capitalP.invert = .capitalM := rfl

@[simp] theorem enantiomer_involutive (descriptor : Descriptor) :
    descriptor.enantiomer.enantiomer = descriptor := by
  cases descriptor <;> rfl

@[simp] theorem invert_involutive (descriptor : Descriptor) :
    descriptor.invert.invert = descriptor := by
  cases descriptor <;> rfl

/-- The global mirror and the local epimer action commute pointwise.  This is the algebraic
shadow of the fact that they act independently on the `R/S` and `r/s` pairs. -/
theorem enantiomer_invert_comm (descriptor : Descriptor) :
    descriptor.enantiomer.invert = descriptor.invert.enantiomer := by
  cases descriptor <;> rfl

/-- Symmetric form of `enantiomer_invert_comm`. -/
theorem invert_enantiomer_comm (descriptor : Descriptor) :
    descriptor.invert.enantiomer = descriptor.enantiomer.invert :=
  (enantiomer_invert_comm descriptor).symm

/-- Descriptors for which P-93.1 supplies a source-supported choice of displayed representative.
Mirror-invariant pseudoasymmetric/relative descriptors (`lowercaseR`, `lowercaseS`) cannot select
an enantiomeric representative.  This follows the closed canonical P-93 descriptor policy
(`P93CanonicalDescriptor.GeneralRepresentativeEligible`). -/
def RepresentativeEligible : Descriptor → Prop
  | .capitalR | .capitalS | .axialR | .axialS | .capitalM | .capitalP => True
  | .lowercaseR | .lowercaseS => False

/-- Closed representative polarity for the source-supported descriptor pairs.  Values outside
`RepresentativeEligible` are false and have no authority meaning, following the canonical P-93
descriptor policy. -/
def PreferredAtLowest : Descriptor → Prop
  | .capitalR | .axialR | .capitalM => True
  | _ => False

@[simp] theorem representativeEligible_capitalR :
    Descriptor.capitalR.RepresentativeEligible := trivial

@[simp] theorem representativeEligible_capitalS :
    Descriptor.capitalS.RepresentativeEligible := trivial

@[simp] theorem representativeEligible_axialR :
    Descriptor.axialR.RepresentativeEligible := trivial

@[simp] theorem representativeEligible_axialS :
    Descriptor.axialS.RepresentativeEligible := trivial

@[simp] theorem representativeEligible_capitalM :
    Descriptor.capitalM.RepresentativeEligible := trivial

@[simp] theorem representativeEligible_capitalP :
    Descriptor.capitalP.RepresentativeEligible := trivial

@[simp] theorem not_representativeEligible_lowercaseR :
    ¬ Descriptor.lowercaseR.RepresentativeEligible := by
  simp [RepresentativeEligible]

@[simp] theorem not_representativeEligible_lowercaseS :
    ¬ Descriptor.lowercaseS.RepresentativeEligible := by
  simp [RepresentativeEligible]

/-- Eligibility is invariant under the global molecular mirror. -/
@[simp] theorem enantiomer_representativeEligible_iff (descriptor : Descriptor) :
    descriptor.enantiomer.RepresentativeEligible ↔
      descriptor.RepresentativeEligible := by
  cases descriptor <;> simp [RepresentativeEligible]

/-- Eligibility is invariant under local epimer inversion. -/
@[simp] theorem invert_representativeEligible_iff (descriptor : Descriptor) :
    descriptor.invert.RepresentativeEligible ↔
      descriptor.RepresentativeEligible := by
  cases descriptor <;> simp [RepresentativeEligible]

/-- Exact characterization: the global mirror moves a descriptor precisely when that descriptor
is an eligible representative descriptor.  In particular the universal statement
`enantiomer d ≠ d` is false for `r`/`s`. -/
theorem enantiomer_ne_iff_eligible (descriptor : Descriptor) :
    descriptor.enantiomer ≠ descriptor ↔ descriptor.RepresentativeEligible := by
  cases descriptor <;> simp [RepresentativeEligible]

/-- Exact fixed-point characterization of the global mirror. -/
theorem enantiomer_eq_self_iff_not_eligible (descriptor : Descriptor) :
    descriptor.enantiomer = descriptor ↔ ¬ descriptor.RepresentativeEligible := by
  cases descriptor <;> simp [RepresentativeEligible]

/-- Eligible variant of the former universal `enantiomer_ne`. -/
theorem enantiomer_ne_of_eligible (descriptor : Descriptor)
    (eligible : descriptor.RepresentativeEligible) :
    descriptor.enantiomer ≠ descriptor :=
  (enantiomer_ne_iff_eligible descriptor).2 eligible

/-- Non-fixed variant of the former universal `enantiomer_ne`. -/
theorem enantiomer_ne_of_ne (descriptor : Descriptor)
    (nonfixed : descriptor.enantiomer ≠ descriptor) :
    descriptor.RepresentativeEligible :=
  (enantiomer_ne_iff_eligible descriptor).1 nonfixed

/-- Fixed descriptors are exactly the ineligible ones. -/
theorem enantiomer_eq_self_of_not_eligible (descriptor : Descriptor)
    (ineligible : ¬ descriptor.RepresentativeEligible) :
    descriptor.enantiomer = descriptor :=
  (enantiomer_eq_self_iff_not_eligible descriptor).2 ineligible

/-- The former universal `enantiomer_ne` is refutable: the pseudoasymmetric `r` descriptor is
fixed by the global molecular mirror. -/
theorem not_universal_enantiomer_ne :
    ¬ ∀ descriptor : Descriptor, descriptor.enantiomer ≠ descriptor := by
  intro universal
  exact universal .lowercaseR rfl

/-- The former universal preferred-member flip is refutable: for the fixed `r` descriptor the
left side is false while the right side is true. -/
theorem not_universal_enantiomer_preferredAtLowest_iff :
    ¬ ∀ descriptor : Descriptor,
      descriptor.enantiomer.PreferredAtLowest ↔ ¬ descriptor.PreferredAtLowest := by
  intro universal
  have fixedFlip := universal .lowercaseR
  simp [PreferredAtLowest] at fixedFlip

/-- Eligibility-conditioned polarity flip under the global molecular mirror.  The hypothesis is
necessary: `lowercaseR` is fixed and therefore cannot flip its displayed polarity. -/
theorem enantiomer_preferredAtLowest_iff_of_eligible (descriptor : Descriptor)
    (eligible : descriptor.RepresentativeEligible) :
    descriptor.enantiomer.PreferredAtLowest ↔ ¬ descriptor.PreferredAtLowest := by
  cases descriptor <;> simp_all [RepresentativeEligible, PreferredAtLowest]

/-- Non-fixed variant of the polarity flip, matching the canonical P-93 policy field. -/
theorem enantiomer_preferredAtLowest_iff_of_ne (descriptor : Descriptor)
    (nonfixed : descriptor.enantiomer ≠ descriptor) :
    descriptor.enantiomer.PreferredAtLowest ↔ ¬ descriptor.PreferredAtLowest :=
  enantiomer_preferredAtLowest_iff_of_eligible descriptor
    ((enantiomer_ne_iff_eligible descriptor).1 nonfixed)

/-- Local epimer inversion also flips the displayed polarity of an eligible representative. -/
theorem invert_preferredAtLowest_iff_of_eligible (descriptor : Descriptor)
    (eligible : descriptor.RepresentativeEligible) :
    descriptor.invert.PreferredAtLowest ↔ ¬ descriptor.PreferredAtLowest := by
  cases descriptor <;> simp_all [RepresentativeEligible, PreferredAtLowest]

end Descriptor

/-- One descriptor at each stated locant.  The locant type is abstract because P-93 applies the
same scope rules to atom locants, axes, planes, helices, and compound locant forms. -/
@[ext] structure LocatedConfiguration (Locant : Type*) where
  assignments : List (Locant × Descriptor)
  locantsNodup : (assignments.map Prod.fst).Nodup

namespace LocatedConfiguration

variable {Locant : Type*}

/-- Representative-selection clause shared by `rel-` and `rac-`: among the **eligible**
mirror-variant descriptors, the one at the lowest stated locant must be the displayed member of
its enantiomorphic pair.  Descriptors that are fixed by the global molecular mirror (notably
`r`/`s`) are ignored for selection even when they occur at a lower locant. -/
def IsCanonicalNamedRepresentative [LinearOrder Locant]
    (configuration : LocatedConfiguration Locant) : Prop :=
  ∃ leading ∈ configuration.assignments,
    leading.2.RepresentativeEligible ∧
    leading.2.enantiomer ≠ leading.2 ∧
    (∀ assignment ∈ configuration.assignments,
      assignment.2.RepresentativeEligible →
      assignment.2.enantiomer ≠ assignment.2 →
        leading.1 ≤ assignment.1) ∧
    leading.2.PreferredAtLowest

/-- Mirror every stated stereogenic unit by the global molecular enantiomer, leaving locants
fixed.  Fixed descriptors such as `r`/`s` are unchanged. -/
def globallyInverted (configuration : LocatedConfiguration Locant) :
    LocatedConfiguration Locant where
  assignments := configuration.assignments.map fun assignment =>
    (assignment.1, assignment.2.enantiomer)
  locantsNodup := by
    simpa [List.map_map, Function.comp_def] using configuration.locantsNodup

@[simp] theorem globallyInverted_assignments (configuration : LocatedConfiguration Locant) :
    configuration.globallyInverted.assignments =
      configuration.assignments.map fun assignment =>
        (assignment.1, assignment.2.enantiomer) :=
  rfl

@[simp] theorem globallyInverted_involutive (configuration : LocatedConfiguration Locant) :
    configuration.globallyInverted.globallyInverted = configuration := by
  ext
  simp [globallyInverted, List.map_map, Function.comp_def]

variable [DecidableEq Locant]

/-- Invert the descriptor of an assignment at exactly one target locant using the local epimer
operation.  Unlike `globallyInverted`, this exchanges `lowercaseR ↔ lowercaseS`. -/
def invertAssignmentAt (target : Locant) (assignment : Locant × Descriptor) :
    Locant × Descriptor :=
  if assignment.1 = target then (assignment.1, assignment.2.invert) else assignment

@[simp] theorem invertAssignmentAt_fst (target : Locant)
    (assignment : Locant × Descriptor) :
    (invertAssignmentAt target assignment).1 = assignment.1 := by
  by_cases same : assignment.1 = target <;>
    simp [invertAssignmentAt, same]

@[simp] theorem invertAssignmentAt_involutive (target : Locant)
    (assignment : Locant × Descriptor) :
    invertAssignmentAt target (invertAssignmentAt target assignment) = assignment := by
  rcases assignment with ⟨locant, descriptor⟩
  by_cases same : locant = target <;>
    simp [invertAssignmentAt, same]

/-- Form the epimer at exactly one stated locant; absent locants leave the configuration
unchanged.  This is the local P-93.1.4 action, not the global molecular mirror. -/
def invertedAt (target : Locant) (configuration : LocatedConfiguration Locant) :
    LocatedConfiguration Locant where
  assignments := configuration.assignments.map (invertAssignmentAt target)
  locantsNodup := by
    simpa [List.map_map, Function.comp_def] using configuration.locantsNodup

@[simp] theorem invertedAt_assignments (target : Locant)
    (configuration : LocatedConfiguration Locant) :
    (configuration.invertedAt target).assignments =
      configuration.assignments.map (invertAssignmentAt target) :=
  rfl

@[simp] theorem invertedAt_involutive (target : Locant)
    (configuration : LocatedConfiguration Locant) :
    (configuration.invertedAt target).invertedAt target = configuration := by
  ext
  simp [invertedAt, List.map_map, Function.comp_def]

/-- The global molecular mirror and a local epimer inversion commute.  In particular the order in
which a whole-molecule mirror and a one-unit inversion are applied is immaterial. -/
theorem globallyInverted_invertedAt_comm (target : Locant)
    (configuration : LocatedConfiguration Locant) :
    (configuration.globallyInverted).invertedAt target =
      (configuration.invertedAt target).globallyInverted := by
  apply LocatedConfiguration.ext
  simp only [globallyInverted, invertedAt, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro assignment _
  rcases assignment with ⟨locant, descriptor⟩
  by_cases same : locant = target
  · simp [invertAssignmentAt, same, Descriptor.enantiomer_invert_comm]
  · simp [invertAssignmentAt, same]

end LocatedConfiguration

/-- P-93.1.2.1: two absolute representatives state the same relative configuration exactly when
one is the other or its whole-molecule enantiomer. -/
def RelativeEquivalent {Locant : Type*}
    (left right : LocatedConfiguration Locant) : Prop :=
  right = left ∨ right = left.globallyInverted

theorem relativeEquivalent_refl {Locant : Type*}
    (configuration : LocatedConfiguration Locant) :
    RelativeEquivalent configuration configuration :=
  Or.inl rfl

theorem relativeEquivalent_symm {Locant : Type*}
    {left right : LocatedConfiguration Locant}
    (related : RelativeEquivalent left right) :
    RelativeEquivalent right left := by
  rcases related with same | mirror
  · exact Or.inl same.symm
  · right
    calc
      left = left.globallyInverted.globallyInverted :=
        left.globallyInverted_involutive.symm
      _ = right.globallyInverted :=
        (congrArg LocatedConfiguration.globallyInverted mirror).symm

theorem relativeEquivalent_trans {Locant : Type*}
    {first second third : LocatedConfiguration Locant}
    (firstSecond : RelativeEquivalent first second)
    (secondThird : RelativeEquivalent second third) :
    RelativeEquivalent first third := by
  rcases firstSecond with same₁ | mirror₁
  · subst second
    exact secondThird
  · rcases secondThird with same₂ | mirror₂
    · exact Or.inr (same₂.trans mirror₁)
    · left
      calc
        third = second.globallyInverted := mirror₂
        _ = first.globallyInverted.globallyInverted := congrArg LocatedConfiguration.globallyInverted mirror₁
        _ = first := first.globallyInverted_involutive

/-- The actual denotation of a `rel-` configuration: an equivalence class with two
mirror-related representatives unless the molecular entity is achiral for reasons outside this local list. -/
def relativeSetoid (Locant : Type*) : Setoid (LocatedConfiguration Locant) where
  r := RelativeEquivalent
  iseqv :=
    { refl := relativeEquivalent_refl
      symm := relativeEquivalent_symm
      trans := relativeEquivalent_trans }

def RelativeConfiguration (Locant : Type*) :=
  Quotient (relativeSetoid Locant)

def LocatedConfiguration.toRelative {Locant : Type*}
    (configuration : LocatedConfiguration Locant) : RelativeConfiguration Locant :=
  Quotient.mk _ configuration

@[simp] theorem globallyInverted_same_relative_class {Locant : Type*}
    (configuration : LocatedConfiguration Locant) :
    configuration.globallyInverted.toRelative = configuration.toRelative := by
  apply Quotient.sound
  exact Or.inr configuration.globallyInverted_involutive.symm

/-! ## Absolute and relative notation scope -/

inductive AssignmentScope where
  | absolute
  | relative (group : ℕ)
  deriving DecidableEq, Repr

structure ScopedAssignment (Locant : Type*) where
  locant : Locant
  descriptor : Descriptor
  scope : AssignmentScope
  deriving Repr

structure ScopePlan (Locant : Type*) where
  assignments : List (ScopedAssignment Locant)
  deriving Repr

namespace ScopePlan

variable {Locant : Type*}

def HasAbsolute (plan : ScopePlan Locant) : Prop :=
  ∃ assignment ∈ plan.assignments, assignment.scope = .absolute

def HasRelative (plan : ScopePlan Locant) : Prop :=
  ∃ assignment ∈ plan.assignments, ∃ group, assignment.scope = .relative group

/-- `rel-` is a whole-name prefix, so it applies only when every stated unit belongs to the same
relative-configuration group and there is at least one stated unit. -/
def GlobalRelApplicable (plan : ScopePlan Locant) : Prop :=
  ∃ group, plan.assignments ≠ [] ∧
    ∀ assignment ∈ plan.assignments, assignment.scope = .relative group

/-- P-93.1.2.2's mixed case: independently absolute units coexist with a relative group. -/
def MixedAbsoluteRelative (plan : ScopePlan Locant) : Prop :=
  plan.HasAbsolute ∧ plan.HasRelative

theorem mixedAbsoluteRelative_not_globalRelApplicable (plan : ScopePlan Locant)
    (mixed : plan.MixedAbsoluteRelative) :
    ¬plan.GlobalRelApplicable := by
  rintro ⟨group, _, allRelative⟩
  rcases mixed.1 with ⟨assignment, member, absolute⟩
  have relative := allRelative assignment member
  rw [absolute] at relative
  cases relative

end ScopePlan

/-- Typographical treatment required for a local descriptor in P-93.1.2. -/
inductive DescriptorTypography where
  | plain
  | starred
  deriving DecidableEq, Repr

/-- Preferred local typography for the mixed case of P-93.1.2.2.  Absolute units retain plain
descriptors; units in the unrelated relative group require starred descriptors because `rel-`
would incorrectly scope over the entire name. -/
def mixedTypography {Locant : Type*} (assignment : ScopedAssignment Locant) :
    DescriptorTypography :=
  match assignment.scope with
  | .absolute => .plain
  | .relative _ => .starred

/-! ## Racemates and `ambo` mixtures -/

structure BinaryMixture (Species : Type*) where
  first : Species
  second : Species
  /-- Mole fraction of `first`; that of `second` is `1 - firstFraction`. -/
  firstFraction : ℚ

namespace BinaryMixture

variable {Species : Type*}

def Valid (mixture : BinaryMixture Species) : Prop :=
  0 < mixture.firstFraction ∧ mixture.firstFraction < 1

def response (mixture : BinaryMixture Species) (measurement : Species → ℚ) : ℚ :=
  mixture.firstFraction * measurement mixture.first +
    (1 - mixture.firstFraction) * measurement mixture.second

end BinaryMixture

/-- Source-level composition information when the authority specifies only whether a binary
mixture is equimolar.  P-93.1.4 says “plus a proportion of the epimer” and does not publish a
numerical mole fraction, so inventing one would make the formal observation stronger than the
source. -/
inductive BinaryCompositionClass where
  | equimolar
  | nonEquimolar
  deriving DecidableEq, Repr

/-- A qualitative two-species mixture retaining exactly the composition information printed by
the authority. -/
structure QualitativeBinaryMixture (Species : Type*) where
  first : Species
  second : Species
  composition : BinaryCompositionClass

/-- P-93.1.3: a racemate is an equimolecular mixture of a distinct pair of enantiomers.  The pair
is related by the **global molecular mirror**, so `r`/`s` designations stay fixed; a configuration
whose global mirror is itself cannot be a racemate. -/
def IsRacemate {Locant : Type*}
    (mixture : BinaryMixture (LocatedConfiguration Locant)) : Prop :=
  mixture.Valid ∧
  mixture.second = mixture.first.globallyInverted ∧
  mixture.first ≠ mixture.second ∧
  mixture.firstFraction = (1 : ℚ) / 2

/-- Formal version of “does not exhibit optical activity”: every rational-valued response that
changes sign under global mirror inversion cancels in an equimolar enantiomeric mixture. -/
theorem racemate_cancels_enantiomerOdd_response {Locant : Type*}
    (mixture : BinaryMixture (LocatedConfiguration Locant))
    (racemate : IsRacemate mixture)
    (measurement : LocatedConfiguration Locant → ℚ)
    (enantiomerOdd : ∀ configuration,
      measurement configuration.globallyInverted = -measurement configuration) :
    mixture.response measurement = 0 := by
  rcases racemate with ⟨_, mirror, _, equimolar⟩
  simp only [BinaryMixture.response, mirror, enantiomerOdd, equimolar]
  ring

/-- P-93.1.4: `locant-ambo-` denotes a qualitatively non-equimolar mixture containing the stated
configuration and its epimer at the specified stereogenic unit.  The epimer is formed with the
**local** inversion action, so an `r` unit becomes `s` at exactly that unit.  No unprinted
numerical fraction is introduced. -/
def IsAmboAt {Locant : Type*} [DecidableEq Locant] (locant : Locant)
    (mixture : QualitativeBinaryMixture (LocatedConfiguration Locant)) : Prop :=
  mixture.composition = .nonEquimolar ∧
  mixture.second = mixture.first.invertedAt locant ∧
  mixture.first ≠ mixture.second

theorem amboAt_nonEquimolar {Locant : Type*} [DecidableEq Locant] (locant : Locant)
    (mixture : QualitativeBinaryMixture (LocatedConfiguration Locant))
    (ambo : IsAmboAt locant mixture) :
    mixture.composition = .nonEquimolar :=
  ambo.1

/-! ## Regression checks for the mirror/inversion split

These are deliberately concrete.  They pin the exact source meaning of:

* a low-locant fixed `r` together with a higher-locant `R`/`S`;
* the global molecular mirror, which fixes `r` and exchanges the higher-locant `R`/`S`;
* the local epimer inversion, which exchanges `r`/`s` and fixes the higher-locant descriptor;
* `rel-`/`rac-` semantics, which use the global mirror, not the local epimer action.
-/

namespace Regression

open LocatedConfiguration

/-- Two equal concrete configurations have equal descriptor lists.  This reduces the regression
distinctness proofs to decidable list equality, avoiding any reliance on `simp` evaluating
constructor disequalities. -/
private theorem descriptorList_eq_of_configuration_eq
    {first second : LocatedConfiguration Nat} (equal : first = second) :
    first.assignments.map (fun assignment => assignment.2) =
      second.assignments.map (fun assignment => assignment.2) :=
  congrArg
    (fun configuration : LocatedConfiguration Nat =>
      configuration.assignments.map (fun assignment => assignment.2)) equal

/-- Low locant `r` plus a higher-locant `S`. -/
def lowLocantRHighCapitalS : LocatedConfiguration Nat where
  assignments := [(0, .lowercaseR), (1, .capitalS)]
  locantsNodup := by decide

/-- Low locant `r` plus a higher-locant preferred `R`. -/
def lowLocantRHighCapitalR : LocatedConfiguration Nat where
  assignments := [(0, .lowercaseR), (1, .capitalR)]
  locantsNodup := by decide

/-- A configuration whose only stereogenic descriptor is the fixed pseudoasymmetric `r`. -/
def rOnly : LocatedConfiguration Nat where
  assignments := [(0, .lowercaseR)]
  locantsNodup := by decide

@[simp] theorem lowLocantRHighCapitalS_assignments :
    lowLocantRHighCapitalS.assignments = [(0, .lowercaseR), (1, .capitalS)] := rfl

@[simp] theorem lowLocantRHighCapitalR_assignments :
    lowLocantRHighCapitalR.assignments = [(0, .lowercaseR), (1, .capitalR)] := rfl

@[simp] theorem rOnly_assignments :
    rOnly.assignments = [(0, .lowercaseR)] := rfl

/-- The global molecular mirror fixes the low-locant `r` and exchanges the higher-locant `R`. -/
@[simp] theorem lowLocantRHighCapitalR_globalMirror :
    lowLocantRHighCapitalR.globallyInverted.assignments =
      [(0, .lowercaseR), (1, .capitalS)] := by
  simp [lowLocantRHighCapitalR, LocatedConfiguration.globallyInverted]

/-- The global molecular mirror fixes the low-locant `r` and exchanges the higher-locant `S`. -/
@[simp] theorem lowLocantRHighCapitalS_globalMirror :
    lowLocantRHighCapitalS.globallyInverted.assignments =
      [(0, .lowercaseR), (1, .capitalR)] := by
  simp [lowLocantRHighCapitalS, LocatedConfiguration.globallyInverted]

/-- The local epimer inversion exchanges the low-locant `r` and fixes the higher-locant `R`. -/
@[simp] theorem lowLocantRHighCapitalR_localInversion :
    (lowLocantRHighCapitalR.invertedAt 0).assignments =
      [(0, .lowercaseS), (1, .capitalR)] := by
  simp [lowLocantRHighCapitalR, LocatedConfiguration.invertedAt,
    LocatedConfiguration.invertAssignmentAt]

/-- The local epimer inversion at the higher locant exchanges the capital descriptor and leaves
the low-locant fixed `r` untouched. -/
@[simp] theorem lowLocantRHighCapitalR_localInversionHigh :
    (lowLocantRHighCapitalR.invertedAt 1).assignments =
      [(0, .lowercaseR), (1, .capitalS)] := by
  simp [lowLocantRHighCapitalR, LocatedConfiguration.invertedAt,
    LocatedConfiguration.invertAssignmentAt]

/-- In this configuration the higher-locant local inversion and the global molecular mirror have
the same assignment list: the only unit they treat differently is the fixed low-locant `r`, which
neither operation changes at this target.  The two operations still differ at locant `0`
(`lowLocantRHighCapitalR_globalMirror_ne_localInversion`). -/
theorem lowLocantRHighCapitalR_localInversionHigh_eq_globalMirror :
    lowLocantRHighCapitalR.invertedAt 1 = lowLocantRHighCapitalR.globallyInverted := by
  apply LocatedConfiguration.ext
  rw [lowLocantRHighCapitalR_localInversionHigh, lowLocantRHighCapitalR_globalMirror]

/-- The global mirror fixes the only descriptor of an `r`-only configuration. -/
@[simp] theorem rOnly_globalMirror :
    rOnly.globallyInverted.assignments = [(0, .lowercaseR)] := by
  simp [rOnly, LocatedConfiguration.globallyInverted]

/-- The local epimer inversion exchanges the only descriptor of an `r`-only configuration. -/
@[simp] theorem rOnly_localInversion :
    (rOnly.invertedAt 0).assignments = [(0, .lowercaseS)] := by
  simp [rOnly, LocatedConfiguration.invertedAt, LocatedConfiguration.invertAssignmentAt]

/-- Global mirror and local inversion genuinely differ on the mixed `r`/`R` configuration. -/
theorem lowLocantRHighCapitalR_globalMirror_ne_localInversion :
    lowLocantRHighCapitalR.globallyInverted ≠
      lowLocantRHighCapitalR.invertedAt 0 := by
  intro equal
  have descriptorEq :
      ([Descriptor.lowercaseR, Descriptor.capitalS] : List Descriptor) =
        [Descriptor.lowercaseS, Descriptor.capitalR] := by
    simpa [LocatedConfiguration.invertAssignmentAt, lowLocantRHighCapitalR_globalMirror,
      lowLocantRHighCapitalR_localInversion] using
        descriptorList_eq_of_configuration_eq equal
  exact absurd descriptorEq (by decide)

/-- Global mirror and local inversion genuinely differ on the `r`-only configuration. -/
theorem rOnly_globalMirror_ne_localInversion :
    rOnly.globallyInverted ≠ rOnly.invertedAt 0 := by
  intro equal
  have descriptorEq :
      ([Descriptor.lowercaseR] : List Descriptor) = [Descriptor.lowercaseS] := by
    simpa [LocatedConfiguration.invertAssignmentAt, rOnly_globalMirror, rOnly_localInversion] using
      descriptorList_eq_of_configuration_eq equal
  exact absurd descriptorEq (by decide)

/-- The global mirror of an `r`-only configuration is the configuration itself. -/
theorem rOnly_globalMirror_self : rOnly.globallyInverted = rOnly := by
  ext
  simp [rOnly, LocatedConfiguration.globallyInverted]

/-- The global mirror is a distinct enantiomer of the mixed `r`/`R` configuration. -/
theorem lowLocantRHighCapitalR_globalMirror_ne :
    lowLocantRHighCapitalR ≠ lowLocantRHighCapitalR.globallyInverted := by
  intro equal
  have descriptorEq :
      ([Descriptor.lowercaseR, Descriptor.capitalR] : List Descriptor) =
        [Descriptor.lowercaseR, Descriptor.capitalS] := by
    simpa [lowLocantRHighCapitalR_assignments,
      lowLocantRHighCapitalR_globalMirror] using
        descriptorList_eq_of_configuration_eq equal
  exact absurd descriptorEq (by decide)

/-- The canonical representative of the mixed configuration is the higher-locant `R`; the
lower-locant fixed `r` is ignored for representative selection. -/
theorem lowLocantRHighCapitalR_canonical :
    LocatedConfiguration.IsCanonicalNamedRepresentative lowLocantRHighCapitalR := by
  refine ⟨(1, .capitalR), ?_, ?_, ?_, ?_, ?_⟩
  · simp [lowLocantRHighCapitalR]
  · exact Descriptor.representativeEligible_capitalR
  · exact Descriptor.enantiomer_ne_of_eligible Descriptor.capitalR
      Descriptor.representativeEligible_capitalR
  · intro assignment member eligible _nonfixed
    simp only [lowLocantRHighCapitalR, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with h | h
    · rw [h] at eligible
      exact absurd eligible (by simp [Descriptor.RepresentativeEligible])
    · rw [h]
  · trivial

/-- The global mirror of the mixed configuration is not the canonical named representative: the
lowest eligible descriptor is now `S`, which is not the preferred member. -/
theorem lowLocantRHighCapitalR_globalMirror_not_canonical :
    ¬ LocatedConfiguration.IsCanonicalNamedRepresentative
      lowLocantRHighCapitalR.globallyInverted := by
  rintro ⟨leading, member, eligible, _nonfixed, _minimal, preferred⟩
  rw [lowLocantRHighCapitalR_globalMirror] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h
  · rw [h] at eligible
    exact absurd eligible (by simp [Descriptor.RepresentativeEligible])
  · rw [h] at preferred
    exact absurd preferred (by simp [Descriptor.PreferredAtLowest])

/-- The global mirror is a representative of the same `rel-` class. -/
theorem lowLocantRHighCapitalR_relativeEquivalent_globalMirror :
    RelativeEquivalent lowLocantRHighCapitalR
      lowLocantRHighCapitalR.globallyInverted :=
  Or.inr rfl

/-- A local epimer inversion is not a global enantiomer relation: inverting the `r` unit changes
the relative configuration. -/
theorem lowLocantRHighCapitalR_localInversion_not_relativeEquivalent :
    ¬ RelativeEquivalent lowLocantRHighCapitalR
      (lowLocantRHighCapitalR.invertedAt 0) := by
  intro related
  rcases related with same | mirrored
  · have descriptorEq :
        ([Descriptor.lowercaseS, Descriptor.capitalR] : List Descriptor) =
          [Descriptor.lowercaseR, Descriptor.capitalR] := by
      simpa [LocatedConfiguration.invertAssignmentAt, lowLocantRHighCapitalR_localInversion,
        lowLocantRHighCapitalR_assignments] using
          descriptorList_eq_of_configuration_eq same
    exact absurd descriptorEq (by decide)
  · have descriptorEq :
        ([Descriptor.lowercaseS, Descriptor.capitalR] : List Descriptor) =
          [Descriptor.lowercaseR, Descriptor.capitalS] := by
      simpa [LocatedConfiguration.invertAssignmentAt, lowLocantRHighCapitalR_localInversion,
        lowLocantRHighCapitalR_globalMirror] using
          descriptorList_eq_of_configuration_eq mirrored
    exact absurd descriptorEq (by decide)

/-- An `r`-only configuration has no distinct global enantiomer, so it is not a racemate. -/
theorem rOnly_localInversion_not_relativeEquivalent :
    ¬ RelativeEquivalent rOnly (rOnly.invertedAt 0) := by
  intro related
  rcases related with same | mirrored
  · have descriptorEq :
        ([Descriptor.lowercaseS] : List Descriptor) = [Descriptor.lowercaseR] := by
      simpa [LocatedConfiguration.invertAssignmentAt, rOnly_localInversion, rOnly_assignments] using
        descriptorList_eq_of_configuration_eq same
    exact absurd descriptorEq (by decide)
  · have descriptorEq :
        ([Descriptor.lowercaseS] : List Descriptor) = [Descriptor.lowercaseR] := by
      simpa [LocatedConfiguration.invertAssignmentAt, rOnly_localInversion, rOnly_globalMirror] using
        descriptorList_eq_of_configuration_eq mirrored
    exact absurd descriptorEq (by decide)

/-- The mixed `r`/`R` configuration and its global mirror form a genuine racemate. -/
def lowLocantRHighCapitalRRacemate :
    BinaryMixture (LocatedConfiguration Nat) :=
  { first := lowLocantRHighCapitalR
    second := lowLocantRHighCapitalR.globallyInverted
    firstFraction := (1 : ℚ) / 2 }

theorem lowLocantRHighCapitalR_isRacemate :
    IsRacemate lowLocantRHighCapitalRRacemate := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · norm_num [BinaryMixture.Valid, lowLocantRHighCapitalRRacemate]
  · exact lowLocantRHighCapitalR_globalMirror_ne

/-- An `r`-only configuration cannot be a racemate: the global mirror fixes it. -/
def rOnlyRacemate : BinaryMixture (LocatedConfiguration Nat) :=
  { first := rOnly
    second := rOnly.globallyInverted
    firstFraction := (1 : ℚ) / 2 }

theorem rOnly_not_isRacemate : ¬ IsRacemate rOnlyRacemate := by
  intro racemate
  have distinct := racemate.2.2.1
  exact distinct rOnly_globalMirror_self.symm

/-- The `ambo` mixture at the low-locant `r` is a genuine local epimer mixture. -/
def rOnlyAmbo : QualitativeBinaryMixture (LocatedConfiguration Nat) :=
  { first := rOnly
    second := rOnly.invertedAt 0
    composition := .nonEquimolar }

theorem rOnly_isAmboAtZero : IsAmboAt 0 rOnlyAmbo := by
  refine ⟨rfl, rfl, ?_⟩
  intro equal
  have descriptorEq :
      ([Descriptor.lowercaseR] : List Descriptor) = [Descriptor.lowercaseS] := by
    simpa [LocatedConfiguration.invertAssignmentAt, rOnlyAmbo, rOnly_assignments, rOnly_localInversion] using
      descriptorList_eq_of_configuration_eq equal
  exact absurd descriptorEq (by decide)

/-- The `ambo` mixture at the low-locant `r` and the global mirror of the same configuration are
different constructions: the former performs one local epimer inversion, the latter reflects the
whole molecule. -/
theorem rOnlyAmbo_second_ne_globalMirror :
    rOnlyAmbo.second ≠ rOnly.globallyInverted := by
  intro equal
  have descriptorEq :
      ([Descriptor.lowercaseS] : List Descriptor) = [Descriptor.lowercaseR] := by
    simpa [LocatedConfiguration.invertAssignmentAt, rOnlyAmbo, rOnly_localInversion, rOnly_globalMirror] using
      descriptorList_eq_of_configuration_eq equal
  exact absurd descriptorEq (by decide)

end Regression

end BlueBookP93.GeneralConfiguration

end TetraStereo.OneCenter
