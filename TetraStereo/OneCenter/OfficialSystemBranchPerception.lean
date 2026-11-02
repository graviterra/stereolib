import TetraStereo.OneCenter.OfficialStereochemicalSystem
import TetraStereo.OneCenter.OfficialBranchPerception

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Fixed-point official-environment branch perception.

  `OfficialBranchPerception.lean` walks ligand branches and reads descriptor-bearing centers from
  the older tetrahedral discovery state.  This module performs the same branch-context construction
  from the new general `OfficialDescriptorEnvironment`, so arbitrary registered stereogenic units
  can feed Rule 3/4/5 context after descriptor discovery reaches a fixed point.
-/

namespace OfficialDescriptorEnvironment

variable {Unit : Type*}

/-- Whether an official descriptor environment has any fact for one unit. -/
def hasAnyValue (env : OfficialDescriptorEnvironment Unit) (unit : Unit) : Bool :=
  (env.rule3Geometry unit).isSome ||
    (env.rule4aKind unit).isSome ||
    (env.rule4bPair unit).isSome ||
    (env.rule4cDescriptor unit).isSome ||
    (env.rule5Descriptor unit).isSome

/-- Read a unit context only when at least one official descriptor fact is present. -/
def context? (env : OfficialDescriptorEnvironment Unit) (unit : Unit) :
    Option CIPRuleEngine.OfficialLigandRuleContext :=
  if env.hasAnyValue unit then some (env.toOfficialLigandRuleContext unit) else none

@[simp] theorem context?_eq_none_of_hasAnyValue_eq_false
    (env : OfficialDescriptorEnvironment Unit) (unit : Unit)
    (h : env.hasAnyValue unit = false) :
    env.context? unit = none := by
  simp [context?, h]

theorem context?_eq_some_of_hasAnyValue_eq_true
    (env : OfficialDescriptorEnvironment Unit) (unit : Unit)
    (h : env.hasAnyValue unit = true) :
    env.context? unit = some (env.toOfficialLigandRuleContext unit) := by
  simp [context?, h]

end OfficialDescriptorEnvironment

variable {V Unit : Type*} [Fintype V] [DecidableEq V]

/-- A registered stereochemical unit found while walking a ligand branch. -/
structure BranchEnvironmentSource (m : MultiCenterMolecule V) (Unit : Type*) where
  source : m.Center
  unit : Unit

namespace BranchEnvironmentSource

variable {m : MultiCenterMolecule V}

/-- The official context carried by a branch source in a descriptor environment. -/
def toOfficialLigandRuleContext (env : OfficialDescriptorEnvironment Unit)
    (source : BranchEnvironmentSource m Unit) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  env.toOfficialLigandRuleContext source.unit

/-- The optional official context carried by a branch source in a descriptor environment. -/
def toOfficialLigandRuleContext? (env : OfficialDescriptorEnvironment Unit)
    (source : BranchEnvironmentSource m Unit) :
    Option CIPRuleEngine.OfficialLigandRuleContext :=
  env.context? source.unit

end BranchEnvironmentSource

/-- First pair of environment branch sources whose molecular source centers are distinct. -/
def firstDistinctEnvironmentSourcePair? {m : MultiCenterMolecule V} :
    List (BranchEnvironmentSource m Unit) →
      Option (BranchEnvironmentSource m Unit × BranchEnvironmentSource m Unit)
  | [] => none
  | source :: sources =>
      match sources.find? fun other => decide (other.source ≠ source.source) with
      | some other => some (source, other)
      | none => firstDistinctEnvironmentSourcePair? sources

@[simp] theorem firstDistinctEnvironmentSourcePair?_cons_cons_of_source_ne
    {m : MultiCenterMolecule V} (left right : BranchEnvironmentSource m Unit)
    (rest : List (BranchEnvironmentSource m Unit)) (h : right.source ≠ left.source) :
    firstDistinctEnvironmentSourcePair? (left :: right :: rest) = some (left, right) := by
  simp [firstDistinctEnvironmentSourcePair?, h]

/-- Search one source against later sources for the first distinct pair carrying Rule-5 facts. -/
def firstRule5PairWithSource? {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit) (source : BranchEnvironmentSource m Unit) :
    List (BranchEnvironmentSource m Unit) →
      Option (OfficialRule5Descriptor × OfficialRule5Descriptor)
  | [] => none
  | other :: rest =>
      if other.source ≠ source.source then
        match env.rule5Descriptor source.unit, env.rule5Descriptor other.unit with
        | some leftDescriptor, some rightDescriptor => some (leftDescriptor, rightDescriptor)
        | _, _ => firstRule5PairWithSource? env source rest
      else
        firstRule5PairWithSource? env source rest

/-- First distinct branch-source pair carrying Rule-5 descriptors. -/
def firstDistinctRule5DescriptorPair? {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit) :
    List (BranchEnvironmentSource m Unit) →
      Option (OfficialRule5Descriptor × OfficialRule5Descriptor)
  | [] => none
  | source :: sources =>
      match firstRule5PairWithSource? env source sources with
      | some pair => some pair
      | none => firstDistinctRule5DescriptorPair? env sources

@[simp] theorem firstDistinctRule5DescriptorPair?_cons_cons_of_source_ne_rule5
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit)
    (left right : BranchEnvironmentSource m Unit)
    (rest : List (BranchEnvironmentSource m Unit))
    {leftDescriptor rightDescriptor : OfficialRule5Descriptor}
    (hsource : right.source ≠ left.source)
    (hleft : env.rule5Descriptor left.unit = some leftDescriptor)
    (hright : env.rule5Descriptor right.unit = some rightDescriptor) :
    firstDistinctRule5DescriptorPair? env (left :: right :: rest) =
      some (leftDescriptor, rightDescriptor) := by
  simp [firstDistinctRule5DescriptorPair?, firstRule5PairWithSource?, hsource, hleft, hright]

/-- Build a branch-level official context from environment sources.

The first descriptor-bearing source supplies the one-source Rule 3/4a/4c/5 context.  The first
distinct pair of Rule-5-bearing sources supplies the branch-level Rule 4b like/unlike fact. -/
def officialContextOfEnvironmentSources {m : MultiCenterMolecule V}
    (env : OfficialDescriptorEnvironment Unit)
    (sources : List (BranchEnvironmentSource m Unit)) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  let base :=
    match sources.head? with
    | some source => env.toOfficialLigandRuleContext source.unit
    | none => CIPRuleEngine.OfficialLigandRuleContext.empty
  match firstDistinctRule5DescriptorPair? env sources with
  | some (leftDescriptor, rightDescriptor) =>
      base.withRule4bPair (OfficialRule5Descriptor.pairKind leftDescriptor rightDescriptor)
  | none => base

@[simp] theorem officialContextOfEnvironmentSources_nil
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit) :
    officialContextOfEnvironmentSources (m := m) env [] =
      CIPRuleEngine.OfficialLigandRuleContext.empty := by
  rfl

theorem officialContextOfEnvironmentSources_rule4bPair?_of_two_distinct_rule5
    {m : MultiCenterMolecule V} (env : OfficialDescriptorEnvironment Unit)
    (left right : BranchEnvironmentSource m Unit)
    (rest : List (BranchEnvironmentSource m Unit))
    {leftDescriptor rightDescriptor : OfficialRule5Descriptor}
    (hsource : right.source ≠ left.source)
    (hleft : env.rule5Descriptor left.unit = some leftDescriptor)
    (hright : env.rule5Descriptor right.unit = some rightDescriptor) :
    (officialContextOfEnvironmentSources env (left :: right :: rest)).rule4bPair? =
      some (OfficialRule5Descriptor.pairKind leftDescriptor rightDescriptor) := by
  simp [officialContextOfEnvironmentSources,
    firstDistinctRule5DescriptorPair?_cons_cons_of_source_ne_rule5 env left right rest hsource
      hleft hright,
    CIPRuleEngine.OfficialLigandRuleContext.withRule4bPair]

namespace MultiCenterMolecule

variable [DecidableEq Unit]
variable (m : MultiCenterMolecule V)

/-- Registered descriptor-bearing units found on a branch by walking distinguished source centers.

`unitsAtCenter` connects the old center-walking frontier to the new arbitrary stereogenic-unit
registry.  A source unit is retained only if the fixed-point environment contains at least one
official descriptor fact for it. -/
def branchEnvironmentSourcesWithin
    (env : OfficialDescriptorEnvironment Unit)
    (unitsAtCenter : m.Center → List Unit)
    (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    List (BranchEnvironmentSource m Unit) :=
  (m.branchSourcesWithin center i fuel).flatMap fun source =>
    (unitsAtCenter source).filterMap fun unit =>
      if env.hasAnyValue unit then some { source := source, unit := unit } else none

/-- Default registered descriptor-bearing units found on a ligand branch. -/
def branchEnvironmentSources
    (env : OfficialDescriptorEnvironment Unit)
    (unitsAtCenter : m.Center → List Unit)
    (center : m.Center) (i : Fin 4) :
    List (BranchEnvironmentSource m Unit) :=
  m.branchEnvironmentSourcesWithin env unitsAtCenter center i (Fintype.card V)

/-- Official branch context read from an arbitrary fixed-point descriptor environment. -/
def officialBranchContextFromEnvironmentWithin
    (env : OfficialDescriptorEnvironment Unit)
    (unitsAtCenter : m.Center → List Unit)
    (center : m.Center) (i : Fin 4) (fuel : ℕ) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  officialContextOfEnvironmentSources
    env (m.branchEnvironmentSourcesWithin env unitsAtCenter center i fuel)

/-- Default official branch context read from an arbitrary descriptor environment. -/
def officialBranchContextFromEnvironment
    (env : OfficialDescriptorEnvironment Unit)
    (unitsAtCenter : m.Center → List Unit)
    (center : m.Center) (i : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialBranchContextFromEnvironmentWithin env unitsAtCenter center i (Fintype.card V)

/-- Official branch context read from detector output after schedule fuel and branch-walk fuel. -/
def officialBranchContextFromDetectorWithin
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    (scheduleFuel branchFuel : ℕ)
    (center : m.Center) (i : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialBranchContextFromEnvironmentWithin
    (output.finalEnvironment scheduleFuel) unitsAtCenter center i branchFuel

/-- Default official branch context read from detector output. -/
def officialBranchContextFromDetector
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    (center : m.Center) (i : Fin 4) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialBranchContextFromDetectorWithin output unitsAtCenter (Fintype.card V)
    (Fintype.card V) center i

/-- Feed fixed-point detector branch contexts into the canonical official CIP comparator. -/
def cipOfficialCompareAtFromBranchDetectorWithin
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    (scheduleFuel branchFuel : ℕ)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialCompareAt
    (fun queryCenter queryIndex =>
      m.officialBranchContextFromDetectorWithin output unitsAtCenter scheduleFuel branchFuel
        queryCenter queryIndex)
    center i j

/-- Default fixed-point detector branch comparison. -/
def cipOfficialCompareAtFromBranchDetector
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialCompareAtFromBranchDetectorWithin output unitsAtCenter (Fintype.card V)
    (Fintype.card V) center i j

/-- Bundled result surface for branch perception driven by a fixed-point official descriptor
environment. -/
structure OfficialSystemBranchPerceptionEngineResult
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    (scheduleFuel branchFuel : ℕ) where
  environment : OfficialDescriptorEnvironment Unit
  context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext
  compare : m.Center → Fin 4 → Fin 4 → CIPTraceCertificate

/-- Run the fixed-point-environment branch perception engine with explicit schedule and branch
fuel. -/
def officialSystemBranchPerceptionEngineWithin
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    (scheduleFuel branchFuel : ℕ) :
    m.OfficialSystemBranchPerceptionEngineResult output unitsAtCenter scheduleFuel branchFuel where
  environment := output.finalEnvironment scheduleFuel
  context := fun center i =>
    m.officialBranchContextFromDetectorWithin output unitsAtCenter scheduleFuel branchFuel center i
  compare := fun center i j =>
    m.cipOfficialCompareAtFromBranchDetectorWithin output unitsAtCenter scheduleFuel branchFuel
      center i j

/-- Run the default fixed-point-environment branch perception engine. -/
def officialSystemBranchPerceptionEngine
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit) :
    m.OfficialSystemBranchPerceptionEngineResult output unitsAtCenter (Fintype.card V)
      (Fintype.card V) :=
  m.officialSystemBranchPerceptionEngineWithin output unitsAtCenter (Fintype.card V)
    (Fintype.card V)

/-- Branch contexts read from detector output are stable once the detector environment is fixed. -/
theorem officialBranchContextFromDetectorWithin_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel)
    (center : m.Center) (i : Fin 4) :
    m.officialBranchContextFromDetectorWithin output unitsAtCenter
        (scheduleFuel + 1) branchFuel center i =
      m.officialBranchContextFromDetectorWithin output unitsAtCenter
        scheduleFuel branchFuel center i := by
  have henv := output.finalEnvironment_succ_eq_self_of_fixedAt h
  rw [officialBranchContextFromDetectorWithin, officialBranchContextFromDetectorWithin, henv]

/-- Detector-fed branch comparisons are stable once the detector environment is fixed. -/
theorem cipOfficialCompareAtFromBranchDetectorWithin_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (unitsAtCenter : m.Center → List Unit)
    {scheduleFuel : ℕ} (branchFuel : ℕ)
    (h : output.FixedAt scheduleFuel)
    (center : m.Center) (i j : Fin 4) :
    m.cipOfficialCompareAtFromBranchDetectorWithin output unitsAtCenter
        (scheduleFuel + 1) branchFuel center i j =
      m.cipOfficialCompareAtFromBranchDetectorWithin output unitsAtCenter
        scheduleFuel branchFuel center i j := by
  rw [cipOfficialCompareAtFromBranchDetectorWithin, cipOfficialCompareAtFromBranchDetectorWithin]
  apply congrArg (fun context => m.cipOfficialCompareAt context center i j)
  funext queryCenter queryIndex
  exact m.officialBranchContextFromDetectorWithin_succ_eq_of_fixedAt output unitsAtCenter
    branchFuel h queryCenter queryIndex

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
