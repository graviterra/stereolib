import TetraStereo.OneCenter.OfficialDescriptorEnvironment

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-!
  Molecule-level official stereochemical system layer.

  The official descriptor environment is intentionally generic: it can store facts for any unit
  type.  This module gives that environment a molecule-facing interpretation.  A finite registry
  says which stereogenic units exist in a molecule; detector output combines initially perceived
  descriptor facts with a dependency schedule; and the final fixed-point environment is read as
  official CIP context for the canonical `OfficialCIPEngine`.
-/

/-- The broad class of stereochemical question represented by a registered unit. -/
inductive OfficialStereochemicalUnitKind where
  | tetrahedralCenter
  | alkeneOrCumulene
  | axis
  | plane
  | helix
  | conformation
  | ensemble
  | auxiliary
  | phantom
  | lonePair
  deriving DecidableEq, Repr

/-- A finite stereogenic-unit registry for one molecular graph.

`Unit` is deliberately external to the graph: for a mature engine it can be a sum type of
tetrahedral centers, double bonds, axes, planes, helices, conformers, ensemble states, and
auxiliary descriptor sources. -/
structure OfficialStereogenicUnitRegistry (V Unit : Type*) [Fintype V] [DecidableEq V] where
  molecule : MoleculeGraph V
  kind : Unit → OfficialStereochemicalUnitKind
  support : Unit → Finset V
  anchor? : Unit → Option V := fun _ => none

namespace OfficialStereogenicUnitRegistry

variable {V Unit : Type*} [Fintype V] [DecidableEq V]

/-- The finite set of units represented by a registry. -/
def units [Fintype Unit] [DecidableEq Unit]
    (_registry : OfficialStereogenicUnitRegistry V Unit) : Finset Unit :=
  Finset.univ

@[simp] theorem mem_units [Fintype Unit] [DecidableEq Unit]
    (registry : OfficialStereogenicUnitRegistry V Unit) (unit : Unit) :
    unit ∈ registry.units := by
  simp [units]

end OfficialStereogenicUnitRegistry

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distinguished tetrahedral centers of a `MultiCenterMolecule` as an official unit registry.

This is the first concrete registry instance: every distinguished center is registered as a
tetrahedral-center unit, and its support contains the center plus its four enumerated ligands. -/
def tetrahedralCenterRegistry (m : MultiCenterMolecule V) :
    OfficialStereogenicUnitRegistry V m.Center where
  molecule := m.mol
  kind := fun _ => OfficialStereochemicalUnitKind.tetrahedralCenter
  support := fun center =>
    insert center.1 ((Finset.univ : Finset (Fin 4)).image fun i => m.ligandAtomAt center i)
  anchor? := fun center => some center.1

@[simp] theorem tetrahedralCenterRegistry_kind (m : MultiCenterMolecule V)
    (center : m.Center) :
    (m.tetrahedralCenterRegistry).kind center =
      OfficialStereochemicalUnitKind.tetrahedralCenter :=
  rfl

@[simp] theorem tetrahedralCenterRegistry_anchor? (m : MultiCenterMolecule V)
    (center : m.Center) :
    (m.tetrahedralCenterRegistry).anchor? center = some center.1 :=
  rfl

@[simp] theorem center_mem_tetrahedralCenterRegistry_support (m : MultiCenterMolecule V)
    (center : m.Center) :
    center.1 ∈ (m.tetrahedralCenterRegistry).support center := by
  simp [tetrahedralCenterRegistry]

end MultiCenterMolecule

/-- Output of a stereogenic-unit detector before final descriptor interpretation.

The detector supplies initial descriptor facts and a dependency schedule.  Running the schedule with
finite fuel produces a candidate descriptor environment; proving a fixed point upgrades it to a
stable source of official CIP context. -/
structure OfficialDetectorOutput (Unit : Type*) where
  initialEnvironment : OfficialDescriptorEnvironment Unit
  schedule : OfficialDescriptorSchedule Unit

namespace OfficialDescriptorTask

variable {Unit : Type*}



def safeResolve? (task : OfficialDescriptorTask Unit)
    (env : OfficialDescriptorEnvironment Unit) : Option OfficialDescriptorValue :=
  if env.requirementsReady task.requirements then task.resolve? env else none

@[simp] theorem safeResolve?_eq_none_of_requirementsReady_eq_false
    (task : OfficialDescriptorTask Unit) (env : OfficialDescriptorEnvironment Unit)
    (h : env.requirementsReady task.requirements = false) :
    task.safeResolve? env = none := by
  simp [safeResolve?, h]

theorem safeResolve?_eq_resolve?_of_requirementsReady_eq_true
    (task : OfficialDescriptorTask Unit) (env : OfficialDescriptorEnvironment Unit)
    (h : env.requirementsReady task.requirements = true) :
    task.safeResolve? env = task.resolve? env := by
  simp [safeResolve?, h]

end OfficialDescriptorTask

namespace OfficialDetectorOutput

variable {Unit : Type*} [DecidableEq Unit]

/-- The descriptor environment after running the detector schedule with finite fuel. -/
def finalEnvironment (output : OfficialDetectorOutput Unit) (fuel : ℕ) :
    OfficialDescriptorEnvironment Unit :=
  output.schedule.runFrom output.initialEnvironment fuel

/-- The detector has stabilized at this fuel if one more schedule pass changes nothing. -/
def FixedAt (output : OfficialDetectorOutput Unit) (fuel : ℕ) : Prop :=
  output.schedule.FixedPoint (output.finalEnvironment fuel)

/-- Read one descriptor slot from the detector's final environment. -/
def descriptorValue? (output : OfficialDetectorOutput Unit) (fuel : ℕ)
    (unit : Unit) (slot : OfficialDescriptorSlot) : Option OfficialDescriptorValue :=
  (output.finalEnvironment fuel).value? unit slot

/-- Read all official-rule facts for one unit as a CIP ligand context. -/
def contextAt (output : OfficialDetectorOutput Unit) (fuel : ℕ) (unit : Unit) :
    CIPRuleEngine.OfficialLigandRuleContext :=
  (output.finalEnvironment fuel).toOfficialLigandRuleContext unit

/-- Dependency-guarded descriptor read: if the requested dependencies are not ready, return `none`
rather than exposing a possibly guessed descriptor. -/
def safeDescriptorValue? (output : OfficialDetectorOutput Unit) (fuel : ℕ)
    (requirements : List (OfficialDescriptorRequirement Unit))
    (unit : Unit) (slot : OfficialDescriptorSlot) : Option OfficialDescriptorValue :=
  let env := output.finalEnvironment fuel
  if env.requirementsReady requirements then env.value? unit slot else none

@[simp] theorem finalEnvironment_zero (output : OfficialDetectorOutput Unit) :
    output.finalEnvironment 0 = output.initialEnvironment :=
  rfl

@[simp] theorem finalEnvironment_succ (output : OfficialDetectorOutput Unit) (fuel : ℕ) :
    output.finalEnvironment (fuel + 1) =
      output.schedule.runOnceFrom (output.finalEnvironment fuel) :=
  rfl

/-- Consecutive equal detector iterations are a fixed point. -/
theorem fixedAt_of_finalEnvironment_stabilizes (output : OfficialDetectorOutput Unit)
    {fuel : ℕ}
    (h : output.finalEnvironment (fuel + 1) = output.finalEnvironment fuel) :
    output.FixedAt fuel := by
  exact output.schedule.fixedPoint_of_runFrom_stabilizes output.initialEnvironment h

/-- At a fixed point, one additional schedule pass leaves the final environment unchanged. -/
theorem finalEnvironment_succ_eq_self_of_fixedAt
    (output : OfficialDetectorOutput Unit) {fuel : ℕ} (h : output.FixedAt fuel) :
    output.finalEnvironment (fuel + 1) = output.finalEnvironment fuel := by
  simpa [finalEnvironment, FixedAt] using h

/-- Descriptor lookups are stable after the detector has reached a fixed point. -/
theorem descriptorValue?_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit) {fuel : ℕ} (h : output.FixedAt fuel)
    (unit : Unit) (slot : OfficialDescriptorSlot) :
    output.descriptorValue? (fuel + 1) unit slot =
      output.descriptorValue? fuel unit slot := by
  have henv := output.finalEnvironment_succ_eq_self_of_fixedAt h
  change (output.finalEnvironment (fuel + 1)).value? unit slot =
    (output.finalEnvironment fuel).value? unit slot
  rw [henv]

/-- Official ligand contexts are stable after the detector has reached a fixed point. -/
theorem contextAt_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit) {fuel : ℕ} (h : output.FixedAt fuel)
    (unit : Unit) :
    output.contextAt (fuel + 1) unit = output.contextAt fuel unit := by
  have henv := output.finalEnvironment_succ_eq_self_of_fixedAt h
  change (output.finalEnvironment (fuel + 1)).toOfficialLigandRuleContext unit =
    (output.finalEnvironment fuel).toOfficialLigandRuleContext unit
  rw [henv]

/-- If dependencies are not executable-ready, the safe descriptor API refuses the read. -/
theorem safeDescriptorValue?_eq_none_of_requirementsReady_eq_false
    (output : OfficialDetectorOutput Unit) (fuel : ℕ)
    (requirements : List (OfficialDescriptorRequirement Unit))
    (unit : Unit) (slot : OfficialDescriptorSlot)
    (h : (output.finalEnvironment fuel).requirementsReady requirements = false) :
    output.safeDescriptorValue? fuel requirements unit slot = none := by
  simp [safeDescriptorValue?, h]

/-- When dependencies are executable-ready, the safe descriptor API is the ordinary descriptor
lookup. -/
theorem safeDescriptorValue?_eq_descriptorValue?_of_requirementsReady_eq_true
    (output : OfficialDetectorOutput Unit) (fuel : ℕ)
    (requirements : List (OfficialDescriptorRequirement Unit))
    (unit : Unit) (slot : OfficialDescriptorSlot)
    (h : (output.finalEnvironment fuel).requirementsReady requirements = true) :
    output.safeDescriptorValue? fuel requirements unit slot =
      output.descriptorValue? fuel unit slot := by
  simp [safeDescriptorValue?, descriptorValue?, h]

end OfficialDetectorOutput

namespace MultiCenterMolecule

variable {V Unit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Unit]
variable (m : MultiCenterMolecule V)

/-- Interpret an official descriptor environment as ligand contexts for a multi-center molecule,
using a detector-provided map from each local ligand branch to a descriptor unit. -/
def officialSystemContextFromEnvironment
    (env : OfficialDescriptorEnvironment Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) :
    m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun center i => env.toOfficialLigandRuleContext (ligandUnit center i)

/-- Official branch contexts supplied by a detector output after finite schedule fuel. -/
def officialSystemContextFromDetector
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) (fuel : ℕ) :
    m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  m.officialSystemContextFromEnvironment (output.finalEnvironment fuel) ligandUnit

/-- Compare one ligand pair using the canonical official CIP engine fed by detector output. -/
def cipOfficialCompareAtFromDetector
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) (fuel : ℕ)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialCompareAt (m.officialSystemContextFromDetector output ligandUnit fuel) center i j

/-- Official local order using detector-supplied contexts. -/
def cipOfficialOrderAtFromDetector
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) (fuel : ℕ)
    (center : m.Center) : List (Fin 4) :=
  m.cipOfficialOrderAt (m.officialSystemContextFromDetector output ligandUnit fuel) center

/-- Official local permutation using detector-supplied contexts. -/
def cipOfficialPermutationAtFromDetector
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) (fuel : ℕ)
    (center : m.Center) : Equiv.Perm (Fin 4) :=
  m.cipOfficialPermutationAt (m.officialSystemContextFromDetector output ligandUnit fuel) center

/-- Safe official local permutation using detector-supplied contexts; it returns `none` if official
priorities remain tied. -/
def cipOfficialPermutationAtFromDetector?
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) (fuel : ℕ)
    (center : m.Center) : Option (Equiv.Perm (Fin 4)) :=
  (m.toOneCenterMolecule center).cipOfficialPermutation?
    (fun i => (m.officialSystemContextFromDetector output ligandUnit fuel) center i)

/-- Run the one-center official CIP engine at a distinguished center using detector-supplied
contexts. -/
def cipOfficialEngineAtFromDetector
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) (fuel : ℕ)
    (center : m.Center) :
    OneCenterMolecule.OfficialCIPEngineResult (m.toOneCenterMolecule center) :=
  (m.toOneCenterMolecule center).cipOfficialEngine
    (fun i => (m.officialSystemContextFromDetector output ligandUnit fuel) center i)

/-- Fixed detector environments induce stable branch contexts for the official CIP engine. -/
theorem officialSystemContextFromDetector_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) {fuel : ℕ}
    (h : output.FixedAt fuel) :
    m.officialSystemContextFromDetector output ligandUnit (fuel + 1) =
      m.officialSystemContextFromDetector output ligandUnit fuel := by
  have henv := output.finalEnvironment_succ_eq_self_of_fixedAt h
  funext center i
  change (output.finalEnvironment (fuel + 1)).toOfficialLigandRuleContext
      (ligandUnit center i) =
    (output.finalEnvironment fuel).toOfficialLigandRuleContext (ligandUnit center i)
  rw [henv]

/-- The canonical official CIP comparison is stable once its detector environment is fixed. -/
theorem cipOfficialCompareAtFromDetector_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) {fuel : ℕ}
    (h : output.FixedAt fuel) (center : m.Center) (i j : Fin 4) :
    m.cipOfficialCompareAtFromDetector output ligandUnit (fuel + 1) center i j =
      m.cipOfficialCompareAtFromDetector output ligandUnit fuel center i j := by
  rw [cipOfficialCompareAtFromDetector]
  rw [cipOfficialCompareAtFromDetector]
  rw [m.officialSystemContextFromDetector_succ_eq_of_fixedAt output ligandUnit h]

/-- The detector-fed official engine result is stable once the descriptor environment is fixed. -/
theorem cipOfficialEngineAtFromDetector_succ_eq_of_fixedAt
    (output : OfficialDetectorOutput Unit)
    (ligandUnit : m.Center → Fin 4 → Unit) {fuel : ℕ}
    (h : output.FixedAt fuel) (center : m.Center) :
    m.cipOfficialEngineAtFromDetector output ligandUnit (fuel + 1) center =
      m.cipOfficialEngineAtFromDetector output ligandUnit fuel center := by
  rw [cipOfficialEngineAtFromDetector]
  rw [cipOfficialEngineAtFromDetector]
  rw [m.officialSystemContextFromDetector_succ_eq_of_fixedAt output ligandUnit h]

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
