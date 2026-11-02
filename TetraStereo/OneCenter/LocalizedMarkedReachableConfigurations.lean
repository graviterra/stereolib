import TetraStereo.OneCenter.LocalizedMarkedConfigurationTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Configuration transport at reached molecular occurrences

Only frames in the canonical expansions rooted at actual in-range atoms are needed for report
transport. No condition is imposed at arbitrary fabricated histories. The closure proof follows
both forms of recursive descent, including the tied-child promotion contexts and reflected calls.
This is still an invariance of the experimental constructor; independent chemical correctness
and successful detected-center coverage are not conclusions of this module.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations

open LocalizedGenericMarkedRecalculation LocalizedMarkedConfigurationTransport

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Canonical child expansion from one actual root, including that root itself. -/
def ReachedFrom (mol : RawMolecule) (center : Nat) (node : Node) : Prop :=
  Relation.ReflTransGen (fun parent child => child ∈ mol.canonicalChildren parent)
    (canonicalCenterRoot center) node

/-- The occurrence inventory traversable from the atom roots of the actual report. -/
def Reached (mol : RawMolecule) (node : Node) : Prop :=
  ∃ center, center < mol.atomCount ∧ ReachedFrom mol center node

theorem reached_root (mol : RawMolecule) (center : Nat) (valid : center < mol.atomCount) :
    Reached mol (canonicalCenterRoot center) := ⟨center, valid, .refl⟩

theorem reached_child (mol : RawMolecule) (parent child : Node)
    (reached : Reached mol parent) (edge : child ∈ mol.canonicalChildren parent) :
    Reached mol child := by
  obtain ⟨center, valid, path⟩ := reached
  exact ⟨center, valid, path.tail edge⟩

/-- Original-frame readback agreement only on reached occurrences. -/
def SameReachedConfigurations (mol : RawMolecule) (first second : Geometry) : Prop :=
  ∀ node, Reached mol node → ∀ atoms,
    frameAtoms? mol node = some atoms → readback? first atoms = readback? second atoms

theorem SameReachedConfigurations.mirror {mol : RawMolecule} {first second : Geometry}
    (agree : SameReachedConfigurations mol first second) :
    SameReachedConfigurations mol (mirror first) (mirror second) := by
  intro node reached atoms frame
  rw [readback_mirror, readback_mirror, agree node reached atoms frame]

theorem tiedChildren_subset (mol : RawMolecule) (fuel : Nat) (state : OccurrenceAuxState)
    (node child : Node) (member : child ∈ tiedChildren mol fuel state node) :
    child ∈ mol.canonicalChildren node := by
  unfold tiedChildren at member
  split at member
  · exact (List.mem_filter.mp member).1
  · simp at member

theorem rawWith_congr_on_children (mol : RawMolecule) (fuel : Nat) {first second : Geometry}
    (node : Node)
    (agree : ∀ atoms, frameAtoms? mol node = some atoms → readback? first atoms = readback? second atoms)
    (state : OccurrenceAuxState) (ctx : Option Nat)
    (subFirst subSecond : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState)
    (sub : ∀ child, child ∈ mol.canonicalChildren node → ∀ s x,
      subFirst first s x child = subSecond second s x child) :
    rawWith? mol fuel first state ctx node subFirst =
      rawWith? mol fuel second state ctx node subSecond := by
  apply rawStep_congr_at mol fuel node agree
  intro mark
  unfold underWith
  exact flatMap_congr_mem _ _ _ fun child member =>
    sub child (tiedChildren_subset mol fuel state node child member) state (some mark)

/-- Generated-state agreement at reached occurrences, without assumptions at other histories. -/
theorem facts_congr (mol : RawMolecule) (fuel depth : Nat) :
    ∀ first second, SameReachedConfigurations mol first second →
      ∀ (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node), Reached mol node →
      facts mol fuel depth first state ctx node = facts mol fuel depth second state ctx node := by
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro first second agree state ctx node reached
      have descriptor : descriptor? mol fuel depth first state ctx node =
          descriptor? mol fuel depth second state ctx node := by
        unfold descriptor? descriptorWith?
        rw [rawWith_congr_on_children mol fuel node (agree node reached) state ctx _ _
          (fun child edge s x => ih first second agree s x child
            (reached_child mol node child reached edge)),
          rawWith_congr_on_children mol fuel node (agree.mirror node reached) state ctx _ _
          (fun child edge s x => ih _ _ agree.mirror s x child
            (reached_child mol node child reached edge))]
      rw [facts_succ, facts_succ, descriptor]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child edge => ih first second agree state ctx child
        (reached_child mol node child reached edge)

theorem descriptor_congr (mol : RawMolecule) (fuel depth : Nat) {first second : Geometry}
    (agree : SameReachedConfigurations mol first second) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : Node) (reached : Reached mol node) :
    descriptor? mol fuel depth first state ctx node =
      descriptor? mol fuel depth second state ctx node := by
  unfold descriptor? descriptorWith?
  rw [rawWith_congr_on_children mol fuel node (agree node reached) state ctx _ _
    (fun child edge s x => facts_congr mol fuel depth first second agree s x child
      (reached_child mol node child reached edge)),
    rawWith_congr_on_children mol fuel node (agree.mirror node reached) state ctx _ _
    (fun child edge s x => facts_congr mol fuel depth _ _ agree.mirror s x child
      (reached_child mol node child reached edge))]

theorem assignCenter_congr (mol : RawMolecule) (fuel center : Nat) {first second : Geometry}
    (agree : SameReachedConfigurations mol first second) (valid : center < mol.atomCount) :
    assignCenter? mol fuel first center = assignCenter? mol fuel second center :=
  descriptor_congr mol fuel _ agree [] none _ (reached_root mol center valid)

/-- Equal configurations on the actual expansion inventory give equal complete emitted reports. -/
theorem assign_congr (mol : RawMolecule) {first second : Geometry}
    (agree : SameReachedConfigurations mol first second) : assign mol first = assign mol second := by
  unfold assign
  apply List.filterMap_congr
  intro center member
  rw [assignCenter_congr mol _ center agree (List.mem_range.mp member)]

end TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations.reached_child
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations.tiedChildren_subset
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations.rawWith_congr_on_children
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations.facts_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations.descriptor_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedReachableConfigurations.assign_congr
