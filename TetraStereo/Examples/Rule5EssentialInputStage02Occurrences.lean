import TetraStereo.Examples.Rule5EssentialInputStage01Discovery

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

def sourceSlot : Fin 4 := ⟨2, by decide⟩

def sourceDedupNode :
    { address : List Nat //
      address ∈ ((discovery.center root).branch sourceSlot).key.hierarchyAddresses.dedup } :=
  ⟨[], (List.mem_dedup.mpr
    ((discovery.center root).branch sourceSlot).key.nil_mem_hierarchyAddresses)⟩

def source : ProductionOccurrence :=
  branchOccurrenceAtAddress discovery root sourceSlot sourceDedupNode

def target : ProductionOccurrence := finalOccurrence discovery root

def otherSlot : Fin 4 := ⟨3, by decide⟩

def otherDedupNode :
    { address : List Nat //
      address ∈ ((discovery.center root).branch otherSlot).key.hierarchyAddresses.dedup } :=
  ⟨[], List.mem_dedup.mpr
    ((discovery.center root).branch otherSlot).key.nil_mem_hierarchyAddresses⟩

def other : ProductionOccurrence :=
  branchOccurrenceAtAddress discovery root otherSlot otherDedupNode

theorem source_address : source.address = [2] := rfl
theorem target_address : target.address = [] := rfl
theorem other_address : other.address = [3] := rfl

theorem source_ne_other : source ≠ other := by
  intro equal
  have := congrArg ProductionCIPOccurrenceDiscovery.Occurrence.address equal
  simp [source_address, other_address] at this

theorem source_depth_dependency : DepthDependency source target := by
  exact ⟨rfl, by decide⟩

def sameOccurrence (first second : ProductionOccurrence) : Bool :=
  first.root.1.val == second.root.1.val && first.address == second.address

theorem sameOccurrence_eq_true_iff (first second : ProductionOccurrence) :
    sameOccurrence first second = true ↔ first = second := by
  constructor
  · intro equal
    have parts : (first.root.1.val == second.root.1.val) = true ∧
        (first.address == second.address) = true := by
      change ((first.root.1.val == second.root.1.val) &&
        (first.address == second.address)) = true at equal
      rw [Bool.and_eq_true] at equal
      exact equal
    have centerEqual : first.root.1 = second.root.1 :=
      Fin.ext (beq_iff_eq.mp parts.1)
    have rootEqual : first.root = second.root := Subtype.ext centerEqual
    exact ProductionCIPOccurrenceDiscovery.Occurrence.eq_of_root_eq_address_eq
      first second rootEqual (beq_iff_eq.mp parts.2)
  · intro equal
    subst second
    simp [sameOccurrence]

end TetraStereo.Examples.Rule5EssentialDependency
