import TetraStereo.Engine.RingStereoSphereInventory

/-! A donor contributes only its unsigned priority route and terminal hand when
no emitting route contains an earlier donor. The census retains sphere boundaries
and multiplicity, and works at both the Rule 4b and fixed Rule 5 edge stages. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAntichainTrialOrder
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingStereoSphereInventory (Edge SignedPath Inventory project)
open RingFullPathPairs (bitOf stepKey)
open RingUnorderedSphereReading (readRow)

structure Donor where
  ancestors : List (List Word)
  last : List Word
  hand : RS

def donor? (p : SignedPath) : Option Donor :=
  match p.reverse with
  | [] => none
  | e :: es => e.hand.map fun h => ⟨es.reverse.map Edge.earlier,e.earlier,h⟩

def route (s : RS) (h : Donor) : Path :=
  (h.ancestors.map fun d => stepKey d none) ++ [stepKey h.last (some (h.hand == s))]

/-- Every route ending at a donor has only silent proper ancestors. -/
def Clean (p : SignedPath) : Prop :=
  ∀ es e, p = es ++ [e] → e.hand ≠ none → ∀ x ∈ es, x.hand = none

def census (xs : Inventory) : List (Multiset Donor) := xs.map (Multiset.filterMap donor?)

def word (s : RS) (xs : List (Multiset Donor)) : List Bool :=
  xs.flatMap fun row => Quotient.liftOn row (readRow (route s) bitOf)
    (fun _ _ p => RingUnorderedSphereReading.readRow_perm _ _ p)

private theorem entry (s : RS) (p : SignedPath) (clean : Clean p) :
    (donor? p).map (route s) =
      if (bitOf (project s p)).isSome then some (project s p) else none := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e _ =>
    have proj : project s (es ++ [e]) =
        project s es ++ [stepKey e.earlier (e.hand.map (· == s))] := by simp [project]
    rw [proj,RingFullPathPairs.bitOf_snoc]
    cases hh : e.hand with
    | none => simp [donor?,hh]
    | some h =>
      have eq : (es.map Edge.earlier).map (fun d => stepKey d none) = project s es := by
        simp only [List.map_map,project]
        apply List.map_congr_left
        intro x hx
        simp [clean es e rfl (by simp [hh]) x hx]
      simp [donor?,route,hh,eq]

private theorem row_eq (s : RS) (xs : List SignedPath) (hc : ∀ p ∈ xs, Clean p) :
    readRow (route s) bitOf (xs.filterMap donor?) = readRow (project s) bitOf xs := by
  have eq : (xs.filterMap donor?).map (route s) =
      (xs.map (project s)).filter (fun k => (bitOf k).isSome) := by
    induction xs with
    | nil => rfl
    | cons p ps ih =>
      have t := ih (fun q m => hc q (.tail _ m))
      have e := entry s p (hc p (.head _))
      cases d : donor? p <;> cases v : bitOf (project s p) <;> simp_all
  simp only [readRow,eq,List.filter_filter]
  simp

/-- Sparse, seed-independent observations reconstruct both native reference
readings at any earlier edge stage, including arbitrary mixtures across or
within spheres. The hypothesis can be checked on the unordered expansion. -/
theorem stage_word (i : Input) (r : Reader i) (rev : Bool)
    (stages : List RingRetainedStereoRefinement.Observation) (q : Arm i)
    {xs : Inventory} (found : RingStereoSphereInventory.inventory? i r rev stages q = some xs)
    (ac : ∀ row ∈ xs, ∀ p ∈ row, Clean p) (s : RS) :
    RingFullPathPairs.stageWords i r rev stages s q = some (word s (census xs)) := by
  rw [← RingStereoSphereInventory.reading_exact,found,Option.map_some]
  apply congrArg some
  unfold RingStereoSphereInventory.reading word census
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro row mem
  have h := ac row mem
  revert h
  induction row using Quotient.inductionOn with
  | _ ps =>
    intro h
    exact (row_eq s ps h).symm

end TetraStereo.Engine.RingAntichainTrialOrder
assert_kernel_only TetraStereo.Engine.RingAntichainTrialOrder.stage_word
