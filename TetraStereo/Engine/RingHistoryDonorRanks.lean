import TetraStereo.Engine.RingHistoryDonorFold
import TetraStereo.Examples.RingDeepHistoryComparison

/-! Complete stereochemical branch priorities from written bonds, isotope records
and a frozen table keyed by the newest-first atom history. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHistoryDonorRanks
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingActiveDistanceSchedule (Cell)
open RingRetainedStereoRefinement (Observation priority)
open RingStereoSiblingPass (Branch)
open RingDeepHistoryPathOrder (Edge)
open Examples.DecalinAuxiliary (history)
open Examples.RingDeepHistoryComparison (edge)

def model (m : RawMolecule) (read : List Nat → Cell) : RingHistoryDonorFold.Model Edge :=
  ⟨RingDeepHistoryPathOrder.children m,fun e => RingDeepHistoryPathOrder.key? m e.1 e.2,fun e => read e.2⟩

def rank? (m : RawMolecule) (read : List Nat → Cell) (rev : Bool) (os : List Observation)
    (fuel : Nat) (e : Edge) : Option Branch := RingHistoryDonorFold.rank (model m read) rev fuel os e

def fuel (m : RawMolecule) := 2 * (m.atomCount+1+1) + 1

theorem enough (i : Input) (q : Arm i) : i.certified.localizedRerootCursorBudget q < fuel i.molecule := by
  have count := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  unfold fuel
  rw [←count]
  exact Nat.lt_succ_of_le (i.certified.localizedRerootCursorBudget_le_twice q)

/-- A comparison may use any earlier pass list and either geometry. Equal
sibling priorities require no tie-breaker. Only entries on the selected
original root must agree with the frozen table. -/
theorem exact_rank {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (read : List Nat → Cell) (seen : ∀ t : Site i, t.val.root = f.val.root → read (history t) = r t)
    (rev : Bool) (os : List Observation) (q : Arm i) (p : Site i) (prev : q.previous? = some p)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root)
    (n : Nat) (depth : i.certified.localizedRerootCursorBudget q < n) :
    rank? i.molecule read rev os n (edge q) = priority i r rev os q := by
  let dom (a : Arm i) := i.certified.LocalizedRerootCursorValid a ∧
    a.occurrence.val.root = f.val.root ∧ ∃ t, a.previous? = some t
  have sound : RingHistoryDonorFold.Corresponds (model i.molecule read) r edge dom := by
    constructor
    · exact fun _ d => d.1
    · intro a d c hc
      have edges := i.certified.executableLocalizedRerootChildren_declarative a
      exact ⟨i.certified.localizedRerootChild_valid a c _ edges hc,
        (i.certified.localizedRerootChildren_root_eq a c _ edges hc).trans d.2.1,
        _,i.certified.executableLocalizedRerootChildren_previous a c hc⟩
    · intro a d
      obtain ⟨t,previous⟩ := d.2.2
      exact Examples.RingDeepHistoryComparison.children_exact a t previous d.1
    · intro a d
      obtain ⟨t,previous⟩ := d.2.2
      exact Examples.RingDeepHistoryComparison.key_exact a t previous d.1
    · intro a d
      exact seen a.occurrence d.2.1
  obtain ⟨b,got⟩ := RingOccurrenceStereo.rank_total ready rev os q valid on
  change priority i r rev os q = some b at got
  rw [got]
  exact RingHistoryDonorFold.rank_of_derives sound rev os n q b ⟨valid,on,p,prev⟩ depth
    (RingRetainedStereoRefinement.source os q got)

end TetraStereo.Engine.RingHistoryDonorRanks
assert_kernel_only TetraStereo.Engine.RingHistoryDonorRanks.exact_rank
