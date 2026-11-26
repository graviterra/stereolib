import TetraStereo.Engine.RingOriginOrderDomain

/-! Executable reflection of the eligible-focus origin-order domain. Only canonical
sites are enumerated: an arm's parent field never enters closure or distance tests. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginOrderCheck
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingOriginOrderDomain (Closure distance PreservesOrder Qualifies)

def pair {i : Input} (f q p : Site i) : Bool :=
  match q.val.node.provenance, p.val.node.provenance with
  | .ringDuplicate d, .ringDuplicate e =>
      decide (q.val.root = f.val.root → p.val.root = f.val.root →
        (d < e ↔ distance f ⟨q,none⟩ d < distance f ⟨p,none⟩ e))
  | _, _ => true

private theorem pair_iff {i : Input} (f q p : Site i) :
    pair f q p = true ↔ ∀ d e, Closure f (⟨q,none⟩ : Arm i) d →
      Closure f (⟨p,none⟩ : Arm i) e →
        (d < e ↔ distance f ⟨q,none⟩ d < distance f ⟨p,none⟩ e) := by
  cases hq : q.val.node.provenance <;> cases hp : p.val.node.provenance <;>
    simp [pair,hq,hp,Closure]
  constructor
  · intro h d e qr hd pr he
    subst d
    subst e
    rcases h with h | h | h
    · exact (h qr).elim
    · exact (h pr).elim
    · exact h
  · intro h
    by_cases qr : q.val.root = f.val.root
    · by_cases pr : p.val.root = f.val.root
      · exact Or.inr (Or.inr (h _ _ qr rfl pr rfl))
      · exact Or.inr (Or.inl pr)
    · exact Or.inl qr

/-- Keep only actual closure leaves in this original-root slice before pair testing. -/
def closures (i : Input) (r : i.certified.Atom) : List (Site i) :=
  (RingActiveDistanceSchedule.sites i).filter fun q =>
    q.val.root == r && match q.val.node.provenance with
      | .ringDuplicate _ => true
      | _ => false

private theorem mem_closures {i : Input} {f : Site i} {q : Arm i} {d : Nat}
    (c : Closure f q d) : q.occurrence ∈ closures i f.val.root := by
  simp [closures,RingActiveDistanceSchedule.sites,c.1,c.2]

def focus {i : Input} (f : Site i) : Bool :=
  let qs := closures i f.val.root
  qs.all fun q => qs.all fun p => pair f q p

theorem focus_iff {i : Input} (f : Site i) : focus f = true ↔ PreservesOrder f := by
  simp only [focus,List.all_eq_true,pair_iff]
  constructor
  · intro all q p d e cq cp
    exact all q.occurrence (mem_closures cq) p.occurrence (mem_closures cp) d e cq cp
  · intro all q _ p _ d e cq cp
    exact all ⟨q,none⟩ ⟨p,none⟩ d e cq cp

def check (i : Input) (r : i.certified.Atom) : Bool :=
  (RingActiveDistanceSchedule.sites i).all fun f =>
    if RingEligibleGraph.candidate (RingPyramidalPublication.eligible i) r f then focus f else true

/-- Exact finite certificate, with no dependence on descriptor computations. -/
theorem check_iff (i : Input) (r : i.certified.Atom) : check i r = true ↔ Qualifies i r := by
  simp only [check,List.all_eq_true]
  constructor
  · intro all f cand
    have hit := all f (List.mem_attach ..)
    simpa only [if_pos cand,focus_iff] using hit
  · intro all f _
    split_ifs with cand
    · exact (focus_iff f).mpr (all f cand)
    · rfl

theorem sound {i : Input} {r : i.certified.Atom} (ok : check i r = true) : Qualifies i r :=
  (check_iff i r).mp ok

theorem complete {i : Input} {r : i.certified.Atom} (ok : Qualifies i r) : check i r = true :=
  (check_iff i r).mpr ok
end TetraStereo.Engine.RingOriginOrderCheck
assert_kernel_only TetraStereo.Engine.RingOriginOrderCheck.check_iff
