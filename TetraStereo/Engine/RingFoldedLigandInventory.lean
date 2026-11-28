import TetraStereo.Engine.RingFoldedLigandRanks
import TetraStereo.Engine.RingOrdinaryLigandInventory

/-! Read the signed paths of a folded molecular ligand one sphere at a time.
A child's stored through-4c rank and auxiliary hand supply its path edge. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFoldedLigandInventory
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingFoldedLigandRanks (Tree Spec)
open RingStereoSphereInventory (Visit SignedPath Inventory)
open private nextWith start eraseVisits from TetraStereo.Engine.RingStereoSphereInventory

private abbrev Entry := Tree × SignedPath

private def advance (p : Entry) : List Entry :=
  p.1.children.map fun child =>
    (child,p.2 ++ [⟨child.label.lower.deep,child.label.hand⟩])

private def spheres : Nat → List Entry → Option Inventory
  | _, [] => some []
  | 0, _::_ => none
  | n+1, x::xs => do
    let rest ← spheres n ((x::xs).flatMap advance)
    return (↑((x::xs).map Prod.snd) : Multiset SignedPath) :: rest

/-- Read every signed path and retain its multiplicity at its own distance. -/
def inventory (n : Nat) (t : Tree) : Option Inventory :=
  spheres n [(t,[⟨[],t.label.hand⟩])]

private def Matches {i : Input} (r : Reader i) (rev : Bool) (v : Visit i) (p : Entry) : Prop :=
  Spec i r rev v.arm p.1 ∧ v.path = p.2

private theorem advance_exact {i : Input} {r : Reader i} {rev : Bool}
    {v : Visit i} {p : Entry} (h : Matches r rev v p) :
    ∃ vs, nextWith r rev i.certified.executableLocalizedRerootChildren
        (RingRetainedStereoRefinement.priority i r rev [.lowercase]) v = some vs ∧
      List.Forall₂ (Matches r rev) vs (advance p) := by
  obtain ⟨spec,same⟩ := h
  unfold nextWith advance
  have paired : List.Forall₂ (Spec i r rev)
      (i.certified.executableLocalizedRerootChildren v.arm) p.1.children := spec.children
  generalize i.certified.executableLocalizedRerootChildren v.arm = cs at paired ⊢
  generalize p.1.children = ts at paired ⊢
  induction paired with
  | nil => exact ⟨[],rfl,.nil⟩
  | @cons c t cs ts hc _ ih =>
    obtain ⟨vs,found,more⟩ := ih
    simp only [List.mapM_cons,List.map_cons,hc.lower,hc.hand,found,Option.pure_def,
      Bind.bind,Option.bind] at found ⊢
    exact ⟨_,rfl,.cons ⟨hc,by rw [same]⟩ more⟩

private theorem frontier {i : Input} {r : Reader i} {rev : Bool}
    {row : List (Visit i)} {ps : List Entry} (hs : List.Forall₂ (Matches r rev) row ps) :
    ∃ blocks, row.mapM (nextWith r rev i.certified.executableLocalizedRerootChildren
        (RingRetainedStereoRefinement.priority i r rev [.lowercase])) = some blocks ∧
      List.Forall₂ (Matches r rev) blocks.flatten (ps.flatMap advance) := by
  induction hs with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons h _ ih =>
    obtain ⟨vs,hvs,matchHead⟩ := advance_exact h
    obtain ⟨bs,hbs,matchTail⟩ := ih
    exact ⟨vs::bs,by simp [List.mapM_cons,hvs,hbs],List.rel_append matchHead matchTail⟩

private theorem path_rows {i : Input} {r : Reader i} {rev : Bool}
    {row : List (Visit i)} {ps : List Entry} (hs : List.Forall₂ (Matches r rev) row ps) :
    row.map Visit.path = ps.map Prod.snd := by
  induction hs with
  | nil => rfl
  | cons h _ ih => simp [h.2,ih]

private theorem spheres_exact {i : Input} {r : Reader i} {rev : Bool} (n : Nat)
    {row : List (Visit i)} {ps : List Entry} (hs : List.Forall₂ (Matches r rev) row ps) :
    (RingUnorderedSphereReading.layers? (nextWith r rev i.certified.executableLocalizedRerootChildren
      (RingRetainedStereoRefinement.priority i r rev [.lowercase])) n row).map eraseVisits =
      spheres n ps := by
  induction n generalizing row ps with
  | zero => cases hs <;> rfl
  | succ n ih =>
    cases hs with
    | nil => rfl
    | cons h tail =>
      have all := List.Forall₂.cons h tail
      obtain ⟨bs,found,more⟩ := frontier all
      simp only [RingUnorderedSphereReading.layers?,spheres,found,Option.pure_def]
      rw [← ih more]
      cases he : RingUnorderedSphereReading.layers? (nextWith r rev
          i.certified.executableLocalizedRerootChildren
          (RingRetainedStereoRefinement.priority i r rev [.lowercase])) n bs.flatten <;>
        simp [he,eraseVisits,path_rows all]

/-- The same distance bound gives exactly the native molecular inventory, including
its failure value when an expansion cannot finish. -/
theorem inventory_exact {i : Input} {r : Reader i} {rev : Bool} {q : Arm i} {t : Tree}
    (spec : Spec i r rev q t) :
    inventory (i.certified.localizedRerootCursorBudget q + 1) t =
      RingStereoSphereInventory.inventory? i r rev [.lowercase] q := by
  symm
  apply spheres_exact
  exact .cons ⟨spec,by simp [start,spec.hand]⟩ .nil

/-- Recover all ordinary priority fields from a folded ligand. -/
def key (n : Nat) (t : Tree) : Option RingFullPathEligibility.Key :=
  (inventory n t).map fun inv => RingOrdinaryLigandInventory.assemble (t.label.lower.deep,inv)

theorem key_exact {i : Input} {r : Reader i} {rev : Bool} {q : Arm i} {t : Tree}
    (spec : Spec i r rev q t) :
    key (i.certified.localizedRerootCursorBudget q + 1) t =
      RingFullPathEligibility.key? i r rev q := by
  rw [← RingOrdinaryLigandInventory.key_exact]
  unfold key RingOrdinaryLigandInventory.key? RingOrdinaryLigandInventory.observe?
  rw [inventory_exact spec,spec.lower]
  cases RingStereoSphereInventory.inventory? i r rev [.lowercase] q <;> rfl

/-- Fold the molecular arm once, then read all ordinary key fields from its signed paths. -/
def key? (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : Option RingFullPathEligibility.Key :=
  let n := i.certified.localizedRerootCursorBudget q + 1
  (RingFoldedLigandRanks.collect i r rev n q).bind (key n)

/-- At a valid arm of the current focus, a ready frozen reader suffices for the
fold and its path readout to reproduce the native ordinary key. -/
theorem molecular_key_exact {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) (rev : Bool) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (on : q.occurrence.val.root = f.val.root) :
    key? i r rev q = RingFullPathEligibility.key? i r rev q := by
  obtain ⟨t,hit,spec⟩ := RingFoldedLigandRanks.collect_exact rev ready
    (i.certified.localizedRerootCursorBudget q + 1) q valid on (Nat.lt_succ_self _)
  simpa [key?,hit] using key_exact spec

end TetraStereo.Engine.RingFoldedLigandInventory
assert_kernel_only TetraStereo.Engine.RingFoldedLigandInventory.inventory_exact
assert_kernel_only TetraStereo.Engine.RingFoldedLigandInventory.key_exact
assert_kernel_only TetraStereo.Engine.RingFoldedLigandInventory.molecular_key_exact
