import TetraStereo.Engine.RingSharedArmRefusal
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false

namespace TetraStereo.Engine.RingSharedArmRefusal
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority

private def support (m : RawMolecule) (ls rs : List Cursor) : List (Atom m) :=
  (List.finRange m.atomCount).filter fun x => (ls ++ rs).any fun c => c.node.atom == x.val

/-- Only atoms on one of the two complete retained walks can move. The comparison first
eliminates pairs without two distinct quiet walks and then tests global permutations
supported there, keeping the rest of the molecule fixed. -/
private def searchPair? (i : LocalizedChemicalRing.Input) (depth root : Nat) (l r : Cursor) :
    Option (OfficialCertificate i depth root) := do
  guard (l.node.atom ≠ r.node.atom)
  let m := i.molecule
  let ls ← RingSilentPair.walk? m (IsotopePriority.budget m+1) l
  let rs ← RingSilentPair.walk? m (IsotopePriority.budget m+1) r
  if ∀ c ∈ ls ++ rs, Quiet m root c then
    (permsOfList (support m ls rs)).findSome? fun e => officialExchange? i depth root l.node.atom r.node.atom e
  else none

def exhaustive? (i : LocalizedChemicalRing.Input) (depth root : Nat) :
    Option (OfficialCertificate i depth root) := do
  let f ← occurrence? i.molecule [root]
  let arms := occurrenceLigandCursors i.molecule f
  arms.findSome? fun l => arms.findSome? fun r => searchPair? i depth root l r

private theorem found_pair {i depth root} (c : OfficialCertificate i depth root) :
    (searchPair? i depth root c.left c.right).isSome = true := by
  have perm : c.exchange ∈ permsOfList (support i.molecule c.ls c.rs) := by
    apply mem_permsOfList_iff.mpr
    intro x moved
    have inside : x.val ∈ (c.ls ++ c.rs).map (·.node.atom) := by
      by_contra outside
      exact moved (c.symmetry.2.2.1 x outside)
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp inside
    exact List.mem_filter.mpr ⟨List.mem_finRange _,List.any_eq_true.mpr ⟨a,ha,by simpa using eq⟩⟩
  have search := List.findSome?_isSome_iff.mpr
    ⟨c.exchange,perm,show (officialExchange? i depth root c.left.node.atom c.right.node.atom c.exchange).isSome = true
      by rw [c.recheck]; rfl⟩
  simpa [searchPair?,c.distinct,c.full.1,c.full.2,if_pos c.quiet] using search

/-- The finite reference search succeeds exactly on the independently specified shared-arm
certificate class. No prior success of an alignment algorithm occurs in the criterion. -/
theorem exhaustive_iff (i : LocalizedChemicalRing.Input) (depth root : Nat) :
    (exhaustive? i depth root).isSome = true ↔ Nonempty (OfficialCertificate i depth root) := by
  constructor
  · intro ok
    exact ⟨(exhaustive? i depth root).get ok⟩
  · rintro ⟨c⟩
    simp [exhaustive?,c.reached]
    exact ⟨c.left,c.leftAt,c.right,c.rightAt,found_pair c⟩

/-- First try the local subtree alignment. Exhaustive global exchanges supply the fallback. -/
def completeExchange? (i : LocalizedChemicalRing.Input) (depth root : Nat) :
    Option (OfficialCertificate i depth root) :=
  discover? i depth root <|> exhaustive? i depth root

theorem complete_iff (i : LocalizedChemicalRing.Input) (depth root : Nat) :
    (completeExchange? i depth root).isSome = true ↔ Nonempty (OfficialCertificate i depth root) := by
  constructor
  · intro ok
    exact ⟨(completeExchange? i depth root).get ok⟩
  · intro witness
    obtain ⟨v,h⟩ := Option.isSome_iff_exists.mp ((exhaustive_iff i depth root).mpr witness)
    cases fast : discover? i depth root <;> simp [completeExchange?,fast,h]

end TetraStereo.Engine.RingSharedArmRefusal

assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.exhaustive_iff
assert_kernel_only TetraStereo.Engine.RingSharedArmRefusal.complete_iff
