import TetraStereo.Engine.RingRecursiveSignedReport
import TetraStereo.Engine.RingFrameCoverage

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority
open OneCenter CertifiedLocalizedCIPInput
open Certificate.CanonicalSphereKey

/-- Rule 1a sphere key as read at an individual molecular occurrence. -/
def molecularAtomicKey? (m : RawMolecule) (depth : Nat) (c : CanonicalRerootCursor) : Option (Key Nat) :=
  (atomicTree m 3 depth c).map (ckey 3 depth)

-- The production traversal is private in the earlier module. Its name is
-- needed only in this proof of termination with a full list of arm reads.
local macro "sourceArms" : term => pure (Lean.mkIdent (Lean.mkPrivateNameCore
  `TetraStereo.Engine.RingChemicalPriority `TetraStereo.Engine.RingChemicalPriority.arms?))

local macro "unfoldSourceArms" : tactic => do
  let n := Lean.mkIdent (Lean.mkPrivateNameCore `TetraStereo.Engine.RingChemicalPriority
    `TetraStereo.Engine.RingChemicalPriority.arms?)
  `(tactic| unfold $n:ident)

private theorem collectAtomicArms?_complete (m : RawMolecule) (depth : Nat) (cs : List CanonicalRerootCursor)
    (total : ∀ c ∈ cs, (atomicTree m 3 depth c).isSome = true) :
    (sourceArms m depth cs).isSome = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨tree,found⟩ := Option.isSome_iff_exists.mp (total c (by simp))
    obtain ⟨rest,doneTail⟩ := Option.isSome_iff_exists.mp (ih (fun x hx => total x (by simp [hx])))
    unfoldSourceArms
    simp only [doneTail,Option.pure_def,Bind.bind,Option.bind]
    split <;> simp_all

/-- Four distinct defined molecular keys guarantee that the sorter returns
a strict Rule 1a ranking. No postulated ordering or successful comparison
receipt occurs among the hypotheses. -/
theorem atomicRanking?_of_distinct_keys {m path depth n} (site : occurrence? m path = some n)
    (four : (occurrenceLigandCursors m n).length = 4)
    (total : ∀ c ∈ occurrenceLigandCursors m n, (atomicTree m 3 depth c).isSome = true)
    (distinct : ((occurrenceLigandCursors m n).map (molecularAtomicKey? m depth)).Nodup) :
    ∃ r, atomicRanking? m path depth = some r := by
  obtain ⟨rs,rows⟩ := Option.isSome_iff_exists.mp (collectAtomicArms?_complete m depth _ total)
  let le (a b : AtomicArm m depth) := b.key ≤ a.key
  let sorted := rs.val.insertionSort le
  letI : Std.Total le := ⟨fun a b => le_total b.key a.key⟩
  letI : IsTrans (AtomicArm m depth) le := ⟨fun _ _ _ ab bc => le_trans bc ab⟩
  have ordered : sorted.Pairwise le := List.pairwise_insertionSort le rs.val
  have key (a : AtomicArm m depth) : molecularAtomicKey? m depth a.cursor = some a.key := by
    simp [molecularAtomicKey?,a.molecular,a.exactKey]
  rw [← rs.property,List.map_map] at distinct
  have original : (rs.val.map (fun a => some a.key)).Nodup := by
    simpa only [Function.comp_def,key] using distinct
  have unique := ((List.perm_insertionSort le rs.val).map fun a => some a.key).nodup_iff.mpr original
  have different : sorted.Pairwise (fun a b => a.key ≠ b.key) := by
    exact (List.pairwise_map.mp unique).imp fun {a b} h e => h (congrArg some e)
  have strict : sorted.Pairwise (fun a b => b.key < a.key) :=
    (List.pairwise_and_iff.mpr ⟨ordered,different⟩).imp fun {a b} h => lt_of_le_of_ne h.1 (Ne.symm h.2)
  unfold atomicRanking?
  split
  · rename_i missing
    simp [site] at missing
  · rename_i focus reached
    obtain rfl : focus = n := Option.some.inj (reached.symm.trans site)
    dsimp [sorted,le] at strict
    simp [four,rows,strict]

/-- Exact domain of the Rule 1a sorter on every rooted occurrence. The
criterion inspects the molecular trees before sorting and applies at nested
ring occurrences as well as at the original focus. -/
theorem atomicRanking?_isSome_iff_keys (m : RawMolecule) (path : List Nat) (depth : Nat) :
    (atomicRanking? m path depth).isSome = true ↔ ∃ n, occurrence? m path = some n ∧
      (occurrenceLigandCursors m n).length = 4 ∧
      (∀ c ∈ occurrenceLigandCursors m n, (atomicTree m 3 depth c).isSome = true) ∧
      ((occurrenceLigandCursors m n).map (molecularAtomicKey? m depth)).Nodup := by
  constructor
  · rintro ok
    let r := (atomicRanking? m path depth).get ok
    refine ⟨r.focus,r.reached,r.four,?_,?_⟩
    · intro c hc
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp (r.complete.mem_iff.mpr hc)
      simp [a.molecular]
    · apply (r.complete.map (molecularAtomicKey? m depth)).nodup_iff.mp
      rw [List.map_map]
      apply List.pairwise_map.mpr
      change r.arms.Pairwise (fun a b => molecularAtomicKey? m depth a.cursor ≠ molecularAtomicKey? m depth b.cursor)
      apply r.strict.imp
      intro a b lower equal
      apply ne_of_gt lower
      simpa [molecularAtomicKey?,a.molecular,b.molecular,a.exactKey,b.exactKey] using equal
  · rintro ⟨n,site,four,total,distinct⟩
    exact Option.isSome_iff_exists.mpr (atomicRanking?_of_distinct_keys site four total distinct)

end TetraStereo.Engine.RingChemicalPriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.atomicRanking?_of_distinct_keys
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.atomicRanking?_isSome_iff_keys

namespace TetraStereo.Engine.RingChemicalPriority.ConstitutionalCoverage

open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation

/-- The four molecular sites can be listed in any order for this test.
Only actual positions and their determinant enter the physical hypothesis. -/
def NonzeroVolume (g : Geometry) (ids : List Nat) : Prop :=
  ∃ a b c d, [a,b,c,d].Perm ids ∧ ∃ A B C D,
    g a = some A ∧ g b = some B ∧ g c = some C ∧ g d = some D ∧
    CartesianPoint3.orientedVolume A B C D ≠ 0

theorem NonzeroVolume.all_orders {g ids} (physical : NonzeroVolume g ids) (distinct : ids.Nodup)
    {order : List Nat} (permuted : order.Perm ids) : (readback? g order).isSome = true := by
  obtain ⟨a,b,c,d,same,A,B,C,D,ha,hb,hc,hd,nonzero⟩ := physical
  have seen : (readback? g [a,b,c,d]).isSome = true := by
    rcases lt_or_gt_of_ne nonzero with neg | pos
    · simp [readback?,ha,hb,hc,hd,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,neg]
    · simp [readback?,ha,hb,hc,hd,descriptorOfPriorityOrderedPoints?,descriptorOfOrientedVolume?,pos,not_lt.mpr pos.le]
  exact ReferenceFrame.readback_all_permutations (same.nodup_iff.mpr distinct) rfl seen order
    (permuted.trans same.symm)

/-- At this atom the four incident molecular occurrences have defined,
distinct constitutional sphere keys and a nondegenerate tetrahedral frame. -/
def StrictSite (m : RawMolecule) (g : Geometry) (depth i : Nat) : Prop :=
  let cs := occurrenceLigandCursors m (canonicalCenterRoot i)
  let ids := cs.map (·.node.atom)
  cs.length = 4 ∧ ids.Nodup ∧
    (∀ c ∈ cs, (atomicTree m 3 depth c).isSome = true) ∧
    (cs.map (molecularAtomicKey? m depth)).Nodup ∧ NonzeroVolume g ids

/-- Sorting molecular keys and reading the resulting order gives opposite
hands on the two geometries at every site in this class. -/
theorem StrictSite.ranked_hands {m g depth i} (h : StrictSite m g depth i) (bound : i < m.atomCount) :
    ∃ order hand, atomicOrder? m [i] depth = some order ∧
      Recursive.geometric g order order = some ⟨hand,hand.swap⟩ := by
  obtain ⟨four,distinct,total,keys,volume⟩ := h
  have root : occurrence? m [i] = some (canonicalCenterRoot i) := by simp [occurrence?,bound]
  obtain ⟨r,found⟩ := atomicRanking?_of_distinct_keys root four total keys
  let order := r.arms.map (·.cursor.node.atom)
  have same : r.focus = canonicalCenterRoot i := Option.some.inj (r.reached.symm.trans root)
  have complete : order.Perm ((occurrenceLigandCursors m (canonicalCenterRoot i)).map (·.node.atom)) := by
    simpa only [same,List.map_map,Function.comp_def,order] using
      (r.complete.map (fun c => c.node.atom))
  obtain ⟨hand,reading⟩ := Option.isSome_iff_exists.mp (volume.all_orders distinct complete)
  exact ⟨order,hand,by simp [atomicOrder?,found,order],by simp [Recursive.geometric,readback_mirror,reading]⟩

/-- A whole carbon report exists for every admitted graph satisfying these
per-carbon alternatives. They depend only on molecular bonds, atom data and
coordinates. They permit arbitrary ring connectivity and ring size. -/
theorem report_of_terminal_or_strict (input : LocalizedChemicalRing.Input) (depth : Nat)
    (covered : ∀ i ∈ RingCarbonReport.carbons input.molecule,
      (∃ h : i < input.molecule.atomCount, RingTerminalPair.Focus input.molecule i ∧
        ∃ a b, RingTerminalPair.Equivalent input.molecule ⟨i,h⟩ a b) ∨
      StrictSite input.molecule (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified) depth i) :
    ∃ report, RecursiveSigned.report? input depth = some report := by
  apply Option.isSome_iff_exists.mp
  apply (RecursiveSigned.report?_isSome_iff input depth).mpr
  intro i hi
  rcases covered i hi with terminal | strict
  · exact Or.inr (Or.inl ((RingTerminalPair.check?_isSome_iff _ _).mpr terminal))
  · obtain ⟨order,hand,ranked,read⟩ := strict.ranked_hands (RingCarbonReport.mem_carbons.mp hi).1
    exact Or.inl ((LocalIsotopeCarbonReport.at?_isSome_iff ..).mpr (Or.inl
      ((AtomicCarbonReport.at?_isSome_iff ..).mpr (Or.inr ⟨order,⟨hand,hand.swap⟩,ranked,read⟩))))

end TetraStereo.Engine.RingChemicalPriority.ConstitutionalCoverage

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ConstitutionalCoverage.NonzeroVolume.all_orders
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ConstitutionalCoverage.StrictSite.ranked_hands
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ConstitutionalCoverage.report_of_terminal_or_strict
