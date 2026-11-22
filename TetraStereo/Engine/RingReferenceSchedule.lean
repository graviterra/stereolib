import TetraStereo.Engine.RingReferenceDerivation
import TetraStereo.Engine.RingDiscoveredSchedule
import TetraStereo.Engine.CentresRingPaths

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation
open OneCenter LocalizedGenericMarkedRecalculation Recursive
open InventoryPriority (Entries)

/-- A strict extension in the rooted molecular digraph. -/
abbrev Below (p q : List Nat) := p <+: q ∧ p.length < q.length

private theorem below_append (p : List Nat) (i : Nat) (tail : List Nat) : Below p (p ++ i :: tail) :=
  ⟨⟨i :: tail,rfl⟩,by simp⟩

private theorem below_trans {p q t : List Nat} (x : Below p q) (y : Below q t) : Below p t :=
  ⟨x.1.trans y.1,Nat.lt_trans x.2 y.2⟩

private theorem single_below {m p d ls rs} (f : SignedPair.Frame m p d)
    (left : List.map Prod.fst ls = f.leftPaths) (right : List.map Prod.fst rs = f.rightPaths)
    {x : List Nat × Option Reading} (h : x ∈ ls ++ rs) : Below p x.1 := by
  have path : x.1 ∈ f.requiredPaths := by
    simpa [SignedPair.Frame.requiredPaths,← left,← right] using (List.mem_map_of_mem (f := Prod.fst) h)
  obtain ⟨i,tail,_,eqn⟩ := DiscoveredSchedule.required_address f path
  rw [eqn]
  exact below_append p i tail

private theorem arm_below {m p i} (arm : ReferenceDistance.Arm m (p ++ [i]))
    (atPath : arm.node.history.reverse = p ++ [i]) {x} (member : x ∈ arm.entries) : Below p x.1 := by
  obtain ⟨tail,eqn⟩ := DiscoveredSchedule.carbonSites_address arm.coverage
    (List.mem_map_of_mem (f := Prod.fst) member)
  simpa [eqn,atPath,List.append_assoc] using below_append p i tail

private theorem frame_below {m g p} (s : ReferenceFrame.MolecularFrame m g p) {x} (h : x ∈ s.inputs) :
    Below p x.1 := by
  obtain ⟨row,_,inRow⟩ := List.mem_flatMap.mp (List.mem_dedup.mp h)
  cases basis : row.basis with
  | atomic | constitution => simp [basis,ReferenceFrame.Basis.inputs] at inRow
  | fourth arms _ _ =>
    rcases List.mem_append.mp (show x ∈ arms.left.entries ++ arms.right.entries by
      simpa [basis,ReferenceFrame.Basis.inputs] using inRow) with hx | hx
    · exact arm_below arms.left arms.leftPath hx
    · exact arm_below arms.right arms.rightPath hx
  | stereo pair _ _ _ | tied pair _ =>
    rcases List.mem_append.mp (show x ∈ pair.left.entries ++ pair.right.entries by
      simpa [basis,ReferenceFrame.Basis.inputs] using inRow) with hx | hx
    · exact arm_below pair.left pair.leftAt.2 hx
    · exact arm_below pair.right pair.rightAt.2 hx

/-- Every premise at every depth can be replayed if the target table
retains just the strict descendants of this occurrence. -/
theorem Derives.localize {m g es p v} (d : Derives m g es p v) {other : Entries}
    (keep : ∀ x ∈ es, Below p x.1 → x ∈ other) : Derives m g other p v := by
  induction d with
  | atomic ranked hand => exact .atomic ranked hand
  | isotopic ranked hand => exact .isotopic ranked hand
  | distinguished s bound _ hand ih =>
    have deeper := fun x hx => single_below s.frame s.leftCoverage s.rightCoverage (x := x) hx
    exact .distinguished s (fun x hx => keep x (bound hx) (deeper x hx))
      (fun x hx => ih x hx (fun y hy h => keep y hy (below_trans (deeper x hx) h))) hand
  | indistinguishable s bound _ ih =>
    have deeper := fun x hx => single_below s.frame s.leftKeys s.rightKeys (x := x) hx
    exact .indistinguishable s (fun x hx => keep x (bound hx) (deeper x hx))
      (fun x hx => ih x hx (fun y hy h => keep y hy (below_trans (deeper x hx) h)))
  | ordinary f s bound _ observed ih =>
    exact .ordinary f s (fun x hx => keep x (bound hx) (frame_below f hx))
      (fun x hx => ih x hx (fun y hy h => keep y hy (below_trans (frame_below f hx) h))) observed
  | promotion s bound _ agree ih =>
    exact .promotion s (fun x hx => keep x (bound hx) (frame_below s.frame.toMolecularFrame hx))
      (fun x hx => ih x hx (fun y hy h => keep y hy (below_trans (frame_below s.frame.toMolecularFrame hx) h))) agree

/-- In any decreasing-distance ordering of the actual publications, the
next signed verdict has a derivation using only the already published
prefix. Equal-distance rows may be permuted arbitrarily. -/
theorem Certificate.replay_next {m g p} (c : Certificate m g p) (prior later : Entries)
    (x : List Nat × Option Reading) (all : (prior ++ x :: later).Perm c.published)
    (ordered : (prior ++ x :: later).Pairwise fun a b => b.1.length ≤ a.1.length) :
    Derives m g prior x.1 x.2 := by
  have issued := c.issued x (all.mem_iff.mp (List.mem_append_right _ List.mem_cons_self))
  apply issued.localize
  intro y hy deep
  rcases List.mem_append.mp (all.mem_iff.mpr hy) with h | h
  · exact h
  · rcases List.mem_cons.mp h with rfl | tail
    · exact (Nat.lt_irrefl _ deep.2).elim
    · have bound := (List.pairwise_cons.mp (List.pairwise_append.mp ordered).2.1).1 y tail
      exact (Nat.not_lt_of_ge bound deep.2).elim

/-- All publications at the active distance, including those visited
earlier in the same batch, may be withheld until the batch is complete. -/
theorem Certificate.frozen_batch {m g p} (c : Certificate m g p) {x}
    (published : x ∈ c.published) :
    Derives m g (c.published.filter (fun y => x.1.length < y.1.length)) x.1 x.2 :=
  (c.issued x published).localize (fun _ hy below => List.mem_filter.mpr ⟨hy,decide_eq_true below.2⟩)

/-- A replay starts from an empty store and justifies every publication
from the preceding prefix, followed by the root decision. -/
def Scheduled (m : RawMolecule) (g : Geometry) (p : List Nat) (v : Option Reading) (rows : Entries) :=
  Derives m g rows p v ∧ ∀ before x after, rows = before ++ x :: after → Derives m g before x.1 x.2

theorem Certificate.scheduled {m g p} (c : Certificate m g p) {rows : Entries}
    (perm : rows.Perm c.published) (sorted : rows.Pairwise fun a b => b.1.length ≤ a.1.length) :
    Scheduled m g p c.verdict rows := by
  refine ⟨c.derived.weaken perm.symm.subset,?_⟩
  intro before x after h
  subst rows
  exact c.replay_next _ _ _ perm sorted

def byDistance (discovered : Entries) : Entries :=
  discovered.mergeSort fun a b => decide (b.1.length ≤ a.1.length)

/-- Sorting the signed rows preserves exactly the ordered addresses in the
pinned Centres scheduler, including its tie order for this discovery list. -/
theorem byDistance_paths (es : Entries) :
    (byDistance es).map Prod.fst = (CentresRing.scheduled (es.map Prod.fst)).map Prod.fst := by
  let rank := fun (a b : List Nat) => decide (b.length ≤ a.length)
  rw [byDistance,CentresRing.scheduled,CentresRing.replayListSort_eq,
    List.map_mergeSort (s := rank) (fun _ _ _ _ => rfl),
    List.map_mergeSort (s := rank) (fun _ _ _ _ => rfl),List.zipIdx_map_fst]

/-- Any discovery permutation leads to an exact decreasing-distance
schedule under which the same signed verdicts and root can be derived. -/
theorem Certificate.byDistance_replays {m g p} (c : Certificate m g p) {es : Entries}
    (discovered : es.Perm c.published) : Scheduled m g p c.verdict (byDistance es) := by
  apply c.scheduled ((List.mergeSort_perm ..).trans discovered)
  simpa only [decide_eq_true_eq] using (List.pairwise_mergeSort
    (le := fun (a b : List Nat × Option Reading) => decide (b.1.length ≤ a.1.length))
    (fun _ _ _ h1 h2 => decide_eq_true (le_trans (of_decide_eq_true h2) (of_decide_eq_true h1)))
    (fun a b => by simpa only [Bool.or_eq_true_iff,decide_eq_true_eq] using le_total b.1.length a.1.length) es)

end TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Derives.localize
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Certificate.replay_next
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Certificate.frozen_batch

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.Certificate.byDistance_replays
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceDerivation.byDistance_paths
