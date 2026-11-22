import TetraStereo.Engine.RingOccurrenceSchedule

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.OccurrenceTable
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive

abbrev Path := List Nat
abbrev Cell (m : RawMolecule) (g : Geometry) :=
  (p : Path) × Option (RingAuxiliaryInventory.Result m g p)
abbrev Table (m : RawMolecule) (g : Geometry) := List (Cell m g)



def read {m g} (p : Path) : Table m g → Option (RingAuxiliaryInventory.Result m g p)
  | [] => none
  | ⟨q,v⟩ :: rest => if atPath : q = p then atPath ▸ v else read p rest

private def publish {m g} (paths : List Path) (answer : DiscoveredSchedule.Store m g) : Table m g :=
  paths.map fun p => ⟨p,answer p⟩

private theorem read_publish {m g} (paths : List Path) (answer : DiscoveredSchedule.Store m g)
    (p : Path) : read p (publish paths answer) = if p ∈ paths then answer p else none := by
  induction paths with
  | nil => simp [publish,read]
  | cons q qs ih =>
    by_cases eqn : q = p
    · subst q
      simp [publish,read]
    · have ne := Ne.symm eqn
      simp only [publish,List.map_cons,read,dif_neg eqn,List.mem_cons,ne,false_or] at *
      exact ih

/-- One set of dependency addresses for the next smaller fuel. Overlapping
branches and repeated requests contribute one row each. -/
def frontier (m : RawMolecule) (paths : List Path) : List Path :=
  (paths.dedup.flatMap (OccurrenceSchedule.dependencies m)).dedup

theorem mem_frontier {m paths q} :
    q ∈ frontier m paths ↔ ∃ p ∈ paths, q ∈ OccurrenceSchedule.dependencies m p := by
  simp [frontier]

/-- Construct the lower-fuel table first. All members of the current batch
read the same completed table. The caller provides only graph addresses,
coordinates, hints, search radii and fuel. -/
def evaluate (m : RawMolecule) (g : Geometry) (hint : Path → Option Recursive.Frame)
    (radius : Path → Nat) : Nat → List Path → Table m g
  | 0,_ => []
  | fuel+1,paths =>
    if paths = [] then [] else
      let lower := evaluate m g hint radius fuel (frontier m paths)
      publish paths.dedup (RingAuxiliaryInventory.classifyAt? m g hint radius (fun q => read q lower))

@[simp] theorem evaluate_empty {m g hint radius} (fuel : Nat) :
    evaluate m g hint radius fuel [] = [] := by
  cases fuel <;> rfl

theorem keys {m g hint radius fuel paths} :
    (evaluate m g hint radius (fuel+1) paths).map Sigma.fst = paths.dedup := by
  by_cases empty : paths = []
  · subst paths
    simp
  · simp [evaluate,empty,publish,List.map_map,Function.comp_def]

theorem unique {m g hint radius fuel paths} :
    ((evaluate m g hint radius (fuel+1) paths).map Sigma.fst).Nodup := by
  rw [keys]
  exact List.nodup_dedup _

/-- For every occurrence, the complete stored verdict equals recursive
classification at the same fuel if requested, and is unresolved otherwise.
No correctness hypothesis on the incoming store is required. -/
theorem read_evaluate (m : RawMolecule) (g : Geometry) (hint : Path → Option Recursive.Frame)
    (radius : Path → Nat) (fuel : Nat) (paths : List Path) (p : Path) :
    read p (evaluate m g hint radius fuel paths) =
      if p ∈ paths then RingAuxiliaryInventory.classify? m g hint radius fuel p else none := by
  induction fuel generalizing paths p with
  | zero =>
    simp [evaluate,read,RingAuxiliaryInventory.classify?]
  | succ fuel ih =>
    by_cases empty : paths = []
    · subst paths
      simp [read]
    · simp only [evaluate,if_neg empty,read_publish,List.mem_dedup]
      by_cases requested : p ∈ paths
      · simp only [if_pos requested,RingAuxiliaryInventory.classify?]
        apply OccurrenceSchedule.classifyAt?_of_dependencies
        intro q needed
        have included : q ∈ frontier m paths := mem_frontier.mpr ⟨p,requested,needed⟩
        simpa only [if_pos included] using ih (frontier m paths) q
      · simp only [if_neg requested]

/-- Reordering a batch, or changing how often a supplied request is repeated,
preserves the entire observable dependent store. -/
theorem same_requests (m : RawMolecule) (g : Geometry) (hint : Path → Option Recursive.Frame)
    (radius : Path → Nat) (fuel : Nat) {left right : List Path}
    (same : ∀ p, p ∈ left ↔ p ∈ right) (p : Path) :
    read p (evaluate m g hint radius fuel left) = read p (evaluate m g hint radius fuel right) := by
  rw [read_evaluate,read_evaluate]
  simp only [same p]

theorem permute_batch (m : RawMolecule) (g : Geometry) (hint : Path → Option Recursive.Frame)
    (radius : Path → Nat) (fuel : Nat) {left right : List Path} (perm : left.Perm right) (p : Path) :
    read p (evaluate m g hint radius fuel left) = read p (evaluate m g hint radius fuel right) :=
  same_requests m g hint radius fuel (fun _ => perm.mem_iff) p

/-- All addresses that can still be requested after descending the indicated
number of dependency layers from the original batch. -/
def frontierAt (m : RawMolecule) : Nat → List Path → List Path
  | 0,paths => paths
  | n+1,paths => frontierAt m n (frontier m paths)

/-- An empty molecular frontier certifies a sufficient fuel for every requested
address at once. Additional fuel preserves failures as well as all successful
results, with no assumed convergence of recursive classification. -/
theorem stable_of_empty_frontier (m : RawMolecule) (g : Geometry) (hint : Path → Option Recursive.Frame)
    (radius : Path → Nat) (n extra : Nat) (paths : List Path) (p : Path)
    (empty : frontierAt m n paths = []) (requested : p ∈ paths) :
    RingAuxiliaryInventory.classify? m g hint radius n p =
      RingAuxiliaryInventory.classify? m g hint radius (n+extra) p := by
  induction n generalizing paths p with
  | zero =>
    change paths = [] at empty
    simp [empty] at requested
  | succ n ih =>
    change frontierAt m n (frontier m paths) = [] at empty
    rw [Nat.succ_add]
    apply OccurrenceSchedule.classifyAt?_of_dependencies
    intro q needed
    exact ih (frontier m paths) q empty (mem_frontier.mpr ⟨p,requested,needed⟩)

private def nextNode (m : RawMolecule) (n : RawMolecule.CanonicalBranchNode) (i : Nat) :=
  (m.canonicalChildren n).find? (fun c => c.atom == i && !c.forcedLeaf)

private theorem walk_good {m : RawMolecule} (valid : WellFormedBonds m) (steps : Path)
    (n : RawMolecule.CanonicalBranchNode) (good : GoodNode m n)
    {r : RawMolecule.CanonicalBranchNode} (found : steps.foldlM (nextNode m) n = some r) :
    GoodNode m r := by
  induction steps generalizing n with
  | nil =>
    have same : n = r := by simpa using found
    exact same ▸ good
  | cons i steps ih =>
    cases edge : nextNode m n i with
    | none => simp [List.foldlM_cons,edge] at found
    | some child =>
      have selected : (m.canonicalChildren n).find? (fun c => c.atom == i && !c.forcedLeaf) =
          some child := edge
      have chosen := List.find?_some
        (p := fun c : RawMolecule.CanonicalBranchNode => c.atom == i && !c.forcedLeaf)
        (a := child) selected
      have real : child.forcedLeaf = false := by
        simpa using (Bool.and_eq_true_iff.mp chosen).2
      apply ih child (good.child valid (List.mem_of_find?_eq_some selected) real)
      simpa [List.foldlM_cons,edge] using found

theorem reached_length {m : RawMolecule} (valid : WellFormedBonds m) {p : Path}
    {n : RawMolecule.CanonicalBranchNode} (found : occurrence? m p = some n) :
    p.length ≤ m.atomCount := by
  have good : GoodNode m n := by
    cases p with
    | nil => simp [occurrence?] at found
    | cons a steps =>
      by_cases inRange : a < m.atomCount
      · have root : GoodNode m (canonicalCenterRoot a) := by
          refine ⟨List.nodup_singleton _,?_⟩
          intro i hi
          have eqn : i = a := by simpa [canonicalCenterRoot] using hi
          simpa only [eqn] using inRange
        apply walk_good valid steps _ root
        simpa [occurrence?,nextNode,guard,inRange] using found
      · simp [occurrence?,guard,inRange] at found
  rw [← OccurrenceSchedule.occurrence_address found,List.length_reverse]
  exact good.length_le

private theorem frontierAt_succ (m : RawMolecule) (n : Nat) (paths : List Path) :
    frontierAt m (n+1) paths = frontier m (frontierAt m n paths) := by
  induction n generalizing paths with
  | zero => rfl
  | succ n ih => exact ih (frontier m paths)

private theorem frontier_length {m : RawMolecule} {paths : List Path} (n : Nat) {q : Path}
    (member : q ∈ frontierAt m n paths) : n ≤ q.length := by
  induction n generalizing q with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [frontierAt_succ] at member
    obtain ⟨p,above,child⟩ := mem_frontier.mp member
    exact Nat.lt_of_le_of_lt (ih above) (OccurrenceSchedule.dependencies_deeper child)

/-- Regardless of supplied starting addresses, real molecular walks cannot
carry a dependency beyond all atom indices. The extra two levels admit even
the empty starting address, which can request a one-atom root. -/
theorem atom_bound_frontier (m : RawMolecule) (valid : WellFormedBonds m) (paths : List Path) :
    frontierAt m (m.atomCount+2) paths = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q member
  rw [frontierAt_succ] at member
  obtain ⟨p,previous,needed⟩ := mem_frontier.mp member
  have long : m.atomCount+1 ≤ p.length := frontier_length (m.atomCount+1) previous
  have nonempty : p ≠ [] := by intro empty; simp [empty] at long
  have missing : occurrence? m p = none := by
    cases atPath : occurrence? m p with
    | none => rfl
    | some n => have short := reached_length valid atPath; omega
  rw [OccurrenceSchedule.dependencies_of_unreached nonempty missing] at needed
  exact List.not_mem_nil needed

/-- One molecular fuel works simultaneously at all addresses, including
invalid or unresolved requests. Further recursion cannot alter the result. -/
theorem classification_stable (m : RawMolecule) (valid : WellFormedBonds m) (g : Geometry)
    (hint : Path → Option Recursive.Frame) (radius : Path → Nat) (p : Path) (extra : Nat) :
    RingAuxiliaryInventory.classify? m g hint radius (m.atomCount+2) p =
      RingAuxiliaryInventory.classify? m g hint radius (m.atomCount+2+extra) p :=
  stable_of_empty_frontier m g hint radius _ extra [p] p (atom_bound_frontier m valid _) (by simp)

/-- The neutral saturated molecular admission used by the ring API already
checks both endpoints of each bond. -/
theorem endpoints_of_saturated {m : RawMolecule} (accepted : saturatedWithHalogens m = true) :
    WellFormedBonds m := by
  have admitted : m.admissible? = true := by
    change (m.admissible? && _ && _) = true at accepted
    simp only [Bool.and_eq_true] at accepted
    tauto
  have valid := (m.admissible?_eq_true_iff.mp admitted).1
  intro b member
  exact ⟨(valid b member).1,(valid b member).2.1⟩

end TetraStereo.Engine.RingChemicalPriority.OccurrenceTable

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceTable.mem_frontier
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceTable.unique
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceTable.read_evaluate
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceTable.permute_batch
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceTable.stable_of_empty_frontier
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceTable.classification_stable
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceTable.endpoints_of_saturated
