import TetraStereo.Engine.RingDiscoveredSchedule

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive DiscoveredSchedule

private def advance (m : RawMolecule) (n : RawMolecule.CanonicalBranchNode) (i : Nat) :=
  (m.canonicalChildren n).find? (fun child => child.atom == i && !child.forcedLeaf)

private theorem walk_address {m : RawMolecule} (steps : List Nat) (n : RawMolecule.CanonicalBranchNode)
    {r : RawMolecule.CanonicalBranchNode} (found : steps.foldlM (advance m) n = some r) :
    r.history.reverse = n.history.reverse ++ steps := by
  induction steps generalizing n with
  | nil =>
    have same : n = r := by simpa using found
    subst r
    simp
  | cons i steps ih =>
    cases next : advance m n i with
    | none => simp [List.foldlM_cons,next] at found
    | some child =>
      have edge := List.mem_of_find?_eq_some (show
        (m.canonicalChildren n).find? (fun c => c.atom == i && !c.forcedLeaf) = some child from next)
      have both := List.find?_some
        (show (m.canonicalChildren n).find? (fun c => c.atom == i && !c.forcedLeaf) = some child from next)
      have atom : child.atom = i := eq_of_beq (Bool.and_eq_true_iff.mp both).1
      have rest : steps.foldlM (advance m) child = some r := by
        simpa [List.foldlM_cons,next] using found
      simpa [m.canonicalChildren_history n child edge,atom,List.append_assoc] using ih child rest

theorem occurrence_address {m : RawMolecule} {p : List Nat} {n : RawMolecule.CanonicalBranchNode}
    (found : occurrence? m p = some n) : n.history.reverse = p := by
  cases p with
  | nil => simp [occurrence?] at found
  | cons a steps =>
    by_cases bound : a < m.atomCount
    · have h : steps.foldlM (advance m) (canonicalCenterRoot a) = some n := by
        simpa [occurrence?,advance,guard,bound] using found
      simpa [canonicalCenterRoot] using walk_address steps (canonicalCenterRoot a) h
    · simp [occurrence?,guard,bound] at found

/-- Hinted arms append one atom before looking up their occurrence. At the
empty address this can reach any one-atom root even though that address
has no focus. At a nonempty address only the actual children can be reached. -/
private def starts (m : RawMolecule) : List Nat → List RawMolecule.CanonicalBranchNode
  | [] => (List.range m.atomCount).map canonicalCenterRoot
  | a :: ps => ((occurrence? m (a :: ps)).toList).flatMap m.canonicalChildren

/-- A finite, geometry-independent list containing every external child read.
An unavailable branch contributes no addresses because a failed inventory
cannot request a stored result. Earlier decisions can use fewer addresses. -/
def dependencies (m : RawMolecule) (p : List Nat) : List (List Nat) :=
  (starts m p).flatMap (fun n => (carbonSites m (m.atomCount+1) n).getD [])

theorem dependencies_of_unreached {m : RawMolecule} {p : List Nat} (nonempty : p ≠ [])
    (unreached : occurrence? m p = none) : dependencies m p = [] := by
  cases p with
  | nil => exact (nonempty rfl).elim
  | cons a ps => simp [dependencies,starts,unreached]

private theorem mem_dependencies {m p n ps q} (start : n ∈ starts m p)
    (sites : carbonSites m (m.atomCount+1) n = some ps) (member : q ∈ ps) :
    q ∈ dependencies m p :=
  List.mem_flatMap.mpr ⟨n,start,by simpa [sites] using member⟩

private theorem child_start {m p n u} (found : occurrence? m p = some n)
    (edge : u ∈ m.canonicalChildren n) : u ∈ starts m p := by
  cases p with
  | nil => simp [occurrence?] at found
  | cons a ps => simp [starts,found,edge]

private theorem hinted_start {m p i n} (found : occurrence? m (p ++ [i]) = some n) :
    n ∈ starts m p := by
  cases p with
  | nil =>
    by_cases bound : i < m.atomCount
    · have root : canonicalCenterRoot i = n := by simpa [occurrence?,guard,bound] using found
      exact List.mem_map.mpr ⟨i,List.mem_range.mpr bound,root⟩
    · simp [occurrence?,guard,bound] at found
  | cons a ps =>
    have one : occurrence? m ((a :: ps) ++ [i]) =
        (occurrence? m (a :: ps)).bind (fun c => advance m c i) := by
      by_cases bound : a < m.atomCount <;>
        simp [occurrence?,guard,bound,advance,List.foldlM_append,List.foldlM_cons]
    rw [one] at found
    obtain ⟨parent,reached,edge⟩ := Option.bind_eq_some_iff.mp found
    exact child_start reached (List.mem_of_find?_eq_some
      (show (m.canonicalChildren parent).find? (fun c => c.atom == i && !c.forcedLeaf) = some n from edge))

theorem dependencies_deeper {m p q} (member : q ∈ dependencies m p) : p.length < q.length := by
  obtain ⟨n,start,within⟩ := List.mem_flatMap.mp member
  cases sites : carbonSites m (m.atomCount+1) n with
  | none => simp [sites] at within
  | some ps =>
    have hp : q ∈ ps := by simpa [sites] using within
    obtain ⟨tail,rfl⟩ := carbonSites_address sites hp
    cases p with
    | nil =>
      obtain ⟨a,_,rfl⟩ := List.mem_map.mp start
      simp [canonicalCenterRoot]
    | cons a path =>
      obtain ⟨focus,atFocus,edge⟩ := List.mem_flatMap.mp start
      have addr := occurrence_address (Option.mem_toList.mp atFocus)
      have len := congrArg List.length addr
      simp only [List.length_reverse] at len
      simp [m.canonicalChildren_history focus n edge,len]

private theorem positive_collect_congr {P : List Nat → Reading → Prop}
    (s t : (q : List Nat) → Option {v // P q v}) (paths : List (List Nat))
    (same : ∀ q ∈ paths, s q = t q) :
    Promotion.collect s paths = Promotion.collect t paths := by
  induction paths with
  | nil => rfl
  | cons q qs ih =>
    simp only [Promotion.collect]
    rw [same q List.mem_cons_self, ih (fun p h => same p (List.mem_cons_of_mem q h))]

private theorem arm_congr {P : List Nat → Reading → Prop} (m : RawMolecule)
    {p : List Nat} (focus : RawMolecule.CanonicalBranchNode) (reached : occurrence? m p = some focus)
    (s t : (q : List Nat) → Option {v // P q v})
    (same : ∀ q ∈ dependencies m p, s q = t q) (i : Nat) :
    Promotion.prepareArm? m focus s i = Promotion.prepareArm? m focus t i := by
  by_cases parent : (canonicalOriginalParent? focus).map (·.atom) = some i
  · simp [Promotion.prepareArm?,parent]
  cases edge : ((m.canonicalChildren focus).find? (fun n => n.atom == i)).attach with
  | none => simp [Promotion.prepareArm?,parent,edge]
  | some x =>
    obtain ⟨n,hn⟩ := x
    cases sites : (carbonSites m (m.atomCount+1) n).attach with
    | none => simp [Promotion.prepareArm?,parent,edge,sites]
    | some x =>
      obtain ⟨ps,hp⟩ := x
      have valid : n ∈ m.canonicalChildren focus := List.mem_of_find?_eq_some hn
      have read (q : List Nat) (h : q ∈ ps) : s q = t q :=
        same q (mem_dependencies (child_start reached valid) hp h)
      simp only [Promotion.prepareArm?,dif_neg parent,edge,sites,Option.bind_eq_bind,Option.bind_some]
      rw [positive_collect_congr s t ps read]

private theorem preparation_congr {P : List Nat → Reading → Prop} (m : RawMolecule)
    (p : List Nat) (d : Nat) (s t : (q : List Nat) → Option {v // P q v})
    (same : ∀ q ∈ dependencies m p, s q = t q) :
    Promotion.prepareWith? m p d s = Promotion.prepareWith? m p d t := by
  by_cases domain : saturatedWithHalogens m = true
  · cases reached : (occurrence? m p).attach with
    | none => simp [Promotion.prepareWith?,domain,reached]
    | some x =>
      obtain ⟨n,hn⟩ := x
      have arms := funext (arm_congr m n hn s t same)
      simp only [Promotion.prepareWith?,dif_pos domain,reached,Option.bind_eq_bind,Option.bind_some]
      rw [arms]
  · simp [Promotion.prepareWith?,domain]

private theorem promoted_congr {m g} (p : List Nat) (d : Nat) (s t : Store m g)
    (same : ∀ q ∈ dependencies m p, s q = t q) :
    RingAuxiliaryInventory.promotedAt? p d s = RingAuxiliaryInventory.promotedAt? p d t := by
  have h := preparation_congr m p d (fun q => (s q).bind RingAuxiliaryInventory.Result.positive?)
    (fun q => (t q).bind RingAuxiliaryInventory.Result.positive?)
    (fun q h => congrArg (fun v => v.bind RingAuxiliaryInventory.Result.positive?) (same q h))
  unfold RingAuxiliaryInventory.promotedAt? Promotion.prepareAt?
  rw [h]

private def armRows {m g} (p : List Nat) (s : Store m g) (i : Nat) := do
  let n ← occurrence? m (p ++ [i])
  RingAuxiliaryInventory.collectRows s (← carbonSites m (m.atomCount+1) n)

private theorem armRows_congr {m g} (p : List Nat) (s t : Store m g)
    (same : ∀ q ∈ dependencies m p, s q = t q) (i : Nat) :
    armRows p s i = armRows p t i := by
  cases reached : occurrence? m (p ++ [i]) with
  | none => simp [armRows,reached]
  | some n =>
    cases sites : carbonSites m (m.atomCount+1) n with
    | none => simp [armRows,reached,sites]
    | some ps =>
      simp [armRows,reached,sites]
      exact collect_congr s t ps (fun q h => same q (mem_dependencies (hinted_start reached) sites h))

theorem compareAt?_congr {m g} (p : List Nat) (d : Nat) (f : Recursive.Frame) (s t : Store m g)
    (same : ∀ q ∈ dependencies m p, s q = t q) :
    RingAuxiliaryInventory.compareAt? p d f s = RingAuxiliaryInventory.compareAt? p d f t := by
  have left := armRows_congr p s t same f.left
  have right := armRows_congr p s t same f.right
  unfold armRows at left right
  unfold RingAuxiliaryInventory.compareAt?
  dsimp only
  rw [left,right]

private theorem signedPaired_congr {m g} (p : List Nat) (d : Nat) (s t : Store m g)
    (same : ∀ q ∈ dependencies m p, s q = t q) :
    RingAuxiliaryInventory.signedPairedAt? p d s = RingAuxiliaryInventory.signedPairedAt? p d t := by
  unfold RingAuxiliaryInventory.signedPairedAt?
  by_cases domain : saturatedWithHalogens m = true
  · cases (occurrence? m p).attach with
    | none => simp [domain]
    | some v =>
      obtain ⟨n,hn⟩ := v
      have agree := collect_congr s t (RingAuxiliaryInventory.promotionPaths m n) (by
        intro q h
        obtain ⟨c,edge,inside⟩ := List.mem_flatMap.mp h
        cases found : carbonSites m (m.atomCount+1) c with
        | none => simp [found] at inside
        | some paths => exact same q (mem_dependencies (child_start hn edge) found (by simpa [found] using inside)))
      simp only [dif_pos domain,Option.bind_eq_bind,Option.bind_some]
      unfold RingAuxiliaryInventory.gatherSigned?
      rw [agree]
  · simp [domain]

/-- The actual single update of the recursive classifier uses only strictly
deeper stored outcomes, through the constitutional, hinted, promotion and
discovered priority branches. The equality includes successful and failed searches. -/
theorem classifyAt?_of_dependencies {m g} (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat)
    (p : List Nat) (s t : Store m g)
    (same : ∀ q ∈ dependencies m p, s q = t q) :
    RingAuxiliaryInventory.classifyAt? m g hint radius s p =
      RingAuxiliaryInventory.classifyAt? m g hint radius t p := by
  have discovered := discoverAt?_congr (p := p) (d := radius p) s t (by
    intro f _ q h
    rcases List.mem_append.mp h with l | r
    · exact same q (mem_dependencies (child_start f.reached f.leftAt.1) f.leftComplete l)
    · exact same q (mem_dependencies (child_start f.reached f.rightAt.1) f.rightComplete r))
  simp only [RingAuxiliaryInventory.classifyAt?,promoted_congr p (radius p) s t same,
    discovered,signedPaired_congr p (radius p) s t same,fun f => compareAt?_congr p (radius p) f s t same]

theorem classifyAt?_congr {m g} (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat)
    (p : List Nat) (s t : Store m g)
    (same : ∀ q : List Nat, p.length < q.length → s q = t q) :
    RingAuxiliaryInventory.classifyAt? m g hint radius s p =
      RingAuxiliaryInventory.classifyAt? m g hint radius t p :=
  classifyAt?_of_dependencies hint radius p s t (fun q h => same q (dependencies_deeper h))

/-- The direct recursive evaluator is iteration of this actual single update,
starting with no available children. -/
theorem classify?_successor {m g} (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat)
    (fuel : Nat) (p : List Nat) :
    RingAuxiliaryInventory.classify? m g hint radius (fuel+1) p =
      RingAuxiliaryInventory.classifyAt? m g hint radius
        (RingAuxiliaryInventory.classify? m g hint radius fuel) p := rfl

/-- Publish one direct classifier outcome at its occurrence. -/
def refresh {m g} (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat)
    (s : Store m g) (q : List Nat) : Store m g :=
  fun p => if p = q then RingAuxiliaryInventory.classifyAt? m g hint radius s p else s p

def run {m g} (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat)
    (s : Store m g) (events : List (List Nat)) : Store m g :=
  events.foldl (refresh hint radius) s

theorem run_layer {m g} (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) (distance : Nat)
    (events : List (List Nat)) (level : ∀ q ∈ events, q.length = distance)
    (s : Store m g) (p : List Nat) :
    run hint radius s events p =
      if p ∈ events then RingAuxiliaryInventory.classifyAt? m g hint radius s p else s p := by
  induction events generalizing s with
  | nil => simp [run]
  | cons q qs ih =>
    have qLevel := level q List.mem_cons_self
    have rest : ∀ x ∈ qs, x.length = distance := fun x h => level x (List.mem_cons_of_mem q h)
    change run hint radius (refresh hint radius s q) qs p = _
    rw [ih rest]
    by_cases later : p ∈ qs
    · have done := classifyAt?_congr hint radius p (refresh hint radius s q) s (by
        intro x deeper
        have diff : x ≠ q := by
          intro h
          subst x
          rw [rest p later,qLevel] at deeper
          exact (Nat.lt_irrefl _ deeper)
        simp [refresh,diff])
      simp [later,done]
    · by_cases current : p = q
      · subst p
        simp [later,refresh]
      · simp [later,current,refresh]

theorem permute_layer {m g} (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat)
    (s : Store m g) (distance : Nat) {a b : List (List Nat)} (perm : a.Perm b)
    (level : ∀ q ∈ a, q.length = distance) : run hint radius s a = run hint radius s b := by
  funext p
  rw [run_layer hint radius distance a level s p,
    run_layer hint radius distance b (fun q h => level q (perm.mem_iff.mpr h)) s p]
  simp only [perm.mem_iff]

end TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.occurrence_address
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.classifyAt?_congr
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.classify?_successor
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.run_layer
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.permute_layer
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.classifyAt?_of_dependencies
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.OccurrenceSchedule.dependencies_deeper
