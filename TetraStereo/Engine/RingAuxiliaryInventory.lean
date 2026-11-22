import TetraStereo.Engine.RingTwoPairPriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.RingAuxiliaryInventory
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive Promotion

/-- The complete parent step retains every omission certificate used to
choose its ligand order, including the positive readings below each omission. -/
structure Assignment (m : RawMolecule) (g : Geometry) (p : List Nat) where
  depth : Nat
  frame : Recursive.Frame
  left : InventoryPriority.Entries
  right : InventoryPriority.Entries
  step : InventoryPriority.Step m p depth frame left right
  missing : List ((q : List Nat) × BareSinglePair m q)
  complete : (missing.map Sigma.fst).Perm (InventoryPriority.omissions (left ++ right))
  positive : ∀ q v, (q,some v) ∈ left ++ right → Justified m g q v
  children : ∀ c ∈ missing, ∀ a ∈ c.2.experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2
  consistent : ∀ c ∈ missing, ∀ a ∈ c.2.experiment.arms, ∀ x ∈ a.facts,
    (x.1,some x.2) ∈ left ++ right
  reading : Reading
  read : geometric g (frame.order step.orders.1) (frame.order step.orders.2) = some reading

theorem Assignment.justified {m g p} (a : Assignment m g p) : Justified m g p a.reading :=
  .inventory a.step a.missing a.complete a.positive a.children a.consistent a.read

/-- Reconstruct each negative child's full certificate at its original path. -/
def Assignment.absences {m g p} (a : Assignment m g p) :
    List ((q : List Nat) × SinglePairAbsence m g q) :=
  a.missing.attach.map fun c => ⟨c.val.1,c.val.2,a.children c.val c.property⟩

theorem Assignment.absenceCoverage {m g p} (a : Assignment m g p) :
    (a.absences.map Sigma.fst).Perm (InventoryPriority.omissions (a.left ++ a.right)) := by
  simpa [absences,List.map_map,Function.comp_def] using a.complete

/-- A matched pair of fully decorated arms, including nested absences. -/
structure NestedAbsence (m : RawMolecule) (g : Geometry) (p : List Nat) where
  pair : SignedPair.Pair m p
  positive : ∀ q v, (q,some v) ∈ pair.required → Justified m g q v
  negative : ∀ q, (q,none) ∈ pair.required → ∃ es, Negative m q es ∧ es ⊆ pair.required

/-- The molecular comparison together with the complete, coherent signed
inventories that discharge all its chemical premises. -/
structure SignedAssignment (m : RawMolecule) (g : Geometry) (p : List Nat) where
  depth : Nat
  frame : Recursive.Frame
  left : InventoryPriority.Entries
  right : InventoryPriority.Entries
  step : InventoryPriority.Step m p depth frame left right
  positive : ∀ q v, (q,some v) ∈ left ++ right → Justified m g q v
  negative : ∀ q, (q,none) ∈ left ++ right → ∃ es, Negative m q es ∧ es ⊆ left ++ right
  reading : Reading
  read : geometric g (frame.order step.orders.1) (frame.order step.orders.2) = some reading

theorem SignedAssignment.justified {m g p} (a : SignedAssignment m g p) : Justified m g p a.reading :=
  .signedInventory a.step a.positive a.negative a.read

/-- Both orders and the winning rule are discovered at this occurrence. -/
structure Discovered (m : RawMolecule) (g : Geometry) (p : List Nat) where
  left : InventoryPriority.Entries
  right : InventoryPriority.Entries
  step : DiscoveredPriority.Step m p left right
  positive : ∀ q v, (q,some v) ∈ left ++ right → Justified m g q v
  negative : ∀ q, (q,none) ∈ left ++ right → ∃ es, Negative m q es ∧ es ⊆ left ++ right
  reading : Reading
  read : geometric g step.actual.ligands step.reflected.ligands = some reading

theorem Discovered.justified {m g p} (a : Discovered m g p) : Justified m g p a.reading :=
  .discovered a.step a.positive a.negative a.read

/-- Every eligible marking leaves a chemically matched pair and the same
geometry justifies all positive auxiliaries in the experiment. -/
structure PromotionAbsence (m : RawMolecule) (g : Geometry) (p : List Nat) where
  structural : StructuralRefusal m p
  children : ∀ a ∈ structural.experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2

/-- An absence and a failed search have different representations. -/
inductive Result (m : RawMolecule) (g : Geometry) (p : List Nat) where
  | assigned (value : Reading) (proof : Justified m g p value)
  | compared (certificate : Assignment m g p)
  | absent (certificate : SinglePairAbsence m g p)
  | nested (certificate : NestedAbsence m g p)
  | promotionTie (certificate : PromotionAbsence m g p)
  | signed (certificate : SignedAssignment m g p)
  | discovered (certificate : Discovered m g p)
  | paired (certificate : TwoPairPriority.Step m g p)
  | signedPaired (certificate : TwoPairPriority.SignedStep m g p)

def Result.reading {m g p} : Result m g p → Option Reading
  | .assigned r _ => some r
  | .compared s => some s.reading
  | .absent _ | .nested _ | .promotionTie _ => none
  | .signed a => some a.reading
  | .discovered a => some a.reading
  | .signedPaired a => some a.reading
  | .paired a => some a.reading

def Result.positive? {m g p} : Result m g p → Option {r // Justified m g p r}
  | .assigned r h => some ⟨r,h⟩
  | .compared s => some ⟨s.reading,s.justified⟩
  | .absent _ | .nested _ | .promotionTie _ => none
  | .signed a => some ⟨a.reading,a.justified⟩
  | .discovered a => some ⟨a.reading,a.justified⟩
  | .paired a => some ⟨a.reading,a.justified⟩
  | .signedPaired a => some ⟨a.reading,a.justified⟩

abbrev Located (m : RawMolecule) (g : Geometry) := (q : List Nat) × Result m g q

private def entries {m g} (rows : List (Located m g)) : InventoryPriority.Entries :=
  rows.map fun c => (c.1,c.2.reading)

private def missing {m g} (rows : List (Located m g)) :=
  rows.filterMap fun c => match c.2 with
    | .absent a => some (⟨c.1,a.toBareSinglePair⟩ : (q : List Nat) × BareSinglePair m q)
    | _ => none

private def required {m g p} : Result m g p → InventoryPriority.Entries
  | .absent a => a.toBareSinglePair.required
  | .nested c => c.pair.required
  | .promotionTie c => c.structural.required
  | _ => []

private theorem negative_of_none {m g p} (r : Result m g p) (h : r.reading = none) :
    Negative m p (required r) := by
  cases r with
  | absent c => exact .single c.toBareSinglePair
  | nested c => exact .signed c.pair c.negative
  | promotionTie c => exact .promotionTie c.structural
  | assigned | signed | discovered | signedPaired | paired | compared => contradiction

private def coherent {m g} (rows : List (Located m g)) := rows.all fun row =>
  (required row.2).all fun x => (entries rows).contains x

private theorem all_negative {m g} {rows : List (Located m g)} (ok : coherent rows = true)
    {q} (member : (q,none) ∈ entries rows) :
    ∃ es, Negative m q es ∧ es ⊆ entries rows := by
  obtain ⟨⟨p,r⟩,row,eqn⟩ := List.mem_map.mp member
  obtain ⟨rfl,hr⟩ := Prod.mk.inj eqn
  have incl := List.all_eq_true.mp (List.all_eq_true.mp ok _ row)
  exact ⟨_,negative_of_none r hr,fun _ hx => List.contains_iff_mem.mp (incl _ hx)⟩

private theorem all_positive {m g} {rows : List (Located m g)} {q v}
    (inside : (q,some v) ∈ entries rows) : Justified m g q v := by
  obtain ⟨⟨p,r⟩,_,eq⟩ := List.mem_map.mp inside
  cases r with
  | assigned w h =>
    cases eq
    exact h
  | compared c =>
    cases eq
    exact c.justified
  | absent c | nested c | promotionTie c => simp [Result.reading] at eq
  | signed c | discovered c | signedPaired c | paired c => cases eq; exact c.justified

private theorem children_below {m g} {rows : List (Located m g)} {c}
    (inside : c ∈ missing rows) :
    ∀ a ∈ c.2.experiment.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2 := by
  obtain ⟨⟨q,r⟩,_,eq⟩ := List.mem_filterMap.mp inside
  cases r with
  | assigned | compared | nested | promotionTie | signed | discovered | signedPaired | paired => contradiction
  | absent a =>
    cases eq
    exact a.children

def collectRows {m g} (child : (q : List Nat) → Option (Result m g q))
    (paths : List (List Nat)) : Option (List (Located m g)) :=
  paths.mapM fun q => do return ⟨q,← child q⟩

def compareAt? {m g} (p : List Nat) (d : Nat) (f : Recursive.Frame)
    (child : (q : List Nat) → Option (Result m g q)) : Option (Result m g p) := do
  let collectArm (i : Nat) := do
    let n ← occurrence? m (p ++ [i])
    collectRows child (← carbonSites m (m.atomCount+1) n)
  let ls ← collectArm f.left
  let rs ← collectArm f.right
  let s ← InventoryPriority.check? m p d f (entries ls) (entries rs)
  let ⟨r,h⟩ ← (geometric g (f.order s.orders.1) (f.order s.orders.2)).attach
  have both : entries (ls ++ rs) = entries ls ++ entries rs := List.map_append ..
  have pos : ∀ q v, (q,some v) ∈ entries ls ++ entries rs → Justified m g q v :=
    fun _ _ ok => all_positive (rows := ls ++ rs) (by rw [both]; exact ok)
  if coverage : (missing (ls ++ rs)).map Sigma.fst = InventoryPriority.omissions (entries ls ++ entries rs) then
    if consistent : ∀ c ∈ missing (ls ++ rs), ∀ a ∈ c.2.experiment.arms, ∀ x ∈ a.facts,
        (x.1,some x.2) ∈ entries ls ++ entries rs then
      return .compared ⟨d,f,entries ls,entries rs,s,missing (ls ++ rs),by rw [coverage],
        pos,fun _ hc => children_below hc,consistent,r,h⟩
  if ok : coherent (ls ++ rs) = true then
    have neg : ∀ q, (q,none) ∈ entries ls ++ entries rs →
        ∃ es, Negative m q es ∧ es ⊆ entries ls ++ entries rs := by
      rw [← both]
      exact fun _ inside => all_negative ok inside
    return .signed ⟨d,f,entries ls,entries rs,s,pos,neg,r,h⟩
  none

def discoverAt? {m g} (p : List Nat) (d : Nat)
    (child : (q : List Nat) → Option (Result m g q)) : Option (Result m g p) := do
  let frame ← SignedPair.frame? m p d
  let left ← collectRows child frame.leftPaths
  let right ← collectRows child frame.rightPaths
  let rows := left ++ right
  have both : entries rows = entries left ++ entries right := List.map_append ..
  if ok : coherent rows = true then
    if let some step := DiscoveredPriority.check? frame (entries left) (entries right) then
      let ⟨r,h⟩ ← (geometric g step.actual.ligands step.reflected.ligands).attach
      return .discovered ⟨entries left,entries right,step,
        by rw [← both]; exact fun _ _ member => all_positive member,
        by rw [← both]; exact fun _ member => all_negative ok member,r,h⟩
    let ⟨pair,_⟩ ← frame.checkWith? (entries rows)
    if same : pair.required = entries rows then
      return .nested ⟨pair,by rw [same]; exact fun _ _ h => all_positive h,
        by rw [same]; exact fun _ h => all_negative ok h⟩
  none

private def ordinaryPromotion? {m g p} (prepared : Prepared m g p) : Option (Result m g p) := do
  let e := prepared.experiment
  if let some ⟨c,same⟩ := bareAbsenceFor? e then
    return .absent ⟨c,by rw [same]; exact prepared.children⟩
  let ⟨ts,ht⟩ ← e.trials?.attach
  if let some ⟨c,same⟩ := structuralRefusal? e ts ht then
    return .promotionTie ⟨c,by rw [same]; exact prepared.children⟩
  let ⟨a,ha⟩ ← (result g ts).attach
  let ⟨b,hb⟩ ← (result (mirror g) ts).attach
  let ⟨x,hx⟩ ← a.attach
  let ⟨y,hy⟩ ← b.attach
  return .assigned ⟨x,y⟩ (.promotion e prepared.children ht (hx ▸ ha) (hy ▸ hb))

def promotedAt? {m g} (p : List Nat) (d : Nat)
    (child : (q : List Nat) → Option (Result m g q)) : Option (Result m g p) := do
  let prepared ← prepareAt? m g p d (fun q => (child q).bind Result.positive?)
  return ← (ordinaryPromotion? prepared).orElse fun _ => (TwoPairPriority.check? prepared).map Result.paired

/-- Addresses consulted by a signed promotion. The arm coverage checks below
reject a failed candidate traversal. -/
def promotionPaths (m : RawMolecule) (focus : RawMolecule.CanonicalBranchNode) :=
  (m.canonicalChildren focus).flatMap fun n => (carbonSites m (m.atomCount+1) n).getD []

private def signedArm? (m : RawMolecule) (focus : RawMolecule.CanonicalBranchNode)
    (omitted : List (List Nat)) (es : InventoryPriority.Entries) (i : Nat) :
    Option (Arm m focus omitted) := do
  let ⟨n,hn⟩ ← ((m.canonicalChildren focus).find? (fun n => n.atom == i)).attach
  let ps ← carbonSites m (m.atomCount+1) n
  let fs := InventoryPriority.positives (es.filter fun x => ps.contains x.1)
  if complete : positivePaths omitted (carbonSites m (m.atomCount+1) n) = some (fs.map Prod.fst) then
    return ⟨i,some n,⟨List.mem_of_find?_eq_some hn,by simpa using List.find?_some hn⟩,fs,complete⟩
  none

/-- The signed inventory is the only child data that the promotion reads.
Its proof fields certify observations from the same molecular geometry. -/
structure SignedInputs (m : RawMolecule) (g : Geometry) where
  entries : InventoryPriority.Entries
  positive : ∀ q v, (q,some v) ∈ entries → Justified m g q v
  negative : ∀ q, (q,none) ∈ entries → ∃ es, Negative m q es ∧ es ⊆ entries

def gatherSigned? {m g} (child : (q : List Nat) → Option (Result m g q)) (paths : List (List Nat)) :
    Option (SignedInputs m g) := do
  let rows ← collectRows child paths
  if ok : coherent rows = true then
    return ⟨entries rows,fun _ _ h => all_positive h,fun _ h => all_negative ok h⟩
  none

/-- Build just the chemical experiment from a candidate inventory. A
successful comparison still requires molecular proofs for all its entries. -/
def inventoryExperiment? {m p} (d : Nat) (focus : RawMolecule.CanonicalBranchNode)
    (domain : saturatedWithHalogens m = true) (reached : occurrence? m p = some focus)
    (carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true)
    (es : InventoryPriority.Entries) : Option (Experiment m p (InventoryPriority.omissions es)) := do
  let ids := (occurrenceLigandCursors m focus).map (·.node.atom)
  let omitted := InventoryPriority.omissions es
  let arms ← ids.mapM (signedArm? m focus omitted es)
  if incident : arms.map Arm.ligand = ids then
    if four : arms.length = 4 then
      if distinct : (arms.map Arm.ligand).Nodup then
        return ⟨d,domain,focus,reached,carbon,arms,incident,four,distinct⟩
  none

/-- A signed fallback must have at least one certified omission. -/
def signedExperiment? {m p} (d : Nat) (focus : RawMolecule.CanonicalBranchNode)
    (domain : saturatedWithHalogens m = true) (reached : occurrence? m p = some focus)
    (carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true)
    (es : InventoryPriority.Entries) : Option (Experiment m p (InventoryPriority.omissions es)) := do
  guard (!(InventoryPriority.omissions es).isEmpty)
  inventoryExperiment? d focus domain reached carbon es

def finishSignedPaired? {m g p} (inputs : SignedInputs m g)
    (e : Experiment m p (InventoryPriority.omissions inputs.entries)) : Option (Result m g p) := do
  let need := TwoPairPriority.required e
  if exactInventory : need.Perm inputs.entries then
    if unique : (need.map Prod.fst).Nodup then
      let cert ← TwoPairPriority.certify? e g
      have positives : ∀ a ∈ e.arms, ∀ x ∈ a.facts, Justified m g x.1 x.2 := by
        intro a ha x hx
        apply inputs.positive _ _ (exactInventory.mem_iff.mp _)
        exact List.mem_append_left _ (List.mem_map_of_mem
          (f := fun x : List Nat × Reading => (x.1,some x.2))
          (List.mem_flatMap.mpr ⟨a,ha,hx⟩))
      have negatives : ∀ q ∈ InventoryPriority.omissions inputs.entries,
          ∃ sub, Negative m q sub ∧ sub ⊆ need := by
        intro q h
        have member : (q,none) ∈ need :=
          List.mem_append_right _ (List.mem_map_of_mem (f := fun q => (q,none)) h)
        obtain ⟨sub,valid,inside⟩ := inputs.negative q (exactInventory.mem_iff.mp member)
        exact ⟨sub,valid,fun _ h => exactInventory.mem_iff.mpr (inside h)⟩
      return .signedPaired ⟨_,e,cert,positives,negatives,unique⟩
  none

def signedPairedAt? {m g} (p : List Nat) (d : Nat)
    (child : (q : List Nat) → Option (Result m g q)) : Option (Result m g p) := do
  if domain : saturatedWithHalogens m = true then
    let ⟨focus,reached⟩ ← (occurrence? m p).attach
    guard (canonicalOriginalParent? focus).isNone
    if carbon : (m.atoms[focus.atom]?).any (fun a => a.element == .C) = true then
      let ids := (occurrenceLigandCursors m focus).map (·.node.atom)
      let first ← ids.head?
      let prefixKey ← ligandRows? m p first d
      guard (ids.all fun i => ligandRows? m p i d == some prefixKey)
      let inputs ← gatherSigned? child (promotionPaths m focus)
      let e ← signedExperiment? d focus domain reached carbon inputs.entries
      return ← finishSignedPaired? inputs e
  none

/-- Read one occurrence using the available verdicts at its descendants. -/
def classifyAt? (m : RawMolecule) (g : Geometry) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) (child : (q : List Nat) → Option (Result m g q))
    (p : List Nat) : Option (Result m g p) := do
  let d := radius p
  if let some ⟨order,supported⟩ := constitutionalOrder? m p d then
    let ⟨r,h⟩ ← (geometric g order order).attach
    return .assigned r (.ordinary (supported g r h))
  if let some f := hint p then
    if let some s := compareAt? p d f child then return s
  if let some result := promotedAt? p d child then return result
  (discoverAt? p d child).orElse fun _ => signedPairedAt? p d child

/-- Assignments and certified absences use the same retained digraph.
Exhausting the search yields no verdict. -/
def classify? (m : RawMolecule) (g : Geometry) (hint : List Nat → Option Recursive.Frame)
    (radius : List Nat → Nat) : Nat → (p : List Nat) → Option (Result m g p)
  | 0,_ => none
  | fuel+1,p => classifyAt? m g hint radius (classify? m g hint radius fuel) p

/-- Complete signed inventory of an addressed outward branch. A negative
entry has a finite molecular derivation. All observations needed by it occur
in this same branch inventory. -/
structure ArmInventory (m : RawMolecule) (g : Geometry) (p : List Nat) where
  node : RawMolecule.CanonicalBranchNode
  reached : occurrence? m p = some node
  entries : InventoryPriority.Entries
  coverage : carbonSites m (m.atomCount+1) node = some (entries.map Prod.fst)
  unique : (entries.map Prod.fst).Nodup
  positive : ∀ q v, (q,some v) ∈ entries → Justified m g q v
  negatives : ∀ q, (q,none) ∈ entries → ∃ es, Negative m q es ∧ es ⊆ entries

def arm? (m : RawMolecule) (g : Geometry) (p : List Nat) (fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) :
    Option (ArmInventory m g p) := do
  let ⟨n,hn⟩ ← (occurrence? m p).attach
  let ⟨paths,found⟩ ← (carbonSites m (m.atomCount+1) n).attach
  let rows ← collectRows (classify? m g hint radius fuel) paths
  if cover : (entries rows).map Prod.fst = paths then
    if unique : ((entries rows).map Prod.fst).Nodup then
      if ok : coherent rows = true then
        return ⟨n,hn,entries rows,cover ▸ found,unique,
          fun _ _ member => all_positive member,fun _ member => all_negative ok member⟩
  none

end TetraStereo.Engine.RingChemicalPriority.RingAuxiliaryInventory
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RingAuxiliaryInventory.Assignment.justified
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RingAuxiliaryInventory.classify?
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RingAuxiliaryInventory.Assignment.absenceCoverage
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.RingAuxiliaryInventory.arm?
