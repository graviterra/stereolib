import TetraStereo.Engine.RingAuxiliaryInventory
import TetraStereo.OneCenter.ProductionCIPRule1aGraphRealization

set_option autoImplicit false

namespace TetraStereo.Engine.RingCarbonReport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive Promotion

/-- Every target is a real input atom, in its original index order. -/
def carbons (m : RawMolecule) := (List.range m.atomCount).filter fun i =>
  (m.atoms[i]?).any (fun a => a.element == .C)

theorem mem_carbons {m i} : i ∈ carbons m ↔
    i < m.atomCount ∧ (m.atoms[i]?).any (fun a => a.element == .C) = true := by
  simp only [carbons,List.mem_filter,List.mem_range]

/-- A real, terminal incident hydrogen with its exact atom specification
and source-backed constitutional observation at the fresh root. -/
structure Hydrogen (m : RawMolecule) (i : Nat) (focus : RawMolecule.CanonicalBranchNode) where
  cursor : CanonicalRerootCursor
  incident : cursor ∈ occurrenceLigandCursors m focus
  incoming : cursor.previous? = some focus
  address : cursor.node.history.reverse = [i,cursor.node.atom]
  real : cursor.node.provenance = .realAtom
  leaf : cursor.children m = []
  spec : AtomSpec
  atom : m.atoms[cursor.node.atom]? = some spec
  hydrogen : spec.element = .H
  inBounds : cursor.node.atom < m.atomCount
  attached : m.bondOrder cursor.node.atom i = 1
  onlyRoot : ∀ b ∈ m.bonds, (b.source = cursor.node.atom → b.target = i) ∧
    (b.target = cursor.node.atom → b.source = i)
  observation : IsotopePriority.FullObservation
  source : IsotopePriority.fullObservation? m [i] cursor = some observation

private def hydrogen? {m i focus}
    (member : {c : CanonicalRerootCursor // c ∈ occurrenceLigandCursors m focus}) :
    Option (Hydrogen m i focus) := do
  let c := member.val
  let ⟨a,ha⟩ ← (m.atoms[c.node.atom]?).attach
  if element : a.element = .H then
    if valid : c.previous? = some focus ∧ c.node.history.reverse = [i,c.node.atom] ∧
        c.node.provenance = .realAtom ∧ c.children m = [] then
      if bound : c.node.atom < m.atomCount ∧ m.bondOrder c.node.atom i = 1 then
        if onlyRoot : ∀ b ∈ m.bonds, (b.source = c.node.atom → b.target = i) ∧
            (b.target = c.node.atom → b.source = i) then
          let ⟨o,source⟩ ← (IsotopePriority.fullObservation? m [i] c).attach
          return ⟨c,member.property,valid.1,valid.2.1,valid.2.2.1,valid.2.2.2,a,ha,element,
            bound.1,bound.2,onlyRoot,o,source⟩
  none

def Hydrogen.index {m i n} (c : Hydrogen m i n) : Fin m.atomCount := ⟨c.cursor.node.atom,c.inBounds⟩

theorem Hydrogen.bond_profile {m i n} (h : Hydrogen m i n) (j : Nat) :
    m.bondOrder h.cursor.node.atom j = if j = i then 1 else 0 := by
  by_cases root : j = i
  · simpa [root] using h.attached
  rw [if_neg root]
  by_cases self : h.cursor.node.atom = j
  · rw [self,m.bondOrder_self]
  by_contra nz
  obtain ⟨b,hb,connect⟩ := (m.bondOrder_pos_iff_exists_bond self).mp (Nat.pos_of_ne_zero nz)
  have ends : (b.source = h.cursor.node.atom ∧ b.target = j) ∨
      (b.source = j ∧ b.target = h.cursor.node.atom) := by simpa [RawBond.connects] using connect
  rcases ends with ⟨s,t⟩ | ⟨s,t⟩
  · exact root (t.symm.trans ((h.onlyRoot b hb).1 s))
  · exact root (s.symm.trans ((h.onlyRoot b hb).2 t))

structure HydrogenPair (m : RawMolecule) (i : Nat) where
  focus : RawMolecule.CanonicalBranchNode
  reached : occurrence? m [i] = some focus
  carbon : (m.atoms[i]?).any (fun a => a.element == .C) = true
  four : (occurrenceLigandCursors m focus).length = 4
  distinct : ((occurrenceLigandCursors m focus).map (·.node.atom)).Nodup
  left : Hydrogen m i focus
  right : Hydrogen m i focus
  different : left.cursor.node.atom ≠ right.cursor.node.atom
  identical : left.spec = right.spec
  equalObservation : left.observation = right.observation
  graphLabels : m.toMoleculeGraph.atomZ left.index = m.toMoleculeGraph.atomZ right.index ∧
    m.toMoleculeGraph.atomMass left.index = m.toMoleculeGraph.atomMass right.index ∧
    m.toMoleculeGraph.formalCharge left.index = m.toMoleculeGraph.formalCharge right.index

def hydrogens? (m : RawMolecule) (i : Nat) : Option (HydrogenPair m i) := do
  if carbon : (m.atoms[i]?).any (fun a => a.element == .C) = true then
    let ⟨n,reached⟩ ← (occurrence? m [i]).attach
    let cs := occurrenceLigandCursors m n
    if four : cs.length = 4 ∧ (cs.map (·.node.atom)).Nodup then
      let hs := cs.attach.filterMap (hydrogen? (m := m) (i := i) (focus := n))
      return ← hs.findSome? fun a => hs.findSome? fun b =>
        if h : a.cursor.node.atom ≠ b.cursor.node.atom ∧ a.spec = b.spec ∧ a.observation = b.observation then
          if lab : m.toMoleculeGraph.atomZ a.index = m.toMoleculeGraph.atomZ b.index ∧
              m.toMoleculeGraph.atomMass a.index = m.toMoleculeGraph.atomMass b.index ∧
              m.toMoleculeGraph.formalCharge a.index = m.toMoleculeGraph.formalCharge b.index then
            some ⟨n,reached,carbon,four.1,four.2,a,b,h.1,h.2.1,h.2.2,lab⟩
          else none
        else none
  none

private theorem swap_value {α β : Type} [DecidableEq α] {a b : α} (f : α → β) (h : f a = f b)
    (x : α) : f (Equiv.swap a b x) = f x := by
  by_cases ha : x = a
  · subst x
    simpa only [Equiv.swap_apply_left] using h.symm
  by_cases hb : x = b
  · subst x
    simpa only [Equiv.swap_apply_right] using h
  rw [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Swapping just these two atoms is an automorphism of the whole molecular
graph. Only the stored bonds incident to the selected hydrogens enter its
certificate. The conclusion preserves the bond between every pair of atoms. -/
theorem HydrogenPair.swap_automorphism {m i} (h : HydrogenPair m i) :
    Equiv.swap h.left.index h.right.index ∈ m.toMoleculeGraph.Aut := by
  refine ⟨swap_value _ h.graphLabels.1,swap_value _ h.graphLabels.2.1,
    swap_value _ h.graphLabels.2.2,?_⟩
  have rows (v : Fin m.atomCount) : m.toMoleculeGraph.bond h.left.index v =
      m.toMoleculeGraph.bond h.right.index v :=
    (h.left.bond_profile v.val).trans (h.right.bond_profile v.val).symm
  intro u v
  let swapped := Equiv.swap h.left.index h.right.index
  have first := swap_value (fun x => m.toMoleculeGraph.bond x (swapped v)) (rows (swapped v)) u
  have columns : m.toMoleculeGraph.bond u h.left.index = m.toMoleculeGraph.bond u h.right.index :=
    (m.toMoleculeGraph.bond_symm _ _).trans ((rows u).trans (m.toMoleculeGraph.bond_symm _ _))
  exact first.trans (swap_value (m.toMoleculeGraph.bond u) columns v)

theorem HydrogenPair.swap_atom_spec {m i} (h : HydrogenPair m i) (v : Fin m.atomCount) :
    m.atoms[(Equiv.swap h.left.index h.right.index v).val]? = m.atoms[v.val]? :=
  swap_value (fun a : Fin m.atomCount => m.atoms[a.val]?)
    (h.left.atom.trans ((congrArg some h.identical).trans h.right.atom.symm)) v

theorem HydrogenPair.swap_fixes_other_atoms {m i} (h : HydrogenPair m i) (v : Fin m.atomCount)
    (left : v ≠ h.left.index) (right : v ≠ h.right.index) :
    Equiv.swap h.left.index h.right.index v = v := Equiv.swap_apply_of_ne_of_ne left right

theorem HydrogenPair.equal_of_automorphism_invariant {m i} (h : HydrogenPair m i) {α : Type}
    (read : Fin m.atomCount → α)
    (invariant : ∀ e ∈ m.toMoleculeGraph.Aut, ∀ x, read (e x) = read x) :
    read h.left.index = read h.right.index := by
  simpa only [Equiv.swap_apply_left] using
    (invariant _ h.swap_automorphism h.left.index).symm

/-- The two real hydrogens have no children. Their full constitutional
trees match, including the actual H isotope and pinned mass. -/
theorem HydrogenPair.same_trees {m i} (h : HydrogenPair m i) :
    IsotopePriority.TreesMatch m (IsotopePriority.fullObservation? m [i]) (IsotopePriority.budget m+1)
      h.left.cursor h.right.cursor := by
  refine ⟨h.left.observation,h.left.source,h.right.source.trans (congrArg some h.equalObservation.symm),
    [],?_,?_⟩
  · simpa only [h.right.leaf] using (List.Perm.refl ([] : List CanonicalRerootCursor))
  · rw [h.left.leaf]
    exact .nil

theorem HydrogenPair.equal_readers {m i} (h : HydrogenPair m i) {α : Type}
    (reader : Nat → CanonicalRerootCursor → α)
    (combine : IsotopePriority.FullObservation → List α → α)
    (atNode : ∀ n c o, IsotopePriority.fullObservation? m [i] c = some o →
      reader (n+1) c = combine o ((c.children m).map (reader n)))
    (symmetric : ∀ o {xs ys : List α}, xs.Perm ys → combine o xs = combine o ys) :
    reader (IsotopePriority.budget m+1) h.left.cursor =
      reader (IsotopePriority.budget m+1) h.right.cursor :=
  h.same_trees.observer_eq reader combine atNode symmetric

/-- Every ordering of the four incident ligands includes both indistinguishable
hydrogens. A priority that assigns them the same value cannot rank it strictly. -/
theorem HydrogenPair.no_strict_permutation {m i} (h : HydrogenPair m i) {α : Type} [Preorder α]
    (rank : CanonicalRerootCursor → α) (invariant : rank h.left.cursor = rank h.right.cursor)
    (order : List CanonicalRerootCursor) (perm : order.Perm (occurrenceLigandCursors m h.focus)) :
    ¬ order.Pairwise (fun a b => rank b < rank a) := by
  intro strict
  have noDup : (order.map rank).Nodup := List.pairwise_map.mpr (strict.imp fun lt => ne_of_gt lt)
  have same := List.inj_on_of_nodup_map ((perm.map rank).nodup_iff.mp noDup)
    h.left.incident h.right.incident invariant
  exact h.different (congrArg (fun c : CanonicalRerootCursor => c.node.atom) same)

inductive Absence (m : RawMolecule) (g : Geometry) (i : Nat) where
  | hydrogens : HydrogenPair m i → Absence m g i
  | single : SinglePairAbsence m g [i] → Absence m g i
  | nested : RingAuxiliaryInventory.NestedAbsence m g [i] → Absence m g i
  | promotionTie : RingAuxiliaryInventory.PromotionAbsence m g [i] → Absence m g i

inductive Verdict (m : RawMolecule) (g : Geometry) (i : Nat) where
  | assigned (reading : Reading) : Justified m g [i] reading → Verdict m g i
  | absent : Absence m g i → Verdict m g i

def Verdict.reading {m g i} : Verdict m g i → Option Reading
  | .assigned r _ => some r
  | .absent _ => none

def Verdict.label {m g i} (v : Verdict m g i) : Option LocalizedAuxiliaryLabel :=
  v.reading.bind Reading.label

private def fromResult {m g i} : RingAuxiliaryInventory.Result m g [i] → Verdict m g i
  | .assigned r h => .assigned r h
  | .compared c => .assigned c.reading c.justified
  | .signed c => .assigned c.reading c.justified
  | .discovered c => .assigned c.reading c.justified
  | .paired c => .assigned c.reading c.justified
  | .signedPaired c => .assigned c.reading c.justified
  | .absent c => .absent (.single c)
  | .nested c => .absent (.nested c)
  | .promotionTie c => .absent (.promotionTie c)

/-- Evaluate this carbon as a fresh root. A missing result means the
molecular search or coordinate reading did not furnish a verdict. -/
private def atAdmitted? (m : RawMolecule) (g : Geometry) (fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) (i : Nat) :
    Option (Verdict m g i) := do
  guard ((m.atoms[i]?).any fun a => a.element == .C)
  if let some hs := hydrogens? m i then return .absent (.hydrogens hs)
  return fromResult (← RingAuxiliaryInventory.classify? m g hint radius fuel [i])

def atCarbon? (m : RawMolecule) (g : Geometry) (fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) (i : Nat) :
    Option (Verdict m g i) :=
  if saturatedWithHalogens m = true then atAdmitted? m g fuel hint radius i else none

private theorem fromResult_label {m g i} (r : RingAuxiliaryInventory.Result m g [i]) :
    (fromResult r).label = r.reading.bind Reading.label := by
  cases r <;> rfl

theorem atCarbon?_label_of_no_hydrogens {m g fuel hint radius i}
    (domain : saturatedWithHalogens m = true)
    (carbon : (m.atoms[i]?).any (fun a => a.element == .C) = true)
    (noH : (hydrogens? m i).isNone = true) :
    (atCarbon? m g fuel hint radius i).map Verdict.label =
      (RingAuxiliaryInventory.classify? m g hint radius fuel [i]).map (fun r => r.reading.bind Reading.label) := by
  cases hs : hydrogens? m i with
  | some h => simp [hs] at noH
  | none =>
    cases result : RingAuxiliaryInventory.classify? m g hint radius fuel [i] <;>
      simp [atCarbon?,domain,atAdmitted?,carbon,guard,hs,result,fromResult_label]

theorem atCarbon?_label_of_hydrogens {m g fuel hint radius i}
    (domain : saturatedWithHalogens m = true)
    (carbon : (m.atoms[i]?).any (fun a => a.element == .C) = true)
    (hasH : (hydrogens? m i).isSome = true) :
    (atCarbon? m g fuel hint radius i).map Verdict.label = some none := by
  cases hs : hydrogens? m i with
  | none => simp [hs] at hasH
  | some h => simp [atCarbon?,domain,atAdmitted?,carbon,guard,hs,Verdict.label,Verdict.reading]

structure Row (m : RawMolecule) (g : Geometry) where
  atom : Nat
  value : Verdict m g atom

structure Report (m : RawMolecule) (g : Geometry) where
  domain : saturatedWithHalogens m = true
  rows : List (Row m g)
  complete : rows.map Row.atom = carbons m

def Report.labels {m g} (r : Report m g) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  r.rows.map fun row => (row.atom,row.value.label)

def Report.readings {m g} (r : Report m g) : List (Nat × Option Reading) :=
  r.rows.map fun row => (row.atom,row.value.reading)

theorem Report.label_atoms {m g} (r : Report m g) : r.labels.map Prod.fst = carbons m := by
  simpa only [labels,List.map_map,Function.comp_def] using r.complete

theorem Report.unique {m g} (r : Report m g) : (r.rows.map Row.atom).Nodup := by
  rw [r.complete]
  exact List.nodup_range.filter _

theorem Report.positive_of_label {m g i h} (r : Report m g) (member : (i,some h) ∈ r.labels) :
    ∃ v, Justified m g [i] v ∧ v.label = some h := by
  obtain ⟨row,_,eqn⟩ := List.mem_map.mp member
  obtain ⟨hi,hl⟩ := Prod.mk.inj eqn
  subst i
  cases hv : row.value with
  | assigned v proof =>
    exact ⟨v,proof,by simpa only [hv,Verdict.label,Verdict.reading,Option.bind_some] using hl⟩
  | absent c => simp [hv,Verdict.label,Verdict.reading] at hl

theorem Report.absence_of_label {m g i} (r : Report m g) (member : (i,none) ∈ r.labels) :
    Nonempty (Absence m g i) := by
  obtain ⟨row,_,eqn⟩ := List.mem_map.mp member
  obtain ⟨hi,hl⟩ := Prod.mk.inj eqn
  subst i
  cases hv : row.value with
  | assigned v proof =>
    rcases v with ⟨a,b⟩
    cases a <;> cases b <;> simp [hv,Verdict.label,Verdict.reading,Reading.label,caseFromMirror?] at hl
  | absent c => exact ⟨c⟩

private def gather {m g} (f : (i : Nat) → Option (Verdict m g i)) :
    (is : List Nat) → Option {rows : List (Row m g) // rows.map Row.atom = is}
  | [] => some ⟨[],rfl⟩
  | i :: is => do
    let v ← f i
    let ⟨rows,cover⟩ ← gather f is
    return ⟨⟨i,v⟩ :: rows,by simp [cover]⟩

private theorem gather_iff {m g} (f : (i : Nat) → Option (Verdict m g i)) (is : List Nat) :
    (gather f is).isSome = true ↔ ∀ i ∈ is, (f i).isSome = true := by
  induction is with
  | nil => simp [gather]
  | cons i is ih =>
    cases h : f i <;> cases t : gather f is <;> simp_all [gather]

private theorem gather_labels {m g} (f : (i : Nat) → Option (Verdict m g i))
    (expected : Nat → Option LocalizedAuxiliaryLabel) (is : List Nat)
    (checked : ∀ i ∈ is, (f i).map Verdict.label = some (expected i)) :
    ∃ rs, gather f is = some rs ∧ rs.val.map (fun row => (row.atom,row.value.label)) =
      is.map (fun i => (i,expected i)) := by
  induction is with
  | nil => exact ⟨⟨[],rfl⟩,rfl,rfl⟩
  | cons i is ih =>
    obtain ⟨v,hv,hl⟩ := Option.map_eq_some_iff.mp (checked i List.mem_cons_self)
    obtain ⟨⟨rows,cover⟩,tail,labels⟩ :=
      ih (fun j hj => checked j (List.mem_cons_of_mem _ hj))
    refine ⟨⟨⟨i,v⟩ :: rows,by simp [cover]⟩,?_,?_⟩
    · simp [gather,hv,tail]
    · change (i,v.label) :: rows.map _ = (i,expected i) :: is.map _
      rw [hl,labels]

end TetraStereo.Engine.RingCarbonReport

namespace TetraStereo.Engine
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation RingChemicalPriority

/-- Complete carbon census for the admitted finite neutral saturated
single-bond domain. Each descriptor is a fresh-root result of the supported
molecular procedure. Every reported absence has its own evidence. An
unresolved carbon makes the entire request return none. -/
def classifyRingCarbons? (m : RawMolecule) (g : Geometry) (fuel : Nat)
    (hint : List Nat → Option Recursive.Frame) (radius : List Nat → Nat) :
    Option (RingCarbonReport.Report m g) := do
  if domain : saturatedWithHalogens m = true then
    let ⟨rows,complete⟩ ← RingCarbonReport.gather
      (RingCarbonReport.atAdmitted? m g fuel hint radius) (RingCarbonReport.carbons m)
    return ⟨domain,rows,complete⟩
  none

/-- Equal occurrence verdicts at the fresh roots give equal complete reports,
including their absence evidence. -/
theorem classifyRingCarbons?_congr_fuel {m g x y hint radius}
    (same : saturatedWithHalogens m = true → ∀ i : Nat,
      RingAuxiliaryInventory.classify? m g hint radius x [i] =
        RingAuxiliaryInventory.classify? m g hint radius y [i]) :
    classifyRingCarbons? m g x hint radius = classifyRingCarbons? m g y hint radius := by
  by_cases ok : saturatedWithHalogens m = true
  · have rows : RingCarbonReport.atAdmitted? m g x hint radius =
        RingCarbonReport.atAdmitted? m g y hint radius := by
      funext i
      simp only [RingCarbonReport.atAdmitted?,same ok i]
    simp only [classifyRingCarbons?,ok,↓reduceDIte,rows]
  · simp [classifyRingCarbons?,ok]

theorem classifyRingCarbons?_isSome {m g fuel hint radius} :
    (classifyRingCarbons? m g fuel hint radius).isSome = true ↔
      saturatedWithHalogens m = true ∧ ∀ i ∈ RingCarbonReport.carbons m,
        (RingCarbonReport.atCarbon? m g fuel hint radius i).isSome = true := by
  by_cases valid : saturatedWithHalogens m = true
  · simp only [classifyRingCarbons?,RingCarbonReport.atCarbon?,valid,↓reduceDIte,↓reduceIte,true_and]
    cases e : RingCarbonReport.gather (RingCarbonReport.atAdmitted? m g fuel hint radius)
        (RingCarbonReport.carbons m) <;> simpa [e] using
          (RingCarbonReport.gather_iff (RingCarbonReport.atAdmitted? m g fuel hint radius)
            (RingCarbonReport.carbons m))
  · simp [classifyRingCarbons?,valid]

/-- Assemble the actual report projection from independent kernel proofs of
every fresh-root label, preserving the carbon census and its order. -/
theorem classifyRingCarbons?_labels_of_rows {m g fuel hint radius}
    (expected : Nat → Option LocalizedAuxiliaryLabel) (domain : saturatedWithHalogens m = true)
    (checked : ∀ i ∈ RingCarbonReport.carbons m,
      (RingCarbonReport.atCarbon? m g fuel hint radius i).map RingCarbonReport.Verdict.label =
        some (expected i)) :
    (classifyRingCarbons? m g fuel hint radius).map RingCarbonReport.Report.labels =
      some ((RingCarbonReport.carbons m).map fun i => (i,expected i)) := by
  obtain ⟨⟨rows,cover⟩,gathered,labels⟩ := RingCarbonReport.gather_labels
    (RingCarbonReport.atAdmitted? m g fuel hint radius) expected (RingCarbonReport.carbons m)
    (fun i member => by simpa only [RingCarbonReport.atCarbon?,if_pos domain] using checked i member)
  simpa [classifyRingCarbons?,domain,gathered,RingCarbonReport.Report.labels] using congrArg some labels

/-- Discover each molecular frame and its first applicable stereochemical
rule from the molecule. The two numeric parameters bound recursion and the
initial atomic-number comparison. -/
def classifyDiscoveredRingCarbons? (m : RawMolecule) (g : Geometry) (fuel depth : Nat) :=
  classifyRingCarbons? m g fuel (fun _ => none) (fun _ => depth)

end TetraStereo.Engine

assert_kernel_only TetraStereo.Engine.classifyRingCarbons?
assert_kernel_only TetraStereo.Engine.classifyRingCarbons?_isSome
assert_kernel_only TetraStereo.Engine.classifyRingCarbons?_labels_of_rows
assert_kernel_only TetraStereo.Engine.RingCarbonReport.atCarbon?_label_of_no_hydrogens
assert_kernel_only TetraStereo.Engine.RingCarbonReport.atCarbon?_label_of_hydrogens
assert_kernel_only TetraStereo.Engine.RingCarbonReport.HydrogenPair.same_trees
assert_kernel_only TetraStereo.Engine.RingCarbonReport.HydrogenPair.swap_automorphism
assert_kernel_only TetraStereo.Engine.RingCarbonReport.HydrogenPair.swap_atom_spec
assert_kernel_only TetraStereo.Engine.RingCarbonReport.HydrogenPair.no_strict_permutation
assert_kernel_only TetraStereo.Engine.RingCarbonReport.Report.label_atoms
assert_kernel_only TetraStereo.Engine.RingCarbonReport.Report.positive_of_label
assert_kernel_only TetraStereo.Engine.RingCarbonReport.Report.absence_of_label
assert_kernel_only TetraStereo.Engine.classifyDiscoveredRingCarbons?
