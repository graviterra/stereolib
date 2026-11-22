import TetraStereo.Engine.RingActivePairReport
import TetraStereo.Engine.RingMarkedSilentRefusal
import TetraStereo.Engine.RingCarbonCoverage

set_option autoImplicit false

namespace TetraStereo.Engine.RingActiveCarbonReport
open OneCenter CertifiedLocalizedCIPInput RingChemicalPriority
open LocalizedChemicalRing (Input)

/-- The assignment is attached to the same raw atom, and comes from both
strict geometry-specific rankings at that detected tetrahedral center. -/
structure Active (i : Input) (root : Nat) where
  center : i.certified.TetrahedralCenter
  atom : center.val.val = root
  assignment : RingActivePairReport.Assignment i center
  found : RingActivePairReport.assign? i center = some assignment

def active? (i : Input) (root : Nat) : Option (Active i root) :=
  i.certified.canonicalTetrahedralCenters.findSome? fun c => do
    if h : c.val.val = root then
      let ⟨a,found⟩ ← (RingActivePairReport.assign? i c).attach
      return ⟨c,h,a,found⟩
    none

/-- Report rows distinguish actual two-geometry rankings, marked molecular
refusals, and the earlier evaluator's certificate at the same atom. -/
inductive Row (i : Input) (d root : Nat) where
  | active (a : Active i root)
  | marked (c : RingMarkedSilentRefusal.Certificate i d root)
      (found : RingMarkedSilentRefusal.discover? i d root = some c)
  | previous (c : RingCarbonCoverage.Row i d root) (found : RingCarbonCoverage.carbon? i d root = some c)

def Row.label {i d root} : Row i d root → Option LocalizedAuxiliaryLabel
  | .active a => some a.assignment.label
  | .marked .. => none
  | .previous c _ => c.label

def carbon? (i : Input) (d root : Nat) : Option (Row i d root) := do
  guard ((i.molecule.atoms[root]?).any (fun a => a.element == .C))
  if let some a := active? i root then return .active a
  if let some ⟨c,found⟩ := (RingMarkedSilentRefusal.discover? i d root).attach then return .marked c found
  let ⟨c,found⟩ ← (RingCarbonCoverage.carbon? i d root).attach
  return .previous c found

abbrev Report (i : Input) (d : Nat) := List ((root : Nat) × Row i d root)

def report? (i : Input) (d : Nat) : Option (Report i d) :=
  (RingCarbonReport.carbons i.molecule).mapM fun root => (carbon? i d root).map (Sigma.mk root)

def labels {i d} (r : Report i d) := r.map fun row => (row.1,row.2.label)

theorem report_projection (i : Input) (depth : Nat) :
    (report? i depth).map labels = (RingCarbonReport.carbons i.molecule).mapM
      (fun root => (carbon? i depth root).map (fun row => (root,row.label))) := by
  unfold report?
  generalize RingCarbonReport.carbons i.molecule = roots
  induction roots with
  | nil => rfl
  | cons a as ih =>
    rw [List.mapM_cons,List.mapM_cons]
    cases head : carbon? i depth a <;>
      cases tail : as.mapM (m := Option) (fun root => (carbon? i depth root).map (Sigma.mk root)) <;>
      simp [tail,labels] at ih ⊢ <;> simp [← ih]

theorem active_iff (i : Input) (root : Nat) :
    (active? i root).isSome = true ↔ Nonempty (Active i root) := by
  constructor
  · intro h
    exact ⟨(active? i root).get h⟩
  · rintro ⟨a⟩
    apply List.findSome?_isSome_iff.mpr
    refine ⟨a.center,(i.certified.mem_canonicalTetrahedralCenters_iff a.center).mpr a.center.property,?_⟩
    have att := Option.attach_eq_some _ ⟨a.assignment,a.found⟩
    simp [a.atom,att]

theorem carbon_isSome_iff (i : Input) (d root : Nat) (member : root ∈ RingCarbonReport.carbons i.molecule) :
    (carbon? i d root).isSome = true ↔ Nonempty (Active i root) ∨
      (RingMarkedSilentRefusal.discover? i d root).isSome = true ∨ (RingCarbonCoverage.carbon? i d root).isSome = true := by
  rw [← active_iff]
  have raw := (RingCarbonReport.mem_carbons.mp member).2
  cases a : active? i root with
  | some found => simp [carbon?,raw,a]
  | none =>
    cases m : RingMarkedSilentRefusal.discover? i d root with
    | some c =>
      have att := Option.attach_eq_some _ ⟨c,m⟩
      simp [carbon?,raw,a,att]
    | none =>
      have miss := Option.attach_eq_none_iff.mpr m
      cases p : RingCarbonCoverage.carbon? i d root with
      | none => simp [carbon?,raw,a,miss,Option.attach_eq_none_iff.mpr p]
      | some c =>
        have att := Option.attach_eq_some _ ⟨c,p⟩
        simp [carbon?,raw,a,miss,att]

/-- Coverage of the entire carbon inventory, including mixtures of all
three evidence classes. Failure to produce any row propagates. -/
theorem report_isSome_iff (i : Input) (d : Nat) :
    (report? i d).isSome = true ↔ ∀ root ∈ RingCarbonReport.carbons i.molecule,
      Nonempty (Active i root) ∨ (RingMarkedSilentRefusal.discover? i d root).isSome = true ∨
        (RingCarbonCoverage.carbon? i d root).isSome = true := by
  have total {α β : Type} (f : α → Option β) (xs : List α) :
      (xs.mapM f).isSome = true ↔ ∀ x ∈ xs, (f x).isSome = true := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.mapM_cons,List.forall_mem_cons]
      cases h : f x <;> cases t : xs.mapM f <;> simp_all
  unfold report?
  rw [total]
  apply forall_congr'
  intro root
  apply forall_congr'
  intro mem
  simpa using carbon_isSome_iff i d root mem

theorem inventory {i d r} (found : report? i d = some r) :
    r.map Sigma.fst = RingCarbonReport.carbons i.molecule := by
  have go (xs : List Nat) (rows : Report i d)
      (compiled : xs.mapM (m := Option) (fun j => (carbon? i d j).map (Sigma.mk j)) = some rows) :
      rows.map Sigma.fst = xs := by
    induction xs generalizing rows with
    | nil => simpa using compiled.symm
    | cons j js ih =>
      rw [List.mapM_cons] at compiled
      cases head : carbon? i d j <;>
        cases rest : js.mapM (m := Option) (fun k => (carbon? i d k).map (Sigma.mk k)) <;>
        simp [head,rest] at compiled
      subst rows
      simp [ih _ rest]
  exact go _ _ found

/-- Every displayed atom and label identifies which theorem justifies it.
The previous evaluator's output is retained with its original evidence. -/
theorem evidence {i d} (r : Report i d) {root letter} (listed : (root,letter) ∈ labels r) :
    (∃ a : Active i root, letter = some a.assignment.label) ∨
    (∃ c : RingMarkedSilentRefusal.Certificate i d root, RingMarkedSilentRefusal.discover? i d root = some c ∧
      letter = none ∧ c.pop.consensus? = some none) ∨
    (∃ c : RingCarbonCoverage.Row i d root, RingCarbonCoverage.carbon? i d root = some c ∧ letter = c.label) := by
  obtain ⟨⟨j,row⟩,_,eqn⟩ := List.mem_map.mp listed
  obtain rfl : j = root := congrArg Prod.fst eqn
  have lab := congrArg Prod.snd eqn
  cases row with
  | active a => exact Or.inl ⟨a,lab.symm⟩
  | marked c found => exact Or.inr (Or.inl ⟨c,found,lab.symm,c.refusal⟩)
  | previous c found => exact Or.inr (Or.inr ⟨c,found,lab.symm⟩)

end TetraStereo.Engine.RingActiveCarbonReport

assert_kernel_only TetraStereo.Engine.RingActiveCarbonReport.report_projection
assert_kernel_only TetraStereo.Engine.RingActiveCarbonReport.active_iff
assert_kernel_only TetraStereo.Engine.RingActiveCarbonReport.carbon_isSome_iff
assert_kernel_only TetraStereo.Engine.RingActiveCarbonReport.report_isSome_iff
assert_kernel_only TetraStereo.Engine.RingActiveCarbonReport.inventory
assert_kernel_only TetraStereo.Engine.RingActiveCarbonReport.evidence
