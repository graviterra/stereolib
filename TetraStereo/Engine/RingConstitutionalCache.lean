import TetraStereo.Engine.RingConstitutionalClasses

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.Cached

open OneCenter CertifiedLocalizedCIPInput

/-- Eagerly construct each complete molecular branch key once at this center. -/
private structure Keys (i : CertifiedLocalizedCIPInput) where
  k0 : ExactOfficialRuleMajorKey i.Atom
  k1 : ExactOfficialRuleMajorKey i.Atom
  k2 : ExactOfficialRuleMajorKey i.Atom
  k3 : ExactOfficialRuleMajorKey i.Atom

private def keys (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) : Keys i :=
  ⟨RingStrictConstitution.key i c 0, RingStrictConstitution.key i c 1,
   RingStrictConstitution.key i c 2, RingStrictConstitution.key i c 3⟩

/-- The six oriented upper-triangular entries of the constitutional comparison matrix. -/
structure Comparisons where
  p01 : Ordering
  p02 : Ordering
  p03 : Ordering
  p12 : Ordering
  p13 : Ordering
  p23 : Ordering
  deriving DecidableEq, Repr

private def compareKeys (i : CertifiedLocalizedCIPInput) (k : Keys i) : Comparisons :=
  let compare := fun a b => cipTraceOutcome (ExactOfficialRuleMajorKey.compareTraceObserved
    i.moleculeGraph i.certified.input.molecule.semanticExactOfficialRule1aObservation a b)
  ⟨compare k.k0 k.k1, compare k.k0 k.k2, compare k.k0 k.k3,
   compare k.k1 k.k2, compare k.k1 k.k3, compare k.k2 k.k3⟩

/-- Build the table before collecting ties or sorting. Both operations use the same six values. -/
def comparisons (i : Input) (c : i.certified.TetrahedralCenter) : Comparisons :=
  compareKeys i.certified (keys i.certified c)

def Comparisons.get (t : Comparisons) (a b : Fin 4) : Ordering :=
  match a.val,b.val with
  | 0,1 => t.p01 | 0,2 => t.p02 | 0,3 => t.p03
  | 1,2 => t.p12 | 1,3 => t.p13 | 2,3 => t.p23
  | 1,0 => t.p01.swap | 2,0 => t.p02.swap | 3,0 => t.p03.swap
  | 2,1 => t.p12.swap | 3,1 => t.p13.swap | 3,2 => t.p23.swap
  | _,_ => .eq

private theorem observed (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) (a b : Fin 4) :
    RingStrictConstitution.constitution i c a b = ExactOfficialRuleMajorKey.compare i.moleculeGraph
      (RingStrictConstitution.key i c a) (RingStrictConstitution.key i c b) := by
  unfold RingStrictConstitution.constitution
  rw [ExactOfficialRuleMajorKey.compareTraceObserved_eq_exact _ _ i.executableExactOfficialRule1aObservation_correct,
    ExactOfficialRuleMajorKey.compareTrace_outcome]

theorem get_exact (i : Input) (c : i.certified.TetrahedralCenter) (a b : Fin 4) :
    (comparisons i c).get a b = RingStrictConstitution.constitution i.certified c a b := by
  let ci := i.certified
  letI := ExactOfficialRuleMajorKey.compare_transCmp ci.moleculeGraph
  have diag (x : Fin 4) : Ordering.eq = RingStrictConstitution.constitution ci c x x := by
    rw [observed]
    exact (Std.ReflCmp.compare_self (cmp := ExactOfficialRuleMajorKey.compare ci.moleculeGraph)).symm
  have rev (x y : Fin 4) : (RingStrictConstitution.constitution ci c x y).swap =
      RingStrictConstitution.constitution ci c y x := by
    rw [observed,observed]
    exact Std.OrientedCmp.eq_swap.symm
  fin_cases a <;> fin_cases b <;> first | rfl | apply diag | apply rev

/-- Isolate exactly the comparisons that require rules after 2. -/
def Comparisons.residual (t : Comparisons) : List Pair :=
  pairs.filter fun p => t.get p.1 p.2 == .eq

private theorem get_outcome (i : Input) (c : i.certified.TetrahedralCenter) (p : Pair) :
    (comparisons i c).get p.1 p.2 = (constitutional i c p).outcome := by
  simpa only [get_exact,constitutional_read, Option.map_some, Option.some.injEq] using
    (RingStrictConstitution.constitutional_outcome i.certified c p.1 p.2).symm

theorem residual_exact (i : Input) (c : i.certified.TetrahedralCenter) :
    (comparisons i c).residual = ConstitutionalPartition.residual i c := by
  simp only [Comparisons.residual,ConstitutionalPartition.residual,get_outcome]

/-- Sort the actual canonical ligand slots in descending order using cached outcomes. -/
def Comparisons.order (t : Comparisons) : List (Fin 4) :=
  (List.finRange 4).mergeSort fun a b => (t.get a b).isGE

theorem order_exact (i : Input) (c : i.certified.TetrahedralCenter) :
    (comparisons i c).order = RingStrictConstitution.order i.certified c := by
  simp only [Comparisons.order,RingStrictConstitution.order,get_exact]

def classify (i : Input) (c : i.certified.TetrahedralCenter) : Result :=
  let t := comparisons i c
  match t.residual with
  | p :: ps => .needsStereo (p :: ps)
  | [] => match LocalizedGenericMarkedRecalculation.readback?
      (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
      (RingStrictConstitution.atomIds i.certified c t.order) with
    | some hand => .assigned hand
    | none => .geometryUnavailable

theorem classify_exact (i : Input) (c : i.certified.TetrahedralCenter) :
    classify i c = ConstitutionalPartition.classify i c := by
  cases h : ConstitutionalPartition.residual i c with
  | nil => simp only [classify, ConstitutionalPartition.classify,residual_exact,h,order_exact,
      RingStrictConstitution.assign?, (strict_iff_empty i c).mpr h, if_pos]; rfl
  | cons p ps => simp only [classify, ConstitutionalPartition.classify,residual_exact,h]

/-- Executable cached report over every detected tetrahedral center. -/
def report (i : Input) : List (i.certified.TetrahedralCenter × Result) :=
  i.certified.canonicalTetrahedralCenters.map fun c => (c,classify i c)

/-- Equality includes structural inputs without calibrated coordinates and preserves row order. -/
theorem report_exact (i : Input) : report i = ConstitutionalPartition.report i := by
  simp only [report, ConstitutionalPartition.report, classify_exact]

end TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.Cached

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.Cached.get_exact
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.Cached.residual_exact
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.Cached.order_exact
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.Cached.classify_exact
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ConstitutionalPartition.Cached.report_exact
