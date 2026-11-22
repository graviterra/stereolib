import TetraStereo.Engine.RingActivePairs
import TetraStereo.Engine.RingConstitutionalPartition
import TetraStereo.OneCenter.LocalizedMarkedFrameCalibration

set_option autoImplicit false

namespace TetraStereo.Engine.RingActivePairReport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry inputGeometry_val)

abbrev Slot := Fin 4
abbrev Score := Int × Int
abbrev Reader := Slot → Slot → Option Score

private def four? {α : Type} (f : Slot → Option α) : Option (Slot → α) := do
  let a ← f 0
  let b ← f 1
  let c ← f 2
  let d ← f 3
  return ![a,b,c,d]

private theorem four_at {α : Type} {f : Slot → Option α} {g : Slot → α} (h : four? f = some g) (k : Slot) :
    f k = some (g k) := by
  cases a : f 0 <;> cases b : f 1 <;> cases c : f 2 <;> cases d : f 3 <;> simp [four?,a,b,c,d] at h
  subst g
  fin_cases k <;> assumption

/-- Cache every directed non-self score once. Reverse directions are separately validated by
ranking, so inconsistent signs cannot yield a root label. -/
structure Matrix (read : Reader) where
  get : Slot → Slot → Score
  found : ∀ a b, a ≠ b → read a b = some (get a b)

def matrix? (read : Reader) : Option (Matrix read) := do
  let edge (a b : Slot) := if a = b then some (0,0) else read a b
  let ⟨get,h⟩ ← (four? fun a => four? (edge a)).attach
  return ⟨get,fun a b ab => by simpa [edge,ab] using four_at (four_at h a) b⟩

private def sign (s : Score) (mirror : Bool) : Int := if mirror then s.2 else s.1

def Wins {r} (m : Matrix r) (rev : Bool) (a b : Slot) : Prop :=
  0 < sign (m.get a b) rev ∧ sign (m.get b a) rev < 0

instance {r m rev a b} : Decidable (@Wins r m rev a b) := by unfold Wins; infer_instance

structure Ranking {r} (m : Matrix r) (rev : Bool) where
  slots : List Slot
  perm : slots.Perm (List.finRange 4)
  higher : slots.Pairwise (Wins m rev)

def rank? {r} (m : Matrix r) (rev : Bool) : Option (Ranking m rev) := do
  let valid (p : List Slot) := decide (p.Pairwise (Wins m rev))
  let ⟨slots,h⟩ ← ((List.finRange 4).permutations'.find? valid).attach
  have tested : valid slots = true := List.find?_some h
  return ⟨slots,List.mem_permutations'.mp (List.mem_of_find?_eq_some h),of_decide_eq_true tested⟩

/-- Every strict order is determined by all directed molecular readings. -/
theorem Ranking.source {r m rev} (k : @Ranking r m rev) (a b : Slot) (lt : k.slots.idxOf a < k.slots.idxOf b) :
    ∃ x y : Score, r a b = some x ∧ r b a = some y ∧ 0 < sign x rev ∧ sign y rev < 0 := by
  have aPresent : a ∈ k.slots := k.perm.mem_iff.mpr (by simp)
  have bPresent : b ∈ k.slots := k.perm.mem_iff.mpr (by simp)
  have strict := List.pairwise_iff_getElem.mp k.higher _ _ (List.idxOf_lt_length_of_mem aPresent) (List.idxOf_lt_length_of_mem bPresent) lt
  simp only [List.getElem_idxOf] at strict
  have ne : a ≠ b := by rintro rfl; omega
  exact ⟨_,_,m.found _ _ ne,m.found _ _ ne.symm,strict⟩

private def even (ss : List Slot) := RawMolecule.permutationIsEven (ss.map Fin.val)

/-- Number of unordered ligand pairs whose strict priority changes between the actual
and reflected rankings. -/
def changes (a b : List Slot) := LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
  (fun p => decide (a.idxOf p.1 < a.idxOf p.2) != decide (b.idxOf p.1 < b.idxOf p.2))

private theorem parity {a b : List Slot} (pa : a.Perm (List.finRange 4)) (pb : b.Perm (List.finRange 4)) :
    changes a b % 2 = 0 ↔ even a = even b := by
  have all : ∀ x ∈ (List.finRange 4).permutations', ∀ y ∈ (List.finRange 4).permutations',
      changes x y % 2 = 0 ↔ even x = even y := by decide +kernel
  exact all _ (List.mem_permutations'.mpr pa) _ (List.mem_permutations'.mpr pb)

private def atoms (i : Input) (c : i.certified.TetrahedralCenter) (ss : List Slot) :=
  ss.map fun k => (i.certified.canonicalLigandAtom c k).val

private theorem geometric_order (i : Input) (c : i.certified.TetrahedralCenter) (ss : List Slot)
    (p : ss.Perm (List.finRange 4)) (pt : Slot → CartesianPoint3)
    (coords : ∀ k, inputGeometry i.certified (i.certified.canonicalLigandAtom c k).val = some (pt k)) :
    readback? (inputGeometry i.certified) (atoms i c ss) =
      if even ss then descriptorOfPriorityOrderedPoints? [pt 0,pt 1,pt 2,pt 3] else
        (descriptorOfPriorityOrderedPoints? [pt 0,pt 1,pt 2,pt 3]).map RS.swap := by
  let atom := fun k : Slot => (i.certified.canonicalLigandAtom c k).val
  have lookup (k : Slot) : [atom 0,atom 1,atom 2,atom 3][k.val]? = some (atom k) := by fin_cases k <;> rfl
  have select (xs : List Slot) : atomsAt? [atom 0,atom 1,atom 2,atom 3] (xs.map Fin.val) = some (xs.map atom) := by
    induction xs with
    | nil => rfl
    | cons k xs ih =>
      unfold atomsAt? at ih ⊢
      simp only [List.map_cons,List.mapM_cons,lookup,ih]
      rfl
  have perm : (ss.map Fin.val).Perm [0,1,2,3] := p.map Fin.val
  have read := LocalizedMarkedFrameCalibration.reordered_readback (inputGeometry i.certified) atom pt coords _ perm
  rw [select] at read
  exact read

private theorem higher_at {r m rev} (k : @Ranking r m rev) {a b : Slot} (lt : k.slots.idxOf a < k.slots.idxOf b) : Wins m rev a b := by
  have ma : a ∈ k.slots := k.perm.mem_iff.mpr (by simp)
  have mb : b ∈ k.slots := k.perm.mem_iff.mpr (by simp)
  simpa only [List.getElem_idxOf] using List.pairwise_iff_getElem.mp k.higher _ _
    (List.idxOf_lt_length_of_mem ma) (List.idxOf_lt_length_of_mem mb) lt

theorem Ranking.before_iff {r m rev} (k : @Ranking r m rev) {a b : Slot} (ne : a ≠ b) :
    k.slots.idxOf a < k.slots.idxOf b ↔ 0 < sign (m.get a b) rev := by
  refine ⟨fun h => (higher_at k h).1,?_⟩
  intro pos
  by_contra no
  have distinct : k.slots.idxOf a ≠ k.slots.idxOf b := fun h =>
    ne ((List.idxOf_inj (k.perm.mem_iff.mpr (by simp : a ∈ List.finRange 4))).mp h)
  have back := (higher_at k (lt_of_le_of_ne (not_lt.mp no) distinct.symm)).2
  omega

/-- Count sign reversals in the six computed scores. A retained sign contributes zero;
a reversal on a strict pair contributes one independently of its magnitude. -/
def reversals {r} (m : Matrix r) := LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
  (fun p => decide (0 < (m.get p.1 p.2).1) != decide (0 < (m.get p.1 p.2).2))

theorem changes_eq {r m} (a : @Ranking r m false) (b : Ranking m true) :
    changes a.slots b.slots = reversals m := by
  apply (List.Perm.refl _).countP_congr
  intro p mem
  have ne := ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem)
  simp [a.before_iff ne,b.before_iff ne,sign]

structure Assignment (i : Input) (c : i.certified.TetrahedralCenter) where
  matrix : Matrix (RingActivePairs.rootScore? i c)
  actual : Ranking matrix false
  reflected : Ranking matrix true
  hand : RS
  mirrorHand : RS
  read : readback? (inputGeometry i.certified) (atoms i c actual.slots) = some hand
  mirrorRead : readback? (mirror (inputGeometry i.certified)) (atoms i c reflected.slots) = some mirrorHand

def Assignment.label {i c} (o : Assignment i c) : LocalizedAuxiliaryLabel :=
  if o.mirrorHand = o.hand then .pseudoasymmetric (pseudoRSOfRS o.hand) else .chiral o.hand

def assign? (i : Input) (c : i.certified.TetrahedralCenter) : Option (Assignment i c) := do
  let m ← matrix? (RingActivePairs.rootScore? i c)
  let a ← rank? m false
  let b ← rank? m true
  let ⟨s,hs⟩ ← (readback? (inputGeometry i.certified) (atoms i c a.slots)).attach
  let ⟨t,ht⟩ ← (readback? (mirror (inputGeometry i.certified)) (atoms i c b.slots)).attach
  return ⟨m,a,b,s,t,hs,ht⟩

def label? (i : Input) (c : i.certified.TetrahedralCenter) : Option LocalizedAuxiliaryLabel :=
  (assign? i c).map Assignment.label

/-- The returned label is exactly the physical two-order, two-geometry readback. -/
theorem Assignment.readback {i c} (o : Assignment i c) :
    (RingChemicalPriority.Recursive.geometric (inputGeometry i.certified) (atoms i c o.actual.slots)
      (atoms i c o.reflected.slots)).bind RingChemicalPriority.Recursive.Reading.label = some o.label := by
  simp [RingChemicalPriority.Recursive.geometric,RingChemicalPriority.Recursive.Reading.label,
    caseFromMirror?,o.read,o.mirrorRead,Assignment.label]

/-- The absolute letter is the physical read in actual priority order. An odd number of
sign-reversing molecular pairs makes that letter lowercase. -/
theorem Assignment.casing {i c} (o : Assignment i c) (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    o.label = if reversals o.matrix % 2 = 0 then .chiral o.hand else .pseudoasymmetric (pseudoRSOfRS o.hand) := by
  obtain ⟨pt,points,_,_⟩ := LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated i.certified admit c
  have coords (k : Slot) : inputGeometry i.certified (i.certified.canonicalLigandAtom c k).val = some (pt k) :=
    (inputGeometry_val i.certified _).trans (points k)
  have first := (geometric_order i c _ o.actual.perm pt coords).symm.trans o.read
  have other := o.mirrorRead
  rw [readback_mirror,geometric_order i c _ o.reflected.perm pt coords] at other
  have flip := parity o.actual.perm o.reflected.perm
  rw [changes_eq o.actual o.reflected] at flip
  unfold Assignment.label
  cases ha : even o.actual.slots <;> cases hb : even o.reflected.slots <;>
    cases base : descriptorOfPriorityOrderedPoints? [pt 0,pt 1,pt 2,pt 3] with
    | none => simp [ha,base] at first
    | some s =>
      cases s <;> cases h : o.hand <;> cases hm : o.mirrorHand <;> simp_all [RS.swap]
/-- Number of the six molecular comparisons carrying doubled magnitude. -/
def doubled {r} (m : Matrix r) := LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
  (fun p => (m.get p.1 p.2).1.natAbs == 2)

/-- If the molecular scoring procedure gives magnitude two exactly on the sign-reversing
edges, lowercase is equivalent to odd parity of the doubled scores on all six pairs. -/
theorem Assignment.casing_by_magnitude {i c} (o : Assignment i c) (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (edge : ∀ a b : Slot, a < b → let x := o.matrix.get a b
      (decide (0 < x.1) != decide (0 < x.2)) = (x.1.natAbs == 2)) :
    o.label = if doubled o.matrix % 2 = 0 then .chiral o.hand else .pseudoasymmetric (pseudoRSOfRS o.hand) := by
  have equal : reversals o.matrix = doubled o.matrix := by
    apply (List.Perm.refl _).countP_congr
    intro p mem
    exact edge p.1 p.2 ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem)
  rw [← equal]
  exact o.casing admit

private theorem four_full {α : Type} (f : Slot → Option α) (full : ∀ k, (f k).isSome = true) :
    (four? f).isSome = true := by
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (full 0)
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (full 1)
  obtain ⟨c,hc⟩ := Option.isSome_iff_exists.mp (full 2)
  obtain ⟨d,hd⟩ := Option.isSome_iff_exists.mp (full 3)
  simp [four?,ha,hb,hc,hd]

theorem matrix?_complete (read : Reader) :
    (matrix? read).isSome = true ↔ ∀ a b, a ≠ b → (read a b).isSome = true := by
  constructor
  · intro h a b ne
    obtain ⟨m,_⟩ := Option.isSome_iff_exists.mp h
    rw [m.found a b ne]; rfl
  · intro coverage
    let edge (a b : Slot) : Option Score := if a = b then some (0,0) else read a b
    have cover (a b : Slot) : (edge a b).isSome = true := by by_cases h : a = b <;> simp [edge,h,coverage]
    obtain ⟨m,found⟩ := Option.isSome_iff_exists.mp (four_full _ (fun a => four_full _ (cover a)))
    have seen := Option.attach_eq_some _ ⟨m,found⟩
    change ((four? fun a => four? (edge a)).attach.bind _).isSome = true
    rw [seen]; rfl

private theorem rank_of {r m rev} (w : @Ranking r m rev) : rank? m rev = some w := by
  let valid (ss : List Slot) := decide (ss.Pairwise (Wins m rev))
  have existsOrder : ((List.finRange 4).permutations'.find? valid).isSome :=
    List.find?_isSome.mpr ⟨w.slots,List.mem_permutations'.mpr w.perm,decide_eq_true w.higher⟩
  obtain ⟨ss,found⟩ := Option.isSome_iff_exists.mp existsOrder
  have good : valid ss = true := List.find?_some found
  have perm := List.mem_permutations'.mp (List.mem_of_find?_eq_some found)
  have same : ss = w.slots := List.Perm.eq_of_pairwise
    (fun a b _ _ ab ba => False.elim (not_lt_of_gt ab.1 ba.2)) (of_decide_eq_true good) w.higher (perm.trans w.perm.symm)
  subst ss
  have seen := Option.attach_eq_some _ ⟨w.slots,found⟩
  unfold rank?
  change (((List.finRange 4).permutations'.find? valid).attach.bind _) = _
  rw [seen]; rfl

/-- Missing molecular scores, inconsistent or tied rankings, and failed geometric reads
are the precise obstacles to a row. Any independent valid rankings on the checked score
matrix give the same computed row. -/
theorem assign?_complete (i : Input) (c : i.certified.TetrahedralCenter) :
    (assign? i c).isSome = true ↔ ∃ m : Matrix (RingActivePairs.rootScore? i c), matrix? _ = some m ∧
      ∃ (a : Ranking m false) (b : Ranking m true),
        (readback? (inputGeometry i.certified) (atoms i c a.slots)).isSome = true ∧
        (readback? (mirror (inputGeometry i.certified)) (atoms i c b.slots)).isSome = true := by
  constructor
  · intro h
    obtain ⟨row,found⟩ := Option.isSome_iff_exists.mp h
    cases hm : matrix? (RingActivePairs.rootScore? i c) with
    | none => simp [assign?,hm] at found
    | some m =>
      cases ha : rank? m false with
      | none => simp [assign?,hm,ha] at found
      | some a =>
        cases hb : rank? m true with
        | none => simp [assign?,hm,ha,hb] at found
        | some b =>
          refine ⟨m,rfl,a,b,?_⟩
          cases sa : readback? (inputGeometry i.certified) (atoms i c a.slots) <;>
            cases sb : readback? (mirror (inputGeometry i.certified)) (atoms i c b.slots) <;>
            first | exact ⟨rfl,rfl⟩ | simp [assign?,hm,ha,hb,Option.attach,sa,sb] at found
  · rintro ⟨m,hm,a,b,sa,sb⟩
    obtain ⟨x,left⟩ := Option.isSome_iff_exists.mp sa
    obtain ⟨y,right⟩ := Option.isSome_iff_exists.mp sb
    have l := Option.attach_eq_some _ ⟨x,left⟩
    have r := Option.attach_eq_some _ ⟨y,right⟩
    simp [assign?,hm,rank_of a,rank_of b,l,r]

/-- Enumerate all detected tetrahedral centers and retain unresolved rows explicitly. -/
def report (i : Input) : List (i.certified.TetrahedralCenter × Option LocalizedAuxiliaryLabel) :=
  i.certified.canonicalTetrahedralCenters.map fun c => (c,label? i c)

theorem report_exact (i : Input) (c : i.certified.TetrahedralCenter) (v : Option LocalizedAuxiliaryLabel) :
    (c,v) ∈ report i ↔ label? i c = v := by
  constructor
  · intro h
    obtain ⟨x,_,eqv⟩ := List.mem_map.mp h
    cases eqv
    rfl
  · rintro rfl
    exact List.mem_map.mpr ⟨c,(i.certified.mem_canonicalTetrahedralCenters_iff c).mpr c.2,rfl⟩

end TetraStereo.Engine.RingActivePairReport

assert_kernel_only TetraStereo.Engine.RingActivePairReport.Ranking.source
assert_kernel_only TetraStereo.Engine.RingActivePairReport.changes_eq
assert_kernel_only TetraStereo.Engine.RingActivePairReport.Assignment.readback
assert_kernel_only TetraStereo.Engine.RingActivePairReport.Assignment.casing

assert_kernel_only TetraStereo.Engine.RingActivePairReport.report_exact
assert_kernel_only TetraStereo.Engine.RingActivePairReport.Assignment.casing_by_magnitude
assert_kernel_only TetraStereo.Engine.RingActivePairReport.matrix?_complete
assert_kernel_only TetraStereo.Engine.RingActivePairReport.assign?_complete
