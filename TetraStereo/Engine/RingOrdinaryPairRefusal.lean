import TetraStereo.Engine.RingActivePairReport
import TetraStereo.Engine.RingReferenceFrame

set_option autoImplicit false

namespace TetraStereo.Engine.RingOrdinaryPairRefusal
open RingActivePairReport (Slot Reader Matrix Ranking)
open RingChemicalPriority ReferenceFrame
open LocalizedChemicalRing.ConstitutionalPartition (pairs pairs_spec)

/-- Diagonal entries contain no source comparison. Every other entry is the
actual signed reading on the chosen geometry. -/
def score {r : Reader} (m : Matrix r) (rev : Bool) (a b : Slot) : Int :=
  if a = b then 0 else if rev then (m.get a b).2 else (m.get a b).1

abbrev ids : List Nat := [0,1,2,3]

/-- Reuse the ordinary molecular promotion test on each geometry separately. -/
def table {r : Reader} (m : Matrix r) (rev : Bool) : Table :=
  (List.finRange 4).flatMap fun a => (List.finRange 4).map fun b =>
    let ord := compare (score m rev a b) 0
    ((a.val,b.val),(ord,ord))

theorem read_table {r : Reader} (m : Matrix r) (rev : Bool) (a b : Slot) :
    orderAt (table m rev) false a.val b.val = some (compare (score m rev a b) 0) := by
  fin_cases a <;> fin_cases b <;> rfl

/-- The ordinary two-plus-one-plus-one partition of this matrix. Its same unique
tie must occur in both directed comparisons, on both geometries. All strict
comparisons together must pass the reciprocal and transitive preorder checks. -/
def Valid {r : Reader} (m : Matrix r) (a b : Slot) : Prop :=
  ∀ rev : Bool, coherent ids (table m rev) false = true ∧
    marks ids (table m rev) = [a.val,b.val] ∧
    ∀ x y : Slot, x ≠ y → (score m rev x y = 0 ↔ (x = a ∧ y = b) ∨ (x = b ∧ y = a))

instance {r m a b} : Decidable (@Valid r m a b) := by unfold Valid; infer_instance

structure Certificate {r : Reader} (m : Matrix r) where
  a : Slot
  b : Slot
  ordered : a < b
  partition : Valid m a b

def find? {r : Reader} (m : Matrix r) : Option (Certificate m) :=
  let ok := fun p : Slot × Slot => decide (Valid m p.1 p.2)
  (pairs.find? ok).attach.map fun p =>
    ⟨p.val.1,p.val.2,(pairs_spec p.val).mp (List.mem_of_find?_eq_some p.property),
      of_decide_eq_true (List.find?_some (p := ok) p.property)⟩

theorem find_iff {r : Reader} (m : Matrix r) :
    (find? m).isSome = true ↔ ∃ a b : Slot, a < b ∧ Valid m a b := by
  constructor
  · intro h
    let c := (find? m).get h
    exact ⟨c.a,c.b,c.ordered,c.partition⟩
  · rintro ⟨a,b,ordered,valid⟩
    simp only [find?,Option.isSome_map,Option.isSome_attach]
    exact List.find?_isSome.mpr ⟨(a,b),(pairs_spec _).mpr ordered,decide_eq_true valid⟩

theorem Certificate.no_ranking {r m} (c : @Certificate r m) (rev : Bool) :
    ¬Nonempty (Ranking m rev) := by
  rintro ⟨rank⟩
  have ne := ne_of_lt c.ordered
  have left := ((c.partition rev).2.2 c.a c.b ne).mpr (.inl ⟨rfl,rfl⟩)
  have right := ((c.partition rev).2.2 c.b c.a ne.symm).mpr (.inr ⟨rfl,rfl⟩)
  have different : rank.slots.idxOf c.a ≠ rank.slots.idxOf c.b :=
    fun h => ne ((List.idxOf_inj (rank.perm.mem_iff.mpr (by simp : c.a ∈ List.finRange 4))).mp h)
  rcases lt_or_gt_of_ne different with ab | ba
  · have pos := (rank.before_iff ne).mp ab
    change 0 < (if rev then (m.get c.a c.b).2 else (m.get c.a c.b).1) at pos
    simp only [score,if_neg ne] at left
    omega
  · have pos := (rank.before_iff ne.symm).mp ba
    change 0 < (if rev then (m.get c.b c.a).2 else (m.get c.b c.a).1) at pos
    simp only [score,if_neg ne.symm] at right
    omega

theorem Certificate.no_promotion {r m} (c : @Certificate r m) (rev : Bool) :
    (marks ids (table m rev)).length ∉ [3,4] := by
  rw [(c.partition rev).2.1]
  change (2 : Nat) ∉ [3,4]
  decide

/-- Bind the tie to both directions of the original reader, including the two
signed magnitudes on the two coordinate presentations. -/
theorem Certificate.tied_source {r m} (c : @Certificate r m) :
    r c.a c.b = some (0,0) ∧ r c.b c.a = some (0,0) := by
  have ne := ne_of_lt c.ordered
  have raw {x y : Slot} (xy : x ≠ y) (eqn : ∀ rev, score m rev x y = 0) :
      r x y = some (0,0) := by
    rw [m.found x y xy]
    apply congrArg some
    exact Prod.ext (by simpa [score,xy] using eqn false) (by simpa [score,xy] using eqn true)
  exact ⟨raw ne fun rev => ((c.partition rev).2.2 c.a c.b ne).mpr (.inl ⟨rfl,rfl⟩),
    raw ne.symm fun rev => ((c.partition rev).2.2 c.b c.a ne.symm).mpr (.inr ⟨rfl,rfl⟩)⟩

end TetraStereo.Engine.RingOrdinaryPairRefusal
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairRefusal.read_table
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairRefusal.find_iff
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairRefusal.Certificate.no_ranking
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairRefusal.Certificate.no_promotion
assert_kernel_only TetraStereo.Engine.RingOrdinaryPairRefusal.Certificate.tied_source
