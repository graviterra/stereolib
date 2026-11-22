import TetraStereo.Engine.RingHomogeneousPairPopulation
import TetraStereo.Engine.RingClosedGroupRecognition

set_option autoImplicit false

namespace TetraStereo.Engine.RingFrozenWordDiagnosis
open OneCenter LocalizedChemicalRing RingActivePairs
open RingNestedActivePair (Reader masked Eligible)
open RingClosedPairGroup (FIFO projected word)
open RingFIFOAlternatives (ChemicalWalk)
open RingRetainedChemicalPreorder (Direction)

/-- Cells are taken from the molecular table at the actual focus. The mask
limits publication to the original digraph and the appropriate distance. -/
def reader {i : Input} (f : Site i) : Reader i :=
  masked f (RingActiveDistanceSchedule.snapshot (RingClosedGroupTie.publicationTable i f.val.root))

theorem read_published {i : Input} {f t : Site i} (eligible : Eligible f t) :
    reader f t = RingClosedGroupTie.atRoot i f.val.root t := by
  simp [reader,RingClosedGroupTie.table_readback,masked,eligible,eligible.1]

theorem derived {i : Input} {f t : Site i} (eligible : Eligible f t) {v} (known : reader f t = some v) :
    RingClosedGroupTie.Derivation i t v :=
  RingClosedGroupTie.derivation t eligible.1 ((read_published eligible).symm.trans known)

private theorem rooted {i : Input} {order : Arm i → List (Arm i) → Prop} {qs xs} {root : i.certified.Atom}
    (w : FIFO i order qs xs) (on : ∀ q ∈ qs, q.occurrence.val.root = root) :
    ∀ q ∈ xs, q.occurrence.val.root = root := by
  induction w with
  | stop => exact on
  | @step a rest row out perm _ next ih =>
    have later : ∀ q ∈ rest ++ row, q.occurrence.val.root = root := by
      intro q member
      rcases List.mem_append.mp member with pending | inRow
      · exact on q (List.mem_cons_of_mem _ pending)
      · have child := List.mem_of_mem_filter (perm.mem_iff.mp inRow)
        have frame := i.certified.executableLocalizedRerootChildren_declarative a
        have intended := List.mem_map_of_mem (f := fun c : Arm i => c.occurrence.val) child
        simp only [RingClosedPairGroup.children,frame.1] at intended
        have near := i.certified.mem_localizedRerootNeighborFrames_of_mem_intended a _ intended
        exact ((i.certified.mem_localizedRerootNeighborFrames_iff _ _).mp near).2.1.trans (on a List.mem_cons_self)
    exact List.forall_mem_cons.mpr ⟨on a List.mem_cons_self,ih later⟩

private theorem permitted {i : Input} :
    (fun q row => RingFIFOAlternatives.chemicalPermit i q row = true) =
      RingSeededFIFOTransport.Admissible (RingSeededFIFOTransport.chemicalKey i) :=
  funext fun q => funext fun row => propext (RingFIFOAlternatives.chemical_permitted q row)

private def walks {i : Input} (q : Arm i) :=
  RingFIFOAlternatives.outcomes (RingFIFOAlternatives.chemicalPermit i) id q

private theorem mem_walks {i : Input} {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q)
    (xs : List (Arm i)) : xs ∈ walks q ↔ ChemicalWalk i q xs := by
  simpa only [walks,permitted,id_eq,exists_eq_right] using
    RingFIFOAlternatives.outcome_iff (RingFIFOAlternatives.chemicalPermit i) id valid xs

/-- Each alternative carries its addressed molecular evidence. In particular,
a missing publication is required by every permissible walk on this arm. -/
inductive Result {i : Input} (f : Site i) (q : Arm i) (rev : Bool) (seed : RS) where
  | missing (t : Arm i) (eligible : Eligible f t.occurrence)
      (unpublished : RingClosedGroupTie.atRoot i f.val.root t.occurrence = none)
      (required : ∀ xs, ChemicalWalk i q xs → t ∈ xs)
  | fixed (bits : RingChemicalPriority.PairSpheres.Word) (one : List (Arm i))
      (realized : ChemicalWalk i q one)
      (all : ∀ xs, ChemicalWalk i q xs →
        (∀ t ∈ xs, (reader f t.occurrence).isSome = true) ∧ word (reader f) rev seed xs = bits)
  | conflict (xs ys : List (Arm i)) (left : ChemicalWalk i q xs) (right : ChemicalWalk i q ys)
      (known : ∀ zs, ChemicalWalk i q zs → ∀ t ∈ zs, (reader f t.occurrence).isSome = true)
      (different : word (reader f) rev seed xs ≠ word (reader f) rev seed ys)

/-- Total diagnosis at an actual incident direction. Enumerating legal refinements
is intended for a focused comparison. The words do not assume a Java discovery order. -/
def diagnose {i : Input} (f : Site i) (a : Direction i f) (rev : Bool) (seed : RS) :
    Result f ⟨a.val,some f⟩ rev seed := by
  let q : Arm i := ⟨a.val,some f⟩
  have valid : i.certified.LocalizedRerootCursorValid q :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨a.val.property,a.property⟩
  let read := reader f
  let observe := word read rev seed
  match inventory : walks q with
  | [] =>
    apply False.elim
    obtain ⟨xs,hx⟩ := RingSeededFIFOTransport.walk_exists (RingSeededFIFOTransport.chemicalKey i) [q]
      (fun t ht => (List.mem_singleton.mp ht) ▸ valid)
    have mem := (mem_walks valid xs).mpr hx
    rw [inventory] at mem
    exact List.not_mem_nil mem
  | first :: rest =>
    have one : ChemicalWalk i q first := (mem_walks valid _).mp (inventory ▸ List.mem_cons_self)
    match miss : first.find? (fun t => (read t.occurrence).isNone) with
    | some t =>
      have ht := List.mem_of_find?_eq_some miss
      have bad : read t.occurrence = none := Option.isNone_iff_eq_none.mp (List.find?_some (p := fun z : Arm i => (read z.occurrence).isNone) miss)
      have same := rooted one (root := f.val.root) (by simpa [q] using a.property.1) t ht
      have eligible : Eligible f t.occurrence := by
        by_contra no
        simp [read,reader,masked,same,no] at bad
      exact .missing t eligible ((read_published eligible).symm.trans bad) (fun ys hy =>
        (RingFIFOPopulation.visits_perm (List.Perm.refl [q]) one hy).mem_iff.mp ht)
    | none =>
      have knownOne : ∀ t ∈ first, (read t.occurrence).isSome = true := by
        intro t ht
        have h := List.find?_eq_none.mp miss t ht
        cases cell : read t.occurrence <;> simp_all
      have known := fun ys (hy : ChemicalWalk i q ys) => RingHomogeneousPairPopulation.known_all read one hy knownOne
      match clash : rest.find? (fun ys => decide (observe ys ≠ observe first)) with
      | some ys =>
        have hy := List.mem_of_find?_eq_some clash
        exact .conflict ys first ((mem_walks valid _).mp (inventory ▸ List.mem_cons_of_mem _ hy)) one known
          (of_decide_eq_true (List.find?_some (p := fun zs => decide (observe zs ≠ observe first)) clash))
      | none =>
        refine .fixed (observe first) first one (fun ys hy => ⟨known ys hy,?_⟩)
        have mem := (mem_walks valid ys).mpr hy
        rw [inventory] at mem
        rcases List.mem_cons.mp mem with rfl | tail
        · rfl
        · simpa only [decide_eq_true_eq,not_not] using List.find?_eq_none.mp clash ys tail

end TetraStereo.Engine.RingFrozenWordDiagnosis
assert_kernel_only TetraStereo.Engine.RingFrozenWordDiagnosis.derived
assert_kernel_only TetraStereo.Engine.RingFrozenWordDiagnosis.diagnose
