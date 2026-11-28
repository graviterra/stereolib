import TetraStereo.Engine.RingDeepHistoryPathOrder
import TetraStereo.Engine.RingTwoShellPathOrder
import TetraStereo.Engine.RingHistoryObservation
import TetraStereo.Examples.AntipodalCyclohexaneHands

/-! The raw history comparison agrees with every directed incident edge of
every admitted graph, including directions towards the original root. -/
set_option autoImplicit false
namespace TetraStereo.Examples.RingDeepHistoryComparison
open Engine OneCenter CertifiedLocalizedCIPInput
open RingActivePairs (Arm Site)
open LocalizedChemicalRing (Input)
open RingDeepHistoryPathOrder (Edge)
open DecalinAuxiliary (history)
open AntipodalCyclohexaneHands.HistoryPriority (GraphFacts child_histories)
open RingRetainedChemicalPreorder (Direction keyFor)

def edge {i : Input} (q : Arm i) : Edge :=
  (q.previous?.elim [] history,history q.occurrence)

private theorem facts (i : Input) : GraphFacts i.molecule := by
  intro a
  obtain ⟨nd,bd,occ⟩ := RawMolecule.WrittenNeighborExact.at i.molecule i.admissible.2 a
  exact ⟨nd,fun b => ⟨occ b,bd⟩⟩

theorem children_exact {i : Input} (q : Arm i) (p : Site i) (prev : q.previous? = some p)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    ((i.certified.executableLocalizedRerootChildren q).map edge).Perm
      (RingDeepHistoryPathOrder.children i.molecule (edge q)) := by
  have perm := (child_histories (facts i) rfl q p prev valid).map (fun h => (history q.occurrence,h))
  have mapped : (i.certified.executableLocalizedRerootChildren q).map edge =
      ((i.certified.executableLocalizedRerootChildren q).map fun c => history c.occurrence).map
        (fun h => (history q.occurrence,h)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c mem
    simp [edge,i.certified.executableLocalizedRerootChildren_previous q c mem]
  rw [mapped]
  simpa only [edge,prev,Option.elim_some] using perm

private theorem index {n : Nat} (a : Fin n) (xs : List (Fin n)) :
    (xs.map Fin.val).idxOf a.val = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b t ih =>
    by_cases h : b = a
    · subst b; simp
    · have ne : b.val ≠ a.val := fun eq => h (Fin.ext eq)
      simp [h,ne,ih]

private theorem observation {i : Input} (h : List i.certified.Atom) (terminal : Bool) :
    RingDeepHistoryPathOrder.observe? i.molecule (h.map Fin.val) terminal =
      RingHistoryObservation.observeHistory? i h terminal := by
  cases h with
  | nil => rfl
  | cons a t =>
    have mem : a.val ∈ t.map Fin.val ↔ a ∈ t := by
      constructor
      · intro mem
        obtain ⟨b,hb,val⟩ := List.mem_map.mp mem
        exact (Fin.ext val : b = a) ▸ hb
      · exact fun mem => List.mem_map_of_mem mem
    simp only [RingDeepHistoryPathOrder.observe?,RingHistoryObservation.observeHistory?,List.map_cons,
      List.head?_cons,List.tail_cons,Option.bind_eq_bind,Option.bind_some,List.contains_iff_mem,mem,←List.map_reverse,index]

theorem tree_exact {i : Input} (n : Nat) (q : Arm i) (p : Site i)
    (prev : q.previous? = some p) (valid : i.certified.LocalizedRerootCursorValid q) :
    RingDeepHistoryPathOrder.tree i.molecule n (edge q) = RingConstitutionalTreeInvariant.view i n q := by
  induction n generalizing q p with
  | zero => rfl
  | succ n ih =>
    have perm := children_exact q p prev valid
    have terminal : (RingDeepHistoryPathOrder.children i.molecule (edge q)).isEmpty =
        (i.certified.executableLocalizedRerootChildren q).isEmpty := by
      apply Bool.eq_iff_iff.mpr
      have len := perm.length_eq
      simp only [List.length_map] at len
      rw [List.isEmpty_iff_length_eq_zero,List.isEmpty_iff_length_eq_zero,len]
    apply Prod.ext
    · change RingDeepHistoryPathOrder.observe? i.molecule (history q.occurrence) _ = _
      rw [terminal]
      exact (observation q.occurrence.val.node.history _).trans (RingHistoryObservation.observation_exact i q _)
    · apply Quotient.sound
      apply (perm.symm.map (RingDeepHistoryPathOrder.tree i.molecule n)).trans
      rw [List.map_map]
      apply List.Perm.of_eq
      apply List.map_congr_left
      intro c hc
      exact ih c q.occurrence (i.certified.executableLocalizedRerootChildren_previous q c hc)
        (i.certified.localizedRerootChild_valid q c _ (i.certified.executableLocalizedRerootChildren_declarative q) hc)

theorem direction_key {i : Input} {p : Site i} (a : Direction i p) :
    RingDeepHistoryPathOrder.key? i.molecule (history p) (history a.val) = some (keyFor a) := by
  have bound := i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1
  have valid : i.certified.LocalizedRerootCursorValid (⟨a.val,some p⟩ : Arm i) :=
    (i.certified.mem_localizedRerootNeighborFrames_iff p.val a.val.val).mpr ⟨a.val.property,a.property⟩
  have eqn := tree_exact (RingLigandTreeComparison.depth i) _ p rfl valid
  unfold RingDeepHistoryPathOrder.key?
  rw [←bound]
  exact (congrArg (RingLigandTreeComparison.reconstruct _) eqn).trans (RingLigandTreeComparison.reconstruct_direction a)

theorem key_exact {i : Input} (q : Arm i) (p : Site i) (prev : q.previous? = some p)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    RingDeepHistoryPathOrder.key? i.molecule (edge q).1 (edge q).2 = RingRetainedChemicalTrace.key? i q := by
  obtain ⟨a,old⟩ := q
  cases prev
  let d : Direction i p := ⟨a,((i.certified.mem_localizedRerootNeighborFrames_iff p.val a.val).mp valid).2⟩
  exact (direction_key d).trans (RingRetainedChemicalPreorder.read_key d).symm

theorem compare_exact {i : Input} {p : Site i} (a b : Direction i p) :
    RingDeepHistoryPathOrder.compare? i.molecule (history p,history a.val) (history p,history b.val) =
      RingRetainedChemicalPreorder.compareIn? (RingRetainedChemicalPreorder.table i p) a b := by
  simp [RingDeepHistoryPathOrder.compare?,direction_key,RingRetainedChemicalPreorder.table_order,
    RingRetainedChemicalPreorder.compare_word]

open private rank_prefix append_lt_of_fixed from TetraStereo.Engine.RingTwoShellPathOrder
open RingRetainedReferenceGroup (Path)
open RingFullPathPairs (stepKey)

/-- A strict raw constitutional comparison decides the first differing edge of
two signed paths. Earlier edges agree; later refinements, hands and tails are free. -/
theorem path_lt {i : Input} {p : Site i} (a b : Direction i p)
    (order : RingDeepHistoryPathOrder.compare? i.molecule (history p,history a.val)
      (history p,history b.val) = some .lt)
    {r t : RingNestedActivePair.Reader i} {rev mir : Bool}
    {sa sb : List RingRetainedStereoRefinement.Observation} {x y : RingStereoSiblingPass.Branch}
    (left : RingRetainedStereoRefinement.priority i r rev sa ⟨a.val,some p⟩ = some x)
    (right : RingRetainedStereoRefinement.priority i t mir sb ⟨b.val,some p⟩ = some y)
    (head tailA tailB : Path) (bitA bitB : Option Bool) :
    head ++ stepKey x.deep bitA :: tailA < head ++ stepKey y.deep bitB :: tailB := by
  rw [compare_exact,RingRetainedChemicalPreorder.table_order] at order
  have less := (RingFullPathConstitution.word_lt ..).mp (Option.some.inj order)
  obtain ⟨u,hu⟩ := rank_prefix a sa (RingRetainedStereoRefinement.source _ _ left)
  obtain ⟨v,hv⟩ := rank_prefix b sb (RingRetainedStereoRefinement.source _ _ right)
  have step : stepKey x.deep bitA < stepKey y.deep bitB := by
    simp only [stepKey,hu,hv,List.append_assoc]
    exact append_lt_of_fixed (a := RingRetainedChemicalPreorder.orderWord (keyFor a))
      (b := RingRetainedChemicalPreorder.orderWord (keyFor b)) rfl less _ _
  induction head with
  | nil => exact List.cons_lt_cons_iff.mpr (.inl step)
  | cons _ _ ih => exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,ih⟩)

end TetraStereo.Examples.RingDeepHistoryComparison

assert_kernel_only TetraStereo.Examples.RingDeepHistoryComparison.children_exact
assert_kernel_only TetraStereo.Examples.RingDeepHistoryComparison.tree_exact
assert_kernel_only TetraStereo.Examples.RingDeepHistoryComparison.key_exact
assert_kernel_only TetraStereo.Examples.RingDeepHistoryComparison.compare_exact
assert_kernel_only TetraStereo.Examples.RingDeepHistoryComparison.path_lt
