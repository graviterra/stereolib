import TetraStereo.Engine.RingGeometryExchange
import TetraStereo.OneCenter.LocalizedRetainedCursorTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingGeometryAutomorphism
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingGeometryExchange (Carrier Marked)
open RingRetainedChemicalTrace (observation?)
open RingActiveDistanceSchedule (frozen distance Visible)
noncomputable section

variable {i : Input} (e : i.certified.moleculeGraph.Aut)
private abbrev perm := (e : Equiv.Perm i.certified.Atom)

private theorem idx_map {α : Type} [DecidableEq α] (s : Equiv.Perm α) (a : α) (xs : List α) :
    (xs.map s).idxOf (s a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : x = a <;> simp [h,ih]

private theorem current_eq {α : Type} [DecidableEq α] (s : Equiv.Perm α) (t : Option α) (a : α) :
    (t.map s == some (s a)) = (t == some a) := by
  cases t with
  | none => rfl
  | some b => by_cases h : b = a <;> simp [h]

/-- The raw molecule and the certified digraph use the same renumbering, including
the isotope spelling used for the mass lookup on a real atom. -/
def Records := ∀ a : i.certified.Atom, i.molecule.atoms[((perm e) a).val]? = i.molecule.atoms[a.val]?

private theorem observation (records : Records e) (q : Arm i) (terminal : Bool) :
    observation? i (i.certified.transportCursor i.single e q) terminal = observation? i q terminal := by
  let s := perm e
  let xs := q.occurrence.val.node.history
  have hist (a : i.certified.Atom) : ((xs.map s).tail.contains (s a)) = xs.tail.contains a := by
    apply Bool.eq_iff_iff.mpr
    simp [← List.map_tail]
  have index (a : i.certified.Atom) : ((xs.map s).tail.reverse.idxOf (s a)) = xs.tail.reverse.idxOf a := by
    rw [← List.map_tail,← List.map_reverse,idx_map]
  have head (a : i.certified.Atom) : ((xs.map s).head? == some (s a)) = (xs.head? == some a) := by
    rw [List.head?_map,current_eq]
  unfold observation?
  simp only [transportCursor_occurrence,transportOccurrence_node,mapOfficialNode]
  cases h : q.occurrence.val.node.current? with
  | none => rfl
  | some a =>
    simp only [Option.map_some,Option.bind_eq_bind,Option.bind_some]
    rw [records a]
    cases prov : q.occurrence.val.node.provenance <;> first | rfl | skip
    dsimp only [xs,s] at head hist index
    simp only [head,hist,index]

/-- A physical graph automorphism supplies the whole child correspondence and
all constitutional observations, for every rooted, directed molecular cursor. -/
def carrier (records : Records e) : Carrier i i where
  image := i.certified.transportCursor i.single e
  domain := i.certified.cursorPreviousRootAligned
  below := fun q _ t ht => i.certified.executableLocalizedRerootChildren_cursorAligned q t ht
  children := fun _ h => i.certified.executableLocalizedRerootChildren_transport_perm i.single e h
  observation := by
    intro q aligned
    have edges := i.certified.executableLocalizedRerootChildren_transport_perm i.single e aligned
    have empty : (i.certified.executableLocalizedRerootChildren (i.certified.transportCursor i.single e q)).isEmpty =
        (i.certified.executableLocalizedRerootChildren q).isEmpty := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.isEmpty_iff]
      have h := edges.length_eq
      simp only [List.length_map] at h
      simp [← List.length_eq_zero_iff,h]
    rw [empty,observation e records]

theorem mark (records : Records e) (a : i.certified.Atom) :
    Marked (carrier e records) a.val ((perm e) a).val := by
  intro q _
  unfold RingGroupedMark.bit
  change _ = (((q.occurrence.val.node.current?.map (perm e)).map Fin.val == some ((perm e) a).val).toNat)
  cases h : q.occurrence.val.node.current? with
  | none => rfl
  | some b =>
    by_cases same : b = a
    · subst b; simp
    · have v : b.val ≠ a.val := fun h => same (Fin.ext h)
      have v' : ((perm e) b).val ≠ ((perm e) a).val := fun h => same ((perm e).injective (Fin.ext h))
      simp only [Option.map_some,Option.some_beq_some,beq_eq_false_iff_ne.mpr v,beq_eq_false_iff_ne.mpr v']

abbrev site (q : Site i) := i.certified.transportOccurrence i.single e q

/-- Visibility in the frozen distance schedule depends on root, depth, and
return to the root. All three are preserved by the molecular renumbering. -/
theorem visible (q t : Site i) : Visible (site e q) (site e t) ↔ Visible q t := by
  have depth (x : Site i) : distance (site e x) = distance x :=
    i.certified.transportOccurrence_address_length i.single e x
  unfold Visible
  simp only [depth,site,transportOccurrence_root,Equiv.apply_eq_iff_eq,transportOccurrence_node,mapOfficialNode]
  cases h : t.val.node.current? <;> simp

theorem frozen_transport {s t : RingActiveDistanceSchedule.View i} (q u : Site i)
    (earlier : ∀ v, Visible q v → s v = t (site e v)) :
    frozen s q u = frozen t (site e q) (site e u) := by
  have root : (site e u).val.root = (site e q).val.root ↔ u.val.root = q.val.root := (perm e).injective.eq_iff
  by_cases on : u.val.root = q.val.root
  · have mapped := root.mpr on
    by_cases allowed : Visible q u
    · have m := (visible e q u).mpr allowed
      simp only [frozen,if_neg (not_not_intro on),if_neg (not_not_intro mapped),if_pos allowed.2,if_pos m.2,earlier u allowed]
    · have off : ¬(distance q < distance u ∧ u.val.node.current? ≠ some q.val.root) := fun h => allowed ⟨on,h⟩
      have off' : ¬(distance (site e q) < distance (site e u) ∧
          (site e u).val.node.current? ≠ some (site e q).val.root) := fun h => allowed ((visible e q u).mp ⟨mapped,h⟩)
      simp only [frozen,if_neg (not_not_intro on),if_neg (not_not_intro mapped),if_neg off,if_neg off']
  · simp only [frozen,if_pos on,if_pos (mt root.mp on)]

end
end TetraStereo.Engine.RingGeometryAutomorphism
assert_kernel_only TetraStereo.Engine.RingGeometryAutomorphism.carrier
assert_kernel_only TetraStereo.Engine.RingGeometryAutomorphism.mark
assert_kernel_only TetraStereo.Engine.RingGeometryAutomorphism.frozen_transport
