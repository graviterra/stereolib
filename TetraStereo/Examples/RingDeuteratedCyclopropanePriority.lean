import Batteries.Tactic.OpenPrivate
import TetraStereo.Examples.RingDeuteratedCyclopropane

/-! Kernel-reducible evaluation of the native constitutional ligand words for the
nine-atom reference topology. The reference coordinates are used only for
structural admission. The public report theorem ranges over independently
admitted coordinates at every ordinary-hydrogen spelling. -/
set_option autoImplicit false

namespace TetraStereo.Engine.KernelSort
open List.MergeSort.Internal

def mergeFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if le x y then x :: mergeFuel le n xs (y::ys)
    else y :: mergeFuel le n (x::xs) ys

theorem mergeFuel_eq {α : Type} (le : α → α → Bool) (n : Nat) (xs ys : List α)
    (bound : xs.length + ys.length ≤ n) : mergeFuel le n xs ys = List.merge xs ys le := by
  induction n generalizing xs ys with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hy : ys = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs; subst ys; simp [mergeFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [mergeFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeFuel]
      | cons y ys =>
        simp only [mergeFuel,List.merge]
        split
        · rw [ih _ _ (by simp only [List.length_cons] at bound ⊢; omega)]
        · rw [ih _ _ (by simp only [List.length_cons] at bound ⊢; omega)]

def sortFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | _+1, [] => []
  | _+1, [x] => [x]
  | n+1, x::y::xs =>
    let lr := splitInTwo ⟨x::y::xs,rfl⟩
    mergeFuel le (x::y::xs).length (sortFuel le n lr.1.val) (sortFuel le n lr.2.val)

theorem sortFuel_eq {α : Type} (le : α → α → Bool) (n : Nat) (xs : List α)
    (bound : xs.length ≤ n) : sortFuel le n xs = List.mergeSort xs le := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs; simp [sortFuel]
  | succ n ih =>
    cases xs with
    | nil => simp [sortFuel]
    | cons x xs =>
      cases xs with
      | nil => simp [sortFuel]
      | cons y xs =>
        simp only [sortFuel,List.mergeSort]
        let lr := splitInTwo ⟨x::y::xs,rfl⟩
        have left : lr.1.val.length ≤ n := by
          have h := lr.1.property
          simp only [List.length_cons] at bound h
          omega
        have right : lr.2.val.length ≤ n := by
          have h := lr.2.property
          simp only [List.length_cons] at bound h
          omega
        rw [ih lr.1.val left,ih lr.2.val right,mergeFuel_eq]
        simp only [List.length_mergeSort]
        have h := lr.1.property
        have k := lr.2.property
        simp only [List.length_cons] at h k ⊢
        omega

def sort {α : Type} (xs : List α) (le : α → α → Bool) : List α := sortFuel le xs.length xs

theorem sort_eq {α : Type} (xs : List α) (le : α → α → Bool) : sort xs le = List.mergeSort xs le :=
  sortFuel_eq le xs.length xs (Nat.le_refl _)

theorem function_eq : @List.mergeSort = @sort := by
  funext α xs le
  exact (sort_eq xs le).symm

end TetraStereo.Engine.KernelSort

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace TetraStereo.Engine.RingHydrogenSpelling.IsotopeOrder
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)

def molecule : RawMolecule where
  atoms := [.aliphatic .C,.aliphatic .C,.aliphatic .C,.aliphatic .Br,.aliphatic .F,
    { AtomSpec.aliphatic .H with isotope? := some 2 },.aliphatic .H,.aliphatic .H,.aliphatic .H]
  bonds := [⟨0,1,.single⟩,⟨0,2,.single⟩,⟨0,3,.single⟩,⟨0,4,.single⟩,⟨1,2,.single⟩,
    ⟨1,5,.single⟩,⟨1,6,.single⟩,⟨2,7,.single⟩,⟨2,8,.single⟩]

def referencePoints : SpatialConfiguration := ⟨List.replicate 9 ⟨0,0,0⟩⟩
theorem reference_exists : (LocalizedChemicalRing.admitRawSpatial? molecule referencePoints).isSome = true := by decide +kernel

def reference : Input := (LocalizedChemicalRing.admitRawSpatial? molecule referencePoints).get reference_exists

theorem reference_size : reference.certified.certified.input.molecule.atomCount = 9 := by decide +kernel

def atom (n : Fin 9) : reference.certified.Atom := Fin.cast reference_size.symm n

def origin (n : Fin 9) := RingGroupedReport.origin reference (atom n)

def neighborIDs (n : Fin 9) : List (Fin 9) :=
  match n.val with
  | 0 => [1,2,3,4]
  | 1 => [0,2,5,6]
  | 2 => [0,1,7,8]
  | 3 | 4 => [0]
  | 5 | 6 => [1]
  | _ => [2]

theorem neighbors_sorted (n : Fin 9) :
    (reference.certified.moleculeGraph.neighborFinset (atom n)).sort (· ≤ ·) = (neighborIDs n).map atom := by
  have setEq : reference.certified.moleculeGraph.neighborFinset (atom n) = ((neighborIDs n).map atom).toFinset := by
    ext a
    rw [reference.certified.moleculeGraph.mem_neighborFinset]
    revert a
    fin_cases n <;> decide +kernel
  rw [setEq]
  fin_cases n <;> apply (List.toFinset_sort (· ≤ ·) (by decide +kernel)).mpr <;> decide +kernel

def fastNeighborCopies (a : reference.certified.Atom) :=
  (neighborIDs (Fin.cast reference_size a)).flatMap fun n =>
    (List.range (reference.certified.moleculeGraph.bond a (atom n))).map fun k => (atom n,k)

theorem neighborCopies_eq (a : reference.certified.Atom) :
    reference.certified.executableOfficialNeighborCopies a = fastNeighborCopies a := by
  have aeq : a = atom (Fin.cast reference_size a) := rfl
  conv_lhs => rw [aeq]
  unfold executableOfficialNeighborCopies
  rw [neighbors_sorted,List.flatMap_map]
  rfl

def fastChildCopies (node : OfficialCIPNode reference.certified.Atom) :=
  match node.current? with
  | none => []
  | some a => match node.parent? with
    | none => fastNeighborCopies a
    | some parent => (fastNeighborCopies a).filter fun copy => !(copy.1 == parent && copy.2 == 0)

def fastChildren (node : OfficialCIPNode reference.certified.Atom) :=
  if node.isDuplicateLeaf then [] else (fastChildCopies node).map fun copy => node.extend copy.1 copy.2

theorem children_eq (node : OfficialCIPNode reference.certified.Atom) :
    reference.certified.executableOfficialCIPChildren node = fastChildren node := by
  unfold executableOfficialCIPChildren fastChildren executableOfficialChildCopies fastChildCopies
  cases node.current? <;> cases node.parent? <;> simp only [neighborCopies_eq]

def fastSubtree (root : reference.certified.Atom) : Nat → List Nat →
    OfficialCIPNode reference.certified.Atom → List reference.certified.LocalizedCIPOccurrenceFrame
  | 0,path,node => [⟨root,path,node,0⟩]
  | fuel+1,path,node => ⟨root,path,node,fuel+1⟩ ::
      (fastChildren node).zipIdx.flatMap fun child => fastSubtree root fuel (path++[child.2]) child.1

theorem subtree_eq (root : reference.certified.Atom) (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode reference.certified.Atom) :
    reference.certified.localizedOccurrenceSubtree root fuel path node = fastSubtree root fuel path node := by
  induction fuel generalizing path node with
  | zero => rfl
  | succ fuel ih =>
    simp only [localizedOccurrenceSubtree,fastSubtree,children_eq]
    congr 1
    apply List.flatMap_congr
    intro child _
    exact ih _ _

def fastOccurrences (fuel : Nat) :=
  ((List.finRange reference.certified.certified.input.molecule.atomCount).flatMap
    fun root => fastSubtree root (fuel+1) [] (OfficialCIPNode.root root)).dedup

theorem occurrences_eq (fuel : Nat) : reference.certified.localizedOccurrences fuel = fastOccurrences fuel := by
  unfold localizedOccurrences localizedOccurrencesAtAtom fastOccurrences
  simp only [subtree_eq]

def fastIntended {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :=
  let neighbors := ((fastOccurrences fuel).filter fun c => c.root == cursor.occurrence.val.root &&
    c.address.length+1 == cursor.occurrence.val.address.length && c.address == cursor.occurrence.val.address.dropLast) ++
    ((fastOccurrences fuel).filter fun c => c.root == cursor.occurrence.val.root &&
      c.address.length == cursor.occurrence.val.address.length+1 && c.address.dropLast == cursor.occurrence.val.address)
  if cursor.occurrence.val.node.isDuplicateLeaf then [] else match cursor.previous? with
    | none => neighbors
    | some previous => neighbors.filter fun f => f.address != previous.val.address

theorem intended_eq {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :
    reference.certified.intendedLocalizedRerootChildFrames cursor = fastIntended cursor := by
  unfold intendedLocalizedRerootChildFrames localizedRerootNeighborFrames localizedCarrierParentFrames
    localizedCarrierOutwardChildFrames fastIntended
  cases cursor.previous? <;> simp only [occurrences_eq]

def fastRerootChildren {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :=
  (fastIntended cursor).attach.map fun f =>
    ({ occurrence := ⟨f.val, reference.certified.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
        cursor f.val (by rw [intended_eq]; exact f.property)⟩
       previous? := some cursor.occurrence } : reference.certified.LocalizedRerootCursor fuel)

theorem rerootChildren_eq {fuel : Nat} (cursor : reference.certified.LocalizedRerootCursor fuel) :
    reference.certified.executableLocalizedRerootChildren cursor = fastRerootChildren cursor := by
  unfold executableLocalizedRerootChildren fastRerootChildren
  rw [List.attach_congr (intended_eq cursor),List.map_map]
  apply List.map_congr_left
  intro frame _
  rfl

def centerZero : reference.certified.TetrahedralCenter := ⟨atom 0, by decide +kernel⟩

theorem zero_four : (RingRetainedAuxiliary.frame reference.certified (origin 0)).length = 4 := by
  unfold RingRetainedAuxiliary.frame
  rw [rerootChildren_eq]
  decide +kernel

theorem zero_atoms : (RingRetainedAuxiliary.frame reference.certified (origin 0)).mapM
    (fun q => q.occurrence.val.node.current?.map Fin.val) = some [1,2,3,4] := by
  unfold RingRetainedAuxiliary.frame
  rw [rerootChildren_eq]
  decide +kernel

theorem zero_canonical : RingRetainedAuxiliary.canonical reference.certified centerZero = [1,2,3,4] := by
  unfold RingRetainedAuxiliary.canonical canonicalLigandAtom canonicalNeighborList
  simp only [centerZero]
  have getD (k : Fin ((reference.certified.moleculeGraph.neighborFinset (atom 0)).sort (· ≤ ·)).length) :
      ((reference.certified.moleculeGraph.neighborFinset (atom 0)).sort (· ≤ ·)).get k =
      ((neighborIDs 0).map atom).getD k.val (atom 0) := by
    rw [← List.getD_eq_get (d := atom 0)]
    exact congrArg (fun xs : List reference.certified.Atom => xs.getD k.val (atom 0)) (neighbors_sorted 0)
  simp only [getD]
  decide +kernel

def frameZero : RingNestedActivePair.Frame reference (origin 0) where
  center := centerZero
  recognized := (reference.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mpr ⟨rfl,rfl⟩
  four := zero_four
  ids := [1,2,3,4]
  actualAtoms := zero_atoms
  physical := by rw [zero_canonical]

def centerOne : reference.certified.TetrahedralCenter := ⟨atom 1, by decide +kernel⟩

theorem one_four : (RingRetainedAuxiliary.frame reference.certified (origin 1)).length = 4 := by
  unfold RingRetainedAuxiliary.frame
  rw [rerootChildren_eq]
  decide +kernel

theorem one_atoms : (RingRetainedAuxiliary.frame reference.certified (origin 1)).mapM
    (fun q => q.occurrence.val.node.current?.map Fin.val) = some [0,2,5,6] := by
  unfold RingRetainedAuxiliary.frame
  rw [rerootChildren_eq]
  decide +kernel

theorem one_canonical : RingRetainedAuxiliary.canonical reference.certified centerOne = [0,2,5,6] := by
  unfold RingRetainedAuxiliary.canonical canonicalLigandAtom canonicalNeighborList
  simp only [centerOne]
  have getD (k : Fin ((reference.certified.moleculeGraph.neighborFinset (atom 1)).sort (· ≤ ·)).length) :
      ((reference.certified.moleculeGraph.neighborFinset (atom 1)).sort (· ≤ ·)).get k =
      ((neighborIDs 1).map atom).getD k.val (atom 1) := by
    rw [← List.getD_eq_get (d := atom 1)]
    exact congrArg (fun xs : List reference.certified.Atom => xs.getD k.val (atom 1)) (neighbors_sorted 1)
  simp only [getD]
  decide +kernel

def frameOne : RingNestedActivePair.Frame reference (origin 1) where
  center := centerOne
  recognized := (reference.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mpr ⟨rfl,rfl⟩
  four := one_four
  ids := [0,2,5,6]
  actualAtoms := one_atoms
  physical := by rw [one_canonical]

open private mergeLayers makeColumn rulePrefix build from TetraStereo.Engine.RingRetainedChemicalTrace
open RingRetainedChemicalTrace

def fastMergeLayers {α : Type} : List (List α) → List (List α) → List (List α)
  | [],ys => ys
  | xs,[] => xs
  | x::xs,y::ys => (x++y)::fastMergeLayers xs ys

def stagePrefix : Stage → List Stage
  | .atomic => [.atomic]
  | .duplicate => [.atomic,.duplicate]
  | .mass => [.atomic,.duplicate,.mass]

def fastColumn (o : Observation) (cs : List Key) (s : Stage) : Column :=
  let shallow (k : Key) := (stagePrefix s).map k.root.atStage
  let deep (k : Key) := (stagePrefix s).map fun t => (k.column t).word
  let a := KernelSort.sort cs (fun x y => decide (shallow y ≤ shallow x))
  let b := KernelSort.sort cs (fun x y => decide (deep y ≤ deep x))
  let row (ks : List Key) := ks.map fun k => k.root.atStage s
  let levels := [row a,row b] :: b.foldr (fun k acc => fastMergeLayers (k.column s).levels acc) []
  ⟨[o.atStage s] :: levels.flatten, levels⟩

private theorem mergeLayers_eq : @mergeLayers = @fastMergeLayers := by
  funext α xs ys
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys with
    | nil => rfl
    | cons y ys => exact congrArg (List.cons (x++y)) (ih ys)

private theorem column_eq (o : Observation) (cs : List Key) (s : Stage) :
    makeColumn o cs s = fastColumn o cs s := by
  have prefixEq : rulePrefix = stagePrefix := by funext t; cases t <;> rfl
  have sortEq : @List.mergeSort = @KernelSort.sort := KernelSort.function_eq
  change (⟨[o.atStage s] :: _, _⟩ : Column) = _
  unfold fastColumn
  simp only [← mergeLayers_eq, ← prefixEq, ← sortEq]
  rfl

def fastAssemble (o : Observation) (ks : List Key) : Key :=
  ⟨o,fastColumn o ks .atomic,fastColumn o ks .duplicate,fastColumn o ks .mass⟩

theorem assemble_eq (o : Observation) (ks : List Key) : assemble o ks = fastAssemble o ks := by
  unfold assemble fastAssemble
  rw [column_eq,column_eq,column_eq]

def fastBuild {d : Nat} : Nat → reference.certified.LocalizedRerootCursor d → Option Key
  | 0,_ => none
  | n+1,q => do
    let cs := fastRerootChildren q
    let root ← observation? reference q cs.isEmpty
    let keys ← cs.mapM (fastBuild n)
    return fastAssemble root keys

private theorem build_eq {d : Nat} (n : Nat) (q : reference.certified.LocalizedRerootCursor d) :
    build reference reference.certified.executableLocalizedRerootChildren n q = fastBuild n q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    change (do
      let cs := reference.certified.executableLocalizedRerootChildren q
      let root ← observation? reference q cs.isEmpty
      let keys ← cs.mapM (build reference reference.certified.executableLocalizedRerootChildren n)
      pure (assemble root keys)) = _
    have recEq : build reference reference.certified.executableLocalizedRerootChildren n = fastBuild n := funext ih
    simp only [rerootChildren_eq,recEq,assemble_eq]
    rfl

theorem key_eq {d : Nat} (q : reference.certified.LocalizedRerootCursor d) :
    key? reference q = fastBuild (2*(d+1)+1) q := build_eq _ _

def fastArm (n : Fin 9) (k : RingActivePairReport.Slot) :=
  (fastRerootChildren ⟨origin n,none⟩).getD k.val ⟨origin n,none⟩

theorem arm_eq {n : Fin 9} (fr : RingNestedActivePair.Frame reference (origin n))
    (k : RingActivePairReport.Slot) : fr.arm k = fastArm n k := by
  unfold RingNestedActivePair.Frame.arm
  rw [← List.getD_eq_get (d := ⟨origin n,none⟩)]
  change (reference.certified.executableLocalizedRerootChildren ⟨origin n,none⟩).getD k.val ⟨origin n,none⟩ = _
  exact congrArg (fun xs => xs.getD k.val ⟨origin n,none⟩) (rerootChildren_eq ⟨origin n,none⟩)

def fastWord (n : Fin 9) (k : RingActivePairReport.Slot) : List Word :=
  ((fastBuild (2*((reference.certified.certified.input.molecule.atomCount+1)+1)+1)
    ⟨(fastArm n k).occurrence,some (origin n)⟩).map RingRetainedChemicalPreorder.orderWord).getD []

theorem word_eq {n : Fin 9} (fr : RingNestedActivePair.Frame reference (origin n))
    (k : RingActivePairReport.Slot) : RingFullPathConstitution.word fr k = fastWord n k := by
  have read := RingRetainedChemicalPreorder.read_key (fr.direction k)
  rw [key_eq] at read
  change fastBuild _ ⟨(fr.arm k).occurrence,some (origin n)⟩ = some _ at read
  rw [arm_eq] at read
  unfold RingFullPathConstitution.word fastWord
  rw [read]
  rfl

def rowZero : List RingActivePairReport.Slot := [2,3,0,1]
def rowOne : List RingActivePairReport.Slot := [0,1,2,3]

theorem zero_descending : ((rowZero.map (fastWord 0))).Pairwise (· > ·) := by decide +kernel

theorem one_descending : ((rowOne.map (fastWord 1))).Pairwise (· > ·) := by decide +kernel

theorem injective_of_descending (f : RingActivePairReport.Slot → List Word)
    (row : List RingActivePairReport.Slot) (perm : row.Perm (List.finRange 4))
    (desc : (row.map f).Pairwise (· > ·)) : Function.Injective f := by
  have nd : (row.map f).Nodup := desc.imp (fun h => ne_of_gt h)
  have rnodup : row.Nodup := perm.nodup_iff.mpr (List.nodup_finRange 4)
  intro a b eq
  exact (List.nodup_map_iff_inj_on rnodup).mp nd a
    (perm.mem_iff.mpr (List.mem_finRange a)) b
    (perm.mem_iff.mpr (List.mem_finRange b)) eq

def certificateZero : RingConstitutionalHand.DescendingFrame frameZero [3,4,1,2] where
  row := rowZero
  strict := by
    have eq : RingFullPathConstitution.word frameZero = fastWord 0 := funext (word_eq frameZero)
    rw [eq]
    exact injective_of_descending _ rowZero (by decide +kernel) zero_descending
  legal := ⟨by decide +kernel, by
    have eq : RingFullPathConstitution.word frameZero = fastWord 0 := funext (word_eq frameZero)
    rw [eq]
    exact zero_descending.imp (fun h => le_of_lt h)⟩
  atoms_eq := by decide +kernel

def certificateOne : RingConstitutionalHand.DescendingFrame frameOne [0,2,5,6] where
  row := rowOne
  strict := by
    have eq : RingFullPathConstitution.word frameOne = fastWord 1 := funext (word_eq frameOne)
    rw [eq]
    exact injective_of_descending _ rowOne (by decide +kernel) one_descending
  legal := ⟨by decide +kernel, by
    have eq : RingFullPathConstitution.word frameOne = fastWord 1 := funext (word_eq frameOne)
    rw [eq]
    exact one_descending.imp (fun h => le_of_lt h)⟩
  atoms_eq := by decide +kernel

assert_kernel_only certificateZero
assert_kernel_only certificateOne
assert_kernel_only frameZero
assert_kernel_only key_eq
assert_kernel_only word_eq
end TetraStereo.Engine.RingHydrogenSpelling.IsotopeOrder

namespace TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
open OneCenter IsotopeOrder RingConstitutionalHand
open RingGroupedReport (Report)

theorem reference_source : reference.molecule = source 7 := by decide +kernel

theorem reference_frames (a : reference.certified.Atom) (small : a.val < 2) :
    ∃ fr : RingNestedActivePair.Frame reference (RingGroupedReport.origin reference a),
      Nonempty (OrientationFrame fr (if a.val = 0 then [3,4,1,2] else [0,2,5,6])) := by
  rcases (by omega : a.val = 0 ∨ a.val = 1) with zero | one
  · have atZero : a = atom 0 := Fin.ext zero
    subst a
    exact ⟨frameZero,⟨certificateZero.ranked⟩⟩
  · have atOne : a = atom 1 := Fin.ext one
    subst a
    exact ⟨frameOne,⟨certificateOne.ranked⟩⟩

/-- The public result at every spelling and coordinate table, for any ordered
list of original IDs. Admission depends only on the source and prepared tables. -/
theorem public_report_iff (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    RingHydrogenReport.fromRaw? (source mask) xyz ids = some rows ↔
      PlacementAdmission (source mask) xyz ids ∧ rows = ids.map (fun n => (n,predicted mask xyz n)) :=
  public_of_constitution reference reference_source reference_frames mask xyz ids rows

/-- Every successful report assigns exactly the requested occurrences of C0 and C1. -/
theorem public_assigned_iff (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat) (rows : Report)
    (issued : RingHydrogenReport.fromRaw? (source mask) xyz ids = some rows) (n : Nat) :
    (∃ labels, (n,some labels) ∈ rows) ↔ n ∈ ids ∧ n < 2 := by
  obtain ⟨gate,rfl⟩ := (public_report_iff mask xyz ids rows).mp issued
  obtain ⟨c0,c1⟩ := predicted_isSome_of_constitution reference reference_source reference_frames mask xyz ids gate
  constructor
  · rintro ⟨labels,mem⟩
    obtain ⟨a,ha,eqn⟩ := List.mem_map.mp mem
    obtain ⟨rfl,value⟩ := Prod.mk.inj eqn
    refine ⟨ha,?_⟩
    by_contra! high
    simp [predicted,show a ≠ 0 by omega,show a ≠ 1 by omega] at value
  · rintro ⟨requested,small⟩
    have someLabel : (predicted mask xyz n).isSome = true := by
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
      · exact c0
      · exact c1
    obtain ⟨label,found⟩ := Option.isSome_iff_exists.mp someLabel
    exact ⟨label,List.mem_map.mpr ⟨n,requested,by rw [found]⟩⟩

theorem public_reject_iff (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat) :
    RingHydrogenReport.fromRaw? (source mask) xyz ids = none ↔ ¬ PlacementAdmission (source mask) xyz ids := by
  constructor
  · intro rejected gate
    have accepted := (public_report_iff mask xyz ids _).mpr ⟨gate,rfl⟩
    rw [rejected] at accepted
    contradiction
  · intro failed
    cases computed : RingHydrogenReport.fromRaw? (source mask) xyz ids with
    | none => rfl
    | some rows => exact (failed ((public_report_iff mask xyz ids rows).mp computed).1).elim

end TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.public_report_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.public_reject_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.public_assigned_iff

namespace TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
open OneCenter RingHydrogenCompletion RingWrittenPHReadings LocalizedGenericMarkedRecalculation
open CertifiedLocalizedCIPInput

/-- An independent readback using only the original input coordinates. For an
omitted ordinary H at C1, the fourth point is the center itself. -/
def sourcePrediction (mask : Fin 8) (xyz : SpatialConfiguration) (id : Nat) : Option RingNestedActivePair.Labels :=
  if id = 0 then chiralReading xyz [3,4,1,2]
  else if id = 1 then chiralReading xyz [0,2,5,if mask.val.testBit 0 then 6 else 1]
  else none

private theorem first_generated_lookup {m out : RawMolecule} {xyz pos : SpatialConfiguration}
    (done : prepare? m xyz = some (out,pos)) (rest : List (Nat × Nat))
    (planned : plan m = (1,1)::rest) (h : Point)
    (head : placeAt? m xyz (1,1) = some [h]) : pos.positions[m.atomCount]? = some h := by
  have inputLength := (prepare?_certified done).input_positions
  obtain ⟨candidate,hc,hg⟩ := Option.bind_eq_some_iff.mp done
  obtain ⟨same,_⟩ := gate_eq_some hg
  subst candidate
  unfold candidate? at hc
  rw [planned] at hc
  simp only [List.isEmpty_cons,Bool.false_eq_true,if_false] at hc
  unfold addedPositions? at hc
  rw [planned,List.mapM_cons,head] at hc
  cases tail : rest.mapM (placeAt? m xyz) with
  | none => simp [tail] at hc
  | some blocks =>
    simp only [tail,pure] at hc
    have positions := congrArg (fun r : RawMolecule × SpatialConfiguration => r.2.positions) (Option.some.inj hc)
    change xyz.positions ++ ([h] :: blocks).flatten = pos.positions at positions
    rw [←positions,←inputLength,List.getElem?_append_right (Nat.le_refl _)]
    simp

private theorem absent_plan : ∀ mask : Fin 8, mask.val.testBit 0 = false →
    ∃ rest, plan (source mask) = (1,1)::rest := by
  intro mask off
  refine ⟨(plan (source mask)).tail,?_⟩
  exact (by decide : ∀ m : Fin 8, m.val.testBit 0 = false →
    plan (source m) = (1,1)::(plan (source m)).tail) mask off
private theorem absent_neighbors : ∀ mask : Fin 8, mask.val.testBit 0 = false →
    neighbors (source mask) 1 = [0,2,5] ∧
      ((source mask).writtenNeighbors 1).any (ordinaryHydrogenVertex (source mask)) = false := by decide

theorem generated_c1_lookup (mask : Fin 8) {xyz pos : SpatialConfiguration} {out : RawMolecule}
    (done : prepare? (source mask) xyz = some (out,pos)) (off : mask.val.testBit 0 = false)
    (p0 p1 p2 p5 : Point)
    (h0 : xyz.positions[0]? = some p0) (h1 : xyz.positions[1]? = some p1)
    (h2 : xyz.positions[2]? = some p2) (h5 : xyz.positions[5]? = some p5) :
    pos.positions[(source mask).atomCount]? = some (opposite p1 [p0,p2,p5]) := by
  obtain ⟨rest,planned⟩ := absent_plan mask off
  apply first_generated_lookup done rest planned
  have facts := absent_neighbors mask off
  simp [placeAt?,facts.1,facts.2,h0,h1,h2,h5,placed,place,single,List.take_succ_cons]

theorem opposite_reading (p0 p1 p2 p5 : Point) :
    descriptorOfPriorityOrderedPoints? [p0,p2,p5,opposite p1 [p0,p2,p5]] =
      descriptorOfPriorityOrderedPoints? [p0,p2,p5,p1] := by
  change descriptorOfOrientedVolume? (CartesianPoint3.orientedVolume p0 p2 p5 (opposite p1 [p0,p2,p5])) = _
  rw [orientedVolume_opposite]
  change descriptorOfOrientedVolume? (4 * CartesianPoint3.orientedVolume p0 p2 p5 p1) =
    descriptorOfOrientedVolume? (CartesianPoint3.orientedVolume p0 p2 p5 p1)
  have positive : (0:ℚ) < 4 := by norm_num
  simp [descriptorOfOrientedVolume?,mul_neg_iff,positive,not_lt_of_ge positive.le]
end TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
namespace TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
open OneCenter RingHydrogenCompletion RingWrittenPHReadings LocalizedGenericMarkedRecalculation
open CertifiedLocalizedCIPInput

theorem predicted_eq_source (mask : Fin 8) {xyz pos : SpatialConfiguration} {out : RawMolecule}
    (done : prepare? (source mask) xyz = some (out,pos)) (id : Nat) :
    predicted mask xyz id = sourcePrediction mask xyz id := by
  by_cases atZero : id = 0
  · simp [predicted,sourcePrediction,atZero]
  by_cases atOne : id = 1
  swap
  · simp [predicted,sourcePrediction,atZero,atOne]
  subst id
  simp only [predicted,sourcePrediction,show (1:Nat) ≠ 0 from by decide,if_false,if_true,done]
  change chiralReading pos [0,2,5,c1HydrogenId mask] =
    chiralReading xyz [0,2,5,if mask.val.testBit 0 then 6 else 1]
  have cert := prepare?_certified done
  have bound (n : Fin 6) : n.val < xyz.positions.length := by
    rw [cert.input_positions]
    exact ((completion mask).core n).isLt
  have preserved (n : Fin 6) : geometry pos n.val = geometry xyz n.val := cert.positions_getElem? ((completion mask).core n).isLt
  have p0 : geometry pos 0 = geometry xyz 0 := preserved 0
  have p2 : geometry pos 2 = geometry xyz 2 := preserved 2
  have p5 : geometry pos 5 = geometry xyz 5 := preserved 5
  by_cases bit : mask.val.testBit 0 = true
  · have writtenBound : 6 < (source mask).atomCount :=
      (by decide : ∀ m : Fin 8, m.val.testBit 0 = true → 6 < (source m).atomCount) mask bit
    have p6 : geometry pos 6 = geometry xyz 6 := cert.positions_getElem? writtenBound
    simp only [c1HydrogenId,bit,if_true,chiralReading,readback?,List.mapM_cons,List.mapM_nil,p0,p2,p5,p6]
  · have off : mask.val.testBit 0 = false := Bool.eq_false_iff.mpr bit
    let a := xyz.positions[0]'(bound 0)
    let b := xyz.positions[1]'(bound 1)
    let c := xyz.positions[2]'(bound 2)
    let d := xyz.positions[5]'(bound 5)
    have h0 : xyz.positions[0]? = some a := List.getElem?_eq_getElem (bound 0)
    have h1 : xyz.positions[1]? = some b := List.getElem?_eq_getElem (bound 1)
    have h2 : xyz.positions[2]? = some c := List.getElem?_eq_getElem (bound 2)
    have h5 : xyz.positions[5]? = some d := List.getElem?_eq_getElem (bound 5)
    have hH := generated_c1_lookup mask done off a b c d h0 h1 h2 h5
    have hp0 : pos.positions[0]? = some a := p0.trans h0
    have hp2 : pos.positions[2]? = some c := p2.trans h2
    have hp5 : pos.positions[5]? = some d := p5.trans h5
    simp only [c1HydrogenId,off,Bool.false_eq_true,if_false]
    simp only [chiralReading,readback?,List.mapM_cons,List.mapM_nil,geometry,
      hp0,hp2,hp5,hH,h0,h1,h2,h5,Option.pure_def]
    exact congrArg (Option.map (fun h => (LocalizedTetrahedralRSPseudoDescriptor.chiral h,LocalizedTetrahedralRSPseudoDescriptor.chiral h.swap))) (opposite_reading a b c d)

end TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.predicted_eq_source
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.generated_c1_lookup
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.opposite_reading

namespace TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
open OneCenter RingGroupedReport

/-- The raw report from original coordinates only. When C1 has an implicit
ordinary hydrogen, the fourth determinant position can be C1 itself. -/
theorem public_source_iff (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat) (rows : Report) :
    RingHydrogenReport.fromRaw? (source mask) xyz ids = some rows ↔
      PlacementAdmission (source mask) xyz ids ∧ rows = ids.map (fun n => (n,sourcePrediction mask xyz n)) := by
  rw [public_report_iff]
  apply and_congr_right
  intro admitted
  have equal (n : Nat) : predicted mask xyz n = sourcePrediction mask xyz n :=
    by
    obtain ⟨_,_,_,_,_,_,prepared,_⟩ := admitted
    exact predicted_eq_source mask prepared n
  simp only [equal]

/-- Two admitted reports agree on an arbitrary common request exactly when the
original coordinate determinants agree at the requested stereogenic carbons. -/
theorem spelling_reports_eq_iff (a b : Fin 8) (x y : SpatialConfiguration) (ids : List Nat)
    (left : PlacementAdmission (source a) x ids) (right : PlacementAdmission (source b) y ids) :
    RingHydrogenReport.fromRaw? (source a) x ids = RingHydrogenReport.fromRaw? (source b) y ids ↔
      (0 ∈ ids → sourcePrediction a x 0 = sourcePrediction b y 0) ∧
      (1 ∈ ids → sourcePrediction a x 1 = sourcePrediction b y 1) := by
  rw [(public_source_iff a x ids _).mpr ⟨left,rfl⟩, (public_source_iff b y ids _).mpr ⟨right,rfl⟩,
    Option.some.injEq,List.map_inj_left]
  constructor
  · intro same
    exact ⟨fun atZero => congrArg Prod.snd (same 0 atZero),fun atOne => congrArg Prod.snd (same 1 atOne)⟩
  · rintro ⟨zero,one⟩ n member
    by_cases atZero : n = 0
    · subst n
      exact congrArg (fun v => (0,v)) (zero member)
    by_cases atOne : n = 1
    · subst n
      exact congrArg (fun v => (1,v)) (one member)
    · simp [sourcePrediction,atZero,atOne]

end TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.public_source_iff
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.spelling_reports_eq_iff

namespace TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
open OneCenter RingWrittenPHReadings LocalizedGenericMarkedRecalculation
open RingGroupedReport (Report)

/-- Reflection of the original, possibly hydrogen-suppressed input. -/
def reflectCoordinates (xyz : SpatialConfiguration) : SpatialConfiguration :=
  ⟨xyz.positions.map CartesianPoint3.reflectX⟩

private theorem chiralReading_reflected (xyz : SpatialConfiguration) (ids : List Nat) :
    chiralReading (reflectCoordinates xyz) ids = (chiralReading xyz ids).map Prod.swap := by
  have reflected : geometry (reflectCoordinates xyz) = mirror (geometry xyz) := by
    funext n
    simp [reflectCoordinates, geometry,mirror]
  unfold chiralReading
  rw [reflected,readback_mirror]
  cases readback? (geometry xyz) ids with
  | none => rfl
  | some h => cases h <;> rfl

theorem sourcePrediction_reflected (mask : Fin 8) (xyz : SpatialConfiguration) (id : Nat) :
    sourcePrediction mask (reflectCoordinates xyz) id = (sourcePrediction mask xyz id).map Prod.swap := by
  by_cases z : id = 0 <;> by_cases o : id = 1 <;> simp [sourcePrediction,z,o,chiralReading_reflected]

/-- Re-running the raw evaluator on an admitted reflected source swaps the two
hands in every reported row, with the identical atom order and refusal rows. -/
theorem public_reflected (mask : Fin 8) (xyz : SpatialConfiguration) (ids : List Nat) (rows : Report)
    (issued : RingHydrogenReport.fromRaw? (source mask) xyz ids = some rows)
    (reflected : PlacementAdmission (source mask) (reflectCoordinates xyz) ids) :
    RingHydrogenReport.fromRaw? (source mask) (reflectCoordinates xyz) ids =
      some (rows.map (fun row => (row.1,row.2.map Prod.swap))) := by
  obtain ⟨_,rfl⟩ := (public_source_iff mask xyz ids rows).mp issued
  apply (public_source_iff mask _ ids _).mpr
  exact ⟨reflected,by simp only [List.map_map,Function.comp_def,sourcePrediction_reflected]⟩

end TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings
assert_kernel_only TetraStereo.Engine.RingHydrogenSpelling.IsotopeSpellings.public_reflected
