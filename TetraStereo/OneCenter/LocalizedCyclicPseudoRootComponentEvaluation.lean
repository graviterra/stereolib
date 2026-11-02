import TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter
import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.OneCenter.LocalizedOccurrenceCarrier
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
Root-0 component twin for the nine-atom cyclic pseudo candidate.

The production neighbor enumeration sorts a finset. This file substitutes the
proved neighbor table, builds only the official expansion from atom 0, and
evaluates constitutional keys under the constant-`none` reader. Those keys are
the production keys at every cursor rooted at atom 0.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation

open TetraStereo.OneCenter
open CertifiedLocalizedCIPInput
open LocalizedCyclicPseudoInputWitness
open LocalizedCyclicPseudoSpatialWitness
open OfficialCIPNode

def refInput : LocalizedRuleMajorReference.Input where
  certified := pseudoSpatialCertified

abbrev Input := pseudoSpatialCertified
abbrev Atom := Input.Atom
abbrev Frame := Input.LocalizedCIPOccurrenceFrame
abbrev Fuel := LocalizedUniversalReference.carrierFuel refInput
abbrev Cursor := Input.LocalizedRerootCursor Fuel
abbrev Key := Input.LocalizedRerootCumulativeRule45Key
abbrev Label := LocalizedAuxiliaryLabel

private theorem spatial_atomCount :
    pseudoSpatialCertified.certified.input.molecule.atomCount = 9 := by
  have moleculeEq : pseudoSpatialCertified.certified.input.molecule = pseudoSource.molecule := by
    rw [show pseudoSpatialCertified.certified.input = pseudoSpatialSource from rfl, spatial_molecule]
  rw [moleculeEq]
  exact atomCount_eq

def SA (i : Fin 9) : Atom :=
  ⟨i.val, by rw [spatial_atomCount]; exact i.isLt⟩

private theorem SA_eq (i : Fin 9) : SA i = i := by
  apply Fin.ext
  rfl

theorem fuel_eq : Fuel = 10 := by
  have count : Fuel = pseudoSpatialCertified.certified.input.molecule.atomCount + 1 := rfl
  rw [count, spatial_atomCount]

/-! ## Neighbor table -/

def neighborsOf (a : Atom) : List Atom :=
  match a.val with
  | 0 => [SA 1, SA 2, SA 4, SA 5]
  | 1 => [SA 0]
  | 2 => [SA 0, SA 3, SA 4, SA 6]
  | 3 => [SA 2]
  | 4 => [SA 0, SA 2, SA 7, SA 8]
  | 5 => [SA 0]
  | 6 => [SA 2]
  | 7 => [SA 4]
  | 8 => [SA 4]
  | _ => []

private theorem sorted_of_neighbors (center : Fin 9) (atoms : List (Fin 9))
    (nodup : atoms.Nodup) (pairwise : atoms.Pairwise (· ≤ ·))
    (members : ∀ atom : Fin 9, graph.Adj center atom ↔ atom ∈ atoms) :
    (graph.neighborFinset center).sort (· ≤ ·) = atoms := by
  have finsetEq : graph.neighborFinset center = atoms.toFinset := by
    ext atom
    simp only [MoleculeGraph.mem_neighborFinset, List.mem_toFinset]
    exact members atom
  rw [finsetEq]
  exact ((List.toFinset_sort (· ≤ ·) nodup).mpr pairwise)

private theorem adj_atom3 (atom : Fin 9) : graph.Adj 3 atom ↔ atom = 2 := by
  fin_cases atom <;> decide

private theorem adj_atom5 (atom : Fin 9) : graph.Adj 5 atom ↔ atom = 0 := by
  fin_cases atom <;> decide

private theorem adj_atom6 (atom : Fin 9) : graph.Adj 6 atom ↔ atom = 2 := by
  fin_cases atom <;> decide

private theorem adj_atom7 (atom : Fin 9) : graph.Adj 7 atom ↔ atom = 4 := by
  fin_cases atom <;> decide

private theorem adj_atom8 (atom : Fin 9) : graph.Adj 8 atom ↔ atom = 4 := by
  fin_cases atom <;> decide

private theorem graph_neighborSort :
    ((graph.neighborFinset 0).sort (· ≤ ·) = [1, 2, 4, 5]) ∧
      ((graph.neighborFinset 1).sort (· ≤ ·) = [0]) ∧
      ((graph.neighborFinset 2).sort (· ≤ ·) = [0, 3, 4, 6]) ∧
      ((graph.neighborFinset 3).sort (· ≤ ·) = [2]) ∧
      ((graph.neighborFinset 4).sort (· ≤ ·) = [0, 2, 7, 8]) ∧
      ((graph.neighborFinset 5).sort (· ≤ ·) = [0]) ∧
      ((graph.neighborFinset 6).sort (· ≤ ·) = [2]) ∧
      ((graph.neighborFinset 7).sort (· ≤ ·) = [4]) ∧
      ((graph.neighborFinset 8).sort (· ≤ ·) = [4]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sorted_of_neighbors 0 [1, 2, 4, 5] (by decide) (by decide) fun atom => by
      rw [adj_root]; simp [List.mem_cons]
  · exact sorted_of_neighbors 1 [0] (by decide) (by decide) fun atom => by
      rw [adj_fluorine]; simp [List.mem_cons]
  · exact sorted_of_neighbors 2 [0, 3, 4, 6] (by decide) (by decide) fun atom => by
      rw [adj_arm]; simp [List.mem_cons]
  · exact sorted_of_neighbors 3 [2] (by decide) (by decide) fun atom => by
      rw [adj_atom3]; simp [List.mem_cons]
  · exact sorted_of_neighbors 4 [0, 2, 7, 8] (by decide) (by decide) fun atom => by
      rw [adj_closing]; simp [List.mem_cons]
  · exact sorted_of_neighbors 5 [0] (by decide) (by decide) fun atom => by
      rw [adj_atom5]; simp [List.mem_cons]
  · exact sorted_of_neighbors 6 [2] (by decide) (by decide) fun atom => by
      rw [adj_atom6]; simp [List.mem_cons]
  · exact sorted_of_neighbors 7 [4] (by decide) (by decide) fun atom => by
      rw [adj_atom7]; simp [List.mem_cons]
  · exact sorted_of_neighbors 8 [4] (by decide) (by decide) fun atom => by
      rw [adj_atom8]; simp [List.mem_cons]

private theorem spatial_adj (i j : Fin 9) :
    Input.moleculeGraph.Adj (SA i) (SA j) ↔ graph.Adj i j := by
  rw [SA_eq, SA_eq]
  simp [MoleculeGraph.Adj, CertifiedLocalizedCIPInput.moleculeGraph, pseudoSpatialCertified,
    pseudoSpatialCertifiedAuthority, spatial_molecule, graph, pseudoCertified,
    pseudoCertifiedAuthority]

private theorem atom_val_lt (a : Atom) : a.val < 9 :=
  spatial_atomCount ▸ a.isLt

private theorem input_neighborSort (i : Fin 9) (atoms : List (Fin 9))
    (nodup : (atoms.map SA).Nodup) (ordered : (atoms.map SA).Pairwise (· ≤ ·))
    (members : ∀ j : Fin 9, Input.moleculeGraph.Adj (SA i) (SA j) ↔ j ∈ atoms) :
    (Input.moleculeGraph.neighborFinset (SA i)).sort (· ≤ ·) = atoms.map SA := by
  have finsetEq : Input.moleculeGraph.neighborFinset (SA i) = (atoms.map SA).toFinset := by
    ext atom
    rw [MoleculeGraph.mem_neighborFinset, List.mem_toFinset]
    constructor
    · intro adjacent
      let j : Fin 9 := ⟨atom.val, atom_val_lt atom⟩
      have atomEq : atom = SA j := by
        apply Fin.ext
        rfl
      rw [atomEq] at adjacent
      exact List.mem_map.mpr ⟨j, (members j).mp adjacent, atomEq.symm⟩
    · intro present
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp present
      exact (members j).mpr hj
  rw [finsetEq]
  exact (List.toFinset_sort (· ≤ ·) nodup).mpr ordered

private theorem neighborSort_SA (i : Fin 9) :
    (Input.moleculeGraph.neighborFinset (SA i)).sort (· ≤ ·) = neighborsOf (SA i) := by
  fin_cases i
  · have sorted := input_neighborSort 0 [1, 2, 4, 5] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_root]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 1 [0] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_fluorine]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 2 [0, 3, 4, 6] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_arm]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 3 [2] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_atom3]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 4 [0, 2, 7, 8] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_closing]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 5 [0] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_atom5]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 6 [2] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_atom6]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 7 [4] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_atom7]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted
  · have sorted := input_neighborSort 8 [4] (by decide) (by decide) fun j => by
      rw [spatial_adj, adj_atom8]; simp [List.mem_cons]
    simpa [neighborsOf] using sorted

theorem neighborSort_eq (a : Atom) :
    (Input.moleculeGraph.neighborFinset a).sort (· ≤ ·) = neighborsOf a := by
  have ha : a = SA ⟨a.val, atom_val_lt a⟩ := by
    apply Fin.ext
    rfl
  rw [ha]
  exact neighborSort_SA ⟨a.val, atom_val_lt a⟩

def neighborCopiesT (atom : Atom) : List (Atom × ℕ) :=
  (neighborsOf atom).flatMap fun neighbor =>
    (List.range (Input.moleculeGraph.bond atom neighbor)).map fun copyIndex =>
      (neighbor, copyIndex)

theorem neighborCopies_eq (atom : Atom) :
    Input.executableOfficialNeighborCopies atom = neighborCopiesT atom := by
  unfold executableOfficialNeighborCopies neighborCopiesT
  rw [neighborSort_eq]

def childCopiesT (node : OfficialCIPNode Atom) : List (Atom × ℕ) :=
  match node.current? with
  | none => []
  | some current =>
      match node.parent? with
      | none => neighborCopiesT current
      | some parent =>
          (neighborCopiesT current).filter fun copy =>
            !(copy.1 == parent && copy.2 == 0)

theorem childCopies_eq (node : OfficialCIPNode Atom) :
    Input.executableOfficialChildCopies node = childCopiesT node := by
  unfold executableOfficialChildCopies childCopiesT
  rcases hc : node.current? with _ | current
  · rfl
  · rcases hp : node.parent? with _ | parent
    · simp only [neighborCopies_eq]
    · simp only [neighborCopies_eq]

def childrenT (node : OfficialCIPNode Atom) : List (OfficialCIPNode Atom) :=
  if node.isDuplicateLeaf then []
  else (childCopiesT node).map fun copy => node.extend copy.1 copy.2

theorem children_eq (node : OfficialCIPNode Atom) :
    Input.executableOfficialCIPChildren node = childrenT node := by
  unfold executableOfficialCIPChildren childrenT
  rw [childCopies_eq]

/-! ## Root-0 carrier component -/

def subtreeT (root : Atom) : Nat → List Nat → OfficialCIPNode Atom → List Frame
  | 0, path, node => [{ root := root, address := path, node := node, remaining := 0 }]
  | fuel + 1, path, node =>
      { root := root, address := path, node := node, remaining := fuel + 1 } ::
        (childrenT node).zipIdx.flatMap fun child =>
          subtreeT root fuel (path ++ [child.2]) child.1

theorem subtree_eq (root : Atom) :
    ∀ (fuel : Nat) (path : List Nat) (node : OfficialCIPNode Atom),
      Input.localizedOccurrenceSubtree root fuel path node = subtreeT root fuel path node
  | 0, _, _ => rfl
  | fuel + 1, path, node => by
      rw [localizedOccurrenceSubtree, subtreeT, children_eq]
      congr 1
      congr 1
      funext child
      exact subtree_eq root fuel _ _

theorem subtreeT_root (a : Atom) :
    ∀ (fuel : Nat) (path : List Nat) (node : OfficialCIPNode Atom),
      ∀ f ∈ subtreeT a fuel path node, f.root = a
  | 0, _, _, _, hf => by
      simp only [subtreeT, List.mem_singleton] at hf
      rw [hf]
  | fuel + 1, _, _, f, hf => by
      simp only [subtreeT, List.mem_cons, List.mem_flatMap] at hf
      rcases hf with rfl | ⟨_, _, hchild⟩
      · rfl
      · exact subtreeT_root a fuel _ _ f hchild

def subtree0 : List Frame :=
  subtreeT (SA 0) (Fuel + 1) [] (OfficialCIPNode.root (SA 0))

/-- Finite path classification for real tetrahedral atoms in the root-zero component.  Duplicate
ring closures do not become descriptor sources. -/
def subtree0CenterAddressCheck (frame : Frame) : Bool :=
  match frame.node.current? with
  | none => true
  | some atom =>
      if atom == SA 0 then
        frame.node.provenance != OfficialCIPNodeProvenance.realAtom || frame.address == []
      else if atom == SA 2 then
        frame.node.provenance != OfficialCIPNodeProvenance.realAtom ||
          frame.address == [1] || frame.address == [2, 0]
      else if atom == SA 4 then
        frame.node.provenance != OfficialCIPNodeProvenance.realAtom ||
          frame.address == [2] || frame.address == [1, 1]
      else true

theorem subtree0_centerAddressCheck_all : subtree0.all subtree0CenterAddressCheck = true := by
  decide +kernel

theorem subtree0_centerAddressCheck (frame : Frame) (present : frame ∈ subtree0) :
    subtree0CenterAddressCheck frame = true :=
  (List.all_eq_true.mp subtree0_centerAddressCheck_all) frame present

theorem subtree0_nodup : subtree0.Nodup := by
  decide +kernel

theorem subtree0_root : ∀ f ∈ subtree0, f.root = SA 0 :=
  subtreeT_root (SA 0) _ _ _

theorem filter_dedup {α : Type*} [DecidableEq α] (p : α → Bool) :
    ∀ l : List α, l.dedup.filter p = (l.filter p).dedup
  | [] => rfl
  | x :: xs => by
      by_cases hx : x ∈ xs
      · rw [List.dedup_cons_of_mem hx]
        cases hp : p x
        · rw [List.filter_cons_of_neg (by simp [hp]), filter_dedup p xs]
        · rw [List.filter_cons_of_pos hp, List.dedup_cons_of_mem (List.mem_filter.2 ⟨hx, hp⟩),
            filter_dedup p xs]
      · rw [List.dedup_cons_of_notMem hx]
        cases hp : p x
        · rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_neg (by simp [hp]),
            filter_dedup p xs]
        · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hp,
            List.dedup_cons_of_notMem (fun h => hx (List.mem_filter.1 h).1), filter_dedup p xs]

theorem flatMap_eq_single {α β : Type*} (g : α → List β) (a : α) :
    ∀ l : List α, l.Nodup → a ∈ l → (∀ x ∈ l, x ≠ a → g x = []) → l.flatMap g = g a
  | [], _, ha, _ => by simp at ha
  | x :: xs, hnd, ha, hvan => by
      rw [List.flatMap_cons]
      rw [List.nodup_cons] at hnd
      by_cases hxa : x = a
      · subst hxa
        have : xs.flatMap g = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro y hy
          exact hvan y (List.mem_cons_of_mem x hy) (fun h => hnd.1 (h ▸ hy))
        rw [this, List.append_nil]
      · rw [hvan x List.mem_cons_self hxa, List.nil_append]
        exact flatMap_eq_single g a xs hnd.2
          (by rcases List.mem_cons.1 ha with h | h; exact absurd h.symm hxa; exact h)
          (fun y hy => hvan y (List.mem_cons_of_mem x hy))

def carrierRaw (fuel : Nat) : List Frame :=
  (List.finRange Input.certified.input.molecule.atomCount).flatMap fun a =>
    subtreeT a (fuel + 1) [] (OfficialCIPNode.root a)

theorem carrier_eq (fuel : Nat) :
    Input.localizedOccurrences fuel = (carrierRaw fuel).dedup := by
  unfold localizedOccurrences localizedOccurrencesAtAtom carrierRaw
  simp only [subtree_eq]

theorem carrierRaw_filter0 (p : Frame → Bool) (hp : ∀ c, p c = true → c.root = SA 0) :
    (carrierRaw Fuel).filter p = subtree0.filter p := by
  unfold carrierRaw
  rw [List.filter_flatMap]
  exact flatMap_eq_single _ (SA 0) _ (List.nodup_finRange _) (List.mem_finRange _)
    (fun x _ hx => List.filter_eq_nil_iff.2 fun f hf hpf =>
      hx ((subtreeT_root x _ _ _ f hf).symm.trans (hp f hpf)))

theorem carrier_filter0 (p : Frame → Bool) (hp : ∀ c, p c = true → c.root = SA 0) :
    (Input.localizedOccurrences Fuel).filter p = subtree0.filter p := by
  rw [carrier_eq, filter_dedup, carrierRaw_filter0 p hp,
    List.dedup_eq_self.2 ((subtree0_nodup).filter p)]

theorem mem_carrier_of_mem_subtree0 {f : Frame} (hf : f ∈ subtree0) :
    f ∈ Input.localizedOccurrences Fuel := by
  rw [carrier_eq, List.mem_dedup]
  exact List.mem_flatMap.2 ⟨SA 0, List.mem_finRange _, hf⟩

theorem mem_subtree0_of_mem_carrier {f : Frame}
    (hf : f ∈ Input.localizedOccurrences Fuel) (hroot : f.root = SA 0) :
    f ∈ subtree0 := by
  have h : f ∈ (Input.localizedOccurrences Fuel).filter (fun c => c.root == SA 0) :=
    List.mem_filter.2 ⟨hf, by simpa using hroot⟩
  rw [carrier_filter0 _ (fun c hc => by simpa using hc)] at h
  exact (List.mem_filter.1 h).1

def parentFrames0 (frame : Frame) : List Frame :=
  subtree0.filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length + 1 == frame.address.length &&
      candidate.address == frame.address.dropLast

def outward0 (frame : Frame) : List Frame :=
  subtree0.filter fun candidate =>
    candidate.root == frame.root &&
      candidate.address.length == frame.address.length + 1 &&
      candidate.address.dropLast == frame.address

def neighborFrames0 (frame : Frame) : List Frame :=
  parentFrames0 frame ++ outward0 frame

theorem root_of_pred {frame candidate : Frame} (h : frame.root = SA 0) {P : Prop}
    (hc : candidate.root = frame.root ∧ P) : candidate.root = SA 0 :=
  hc.1.trans h

theorem neighborFrames_eq0 (frame : Frame) (h : frame.root = SA 0) :
    Input.localizedRerootNeighborFrames (fuel := Fuel) frame = neighborFrames0 frame := by
  unfold localizedRerootNeighborFrames localizedCarrierParentFrames
    localizedCarrierOutwardChildFrames neighborFrames0 parentFrames0 outward0
  rw [carrier_filter0 _ (fun c hc => root_of_pred h (by simpa [and_assoc] using hc)),
    carrier_filter0 _ (fun c hc => root_of_pred h (by simpa [and_assoc] using hc))]

def intendedPair0 (frame : Frame) (previous? : Option Frame) : List Frame :=
  if frame.node.isDuplicateLeaf then []
  else
    match previous? with
    | none => neighborFrames0 frame
    | some previous =>
        (neighborFrames0 frame).filter fun candidate =>
          candidate.address != previous.address

theorem intended_eq0 (cursor : Cursor) (h : cursor.occurrence.1.root = SA 0) :
    Input.intendedLocalizedRerootChildFrames cursor =
      intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val) := by
  unfold intendedLocalizedRerootChildFrames intendedPair0
  cases cursor.previous? <;>
    simp only [neighborFrames_eq0 _ h, Option.map_none, Option.map_some]

theorem mem_subtree0_of_mem_intendedPair0 {frame : Frame} {previous? : Option Frame}
    {f : Frame} (hf : f ∈ intendedPair0 frame previous?) : f ∈ subtree0 := by
  unfold intendedPair0 at hf
  split at hf
  · simp at hf
  · cases previous? with
    | none =>
        simp only [neighborFrames0, parentFrames0, outward0, List.mem_append, List.mem_filter] at hf
        rcases hf with h | h <;> exact h.1
    | some _ =>
        simp only [neighborFrames0, parentFrames0, outward0, List.mem_filter,
          List.mem_append] at hf
        rcases hf.1 with h | h <;> exact h.1

/-! ## Constant-none builder twin -/

def readFrameT (_frame : Frame) : Option Label := none

def readT (_cursor : Cursor) : Option Label := none

theorem mapM_congr_mem {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | x :: l, h => by
      rw [List.mapM_cons, List.mapM_cons, h x List.mem_cons_self,
        mapM_congr_mem f g l (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem mapM_map' {α β γ : Type} (f : α → β) (g : β → Option γ) :
    ∀ l : List α, (l.map f).mapM g = l.mapM (fun x => g (f x))
  | [] => rfl
  | x :: l => by rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map' f g l]

def buildF (stage : LocalizedCumulativeRule45Stage) : Nat → Frame → Option Frame → Option Key
  | 0, frame, previous? =>
      let children := intendedPair0 frame previous?
      if children.isEmpty then
        let label := readFrameT frame
        some
          { constitutional := Input.moleculeGraph.officialRuleMajorRootKey frame.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else none
  | fuel + 1, frame, previous? =>
      let children := intendedPair0 frame previous?
      let label := readFrameT frame
      if children.isEmpty then
        some
          { constitutional := Input.moleculeGraph.officialRuleMajorRootKey frame.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }
      else
        (children.mapM (fun child => buildF stage fuel child (some frame))).bind fun childKeys =>
          let sorted := Input.sortLocalizedRerootCumulativeRule45Keys childKeys
          some
            { constitutional := OfficialRuleMajorKey.assemble
                (Input.moleculeGraph.officialRuleMajorRootKey frame.node false)
                (sorted.map fun child => child.constitutional)
              descriptor :=
                [[([], localizedCumulativeRule45Priority stage label)]] ++
                  Input.mergeLocalizedRerootDescriptorChildren sorted
              labels := [[([], label)]] ++
                Input.mergeLocalizedRerootLabelChildren sorted
              rankedLabels := [[([], label)]] ++
                Input.mergeLocalizedRerootRankedLabelChildren sorted }

theorem build_eq (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (cursor : Cursor), cursor.occurrence.1.root = SA 0 →
      Input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage readT fuel cursor =
        buildF stage fuel cursor.occurrence.1 (cursor.previous?.map Subtype.val)
  | 0, cursor, h => by
      rw [buildLocalizedRerootCumulativeRule45KeyWithRead?,
        Input.localizedRerootChildren?_eq_some_executable, buildF]
      change Option.bind (some _) _ = _
      rw [Option.bind]
      dsimp only
      have hmap := Input.executableLocalizedRerootChildren_map cursor
      rw [intended_eq0 cursor h] at hmap
      by_cases hnil : Input.executableLocalizedRerootChildren cursor = []
      · have : intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val) = [] := by
          rw [← hmap, hnil]; rfl
        rw [if_pos hnil, if_pos (List.isEmpty_iff.2 this)]
        rfl

      · have : intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val) ≠ [] := by
          rw [← hmap]; simpa using hnil
        rw [if_neg hnil, if_neg (fun e => this (List.isEmpty_iff.1 e))]
  | fuel + 1, cursor, h => by
      rw [buildLocalizedRerootCumulativeRule45KeyWithRead?,
        Input.localizedRerootChildren?_eq_some_executable, buildF]
      change Option.bind (some _) _ = _
      rw [Option.bind]
      dsimp only
      have hmap := Input.executableLocalizedRerootChildren_map cursor
      rw [intended_eq0 cursor h] at hmap
      by_cases hnil : Input.executableLocalizedRerootChildren cursor = []
      · have : intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val) = [] := by
          rw [← hmap, hnil]; rfl
        rw [if_pos hnil, if_pos (List.isEmpty_iff.2 this)]
        rfl
      · have hne : intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val) ≠ [] := by
          rw [← hmap]; simpa using hnil
        have hchildren :
            (Input.executableLocalizedRerootChildren cursor).mapM
                (Input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage readT fuel) =
              (intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val)).mapM
                (fun child => buildF stage fuel child (some cursor.occurrence.1)) := by
          rw [← hmap, mapM_map']
          apply mapM_congr_mem
          intro child hchild
          have hprev := Input.executableLocalizedRerootChildren_previous cursor child hchild
          have hroot : child.occurrence.1.root = SA 0 := by
            apply subtree0_root
            apply mem_subtree0_of_mem_intendedPair0
            rw [← hmap]
            exact List.mem_map_of_mem hchild
          rw [build_eq stage fuel child hroot, hprev]
          rfl
        rw [if_neg hnil, if_neg (fun e => hne (List.isEmpty_iff.1 e)), hchildren]
        rfl

/-! ## Reader-aware root-component twin for the current rule-major builder

Unlike `buildF`, this twin uses the production rule-major sibling sorter at every
stage.  A caller supplies the actual value of the reader at each finite component
frame; `buildRuleMajor_eq` then transfers it to the real cursor evaluator.
-/

private def ruleMajorTerminalFrameKey (stage : LocalizedCumulativeRule45Stage)
    (frame : Frame) (label : Option Label) : Key :=
  { constitutional := Input.moleculeGraph.officialRuleMajorRootKey frame.node true
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
    labels := [[([], label)]]
    rankedLabels := [[([], label)]] }

private def ruleMajorStepFrameKey (stage : LocalizedCumulativeRule45Stage)
    (frame : Frame) (label : Option Label) (sorted : List Key) : Key :=
  { constitutional := OfficialRuleMajorKey.assemble
      (Input.moleculeGraph.officialRuleMajorRootKey frame.node false)
      (sorted.map fun child => child.constitutional)
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
      Input.mergeLocalizedRerootDescriptorChildren sorted
    labels := [[([], label)]] ++ Input.mergeLocalizedRerootLabelChildren sorted
    rankedLabels := [[([], label)]] ++ Input.mergeLocalizedRerootRankedLabelChildren sorted }

def buildRuleMajorF (stage : LocalizedCumulativeRule45Stage)
    (readFrame : Frame → Option Label) :
    Nat → Frame → Option Frame → Option Key
  | 0, frame, previous? =>
      let children := intendedPair0 frame previous?
      if children.isEmpty then
        some (ruleMajorTerminalFrameKey stage frame (readFrame frame))
      else none
  | fuel + 1, frame, previous? =>
      let children := intendedPair0 frame previous?
      if children.isEmpty then
        some (ruleMajorTerminalFrameKey stage frame (readFrame frame))
      else
        (children.mapM (fun child => buildRuleMajorF stage readFrame fuel child (some frame))).bind
          fun childKeys =>
            some (ruleMajorStepFrameKey stage frame (readFrame frame)
              (Input.sortRuleMajorCumulativeKeys stage childKeys))

theorem buildRuleMajorF_eq_actual
    (stage : LocalizedCumulativeRule45Stage)
    (readFrame : Frame → Option Label)
    (read : Cursor → Option Label)
    (readAgreement : ∀ cursor, cursor.occurrence.1.root = SA 0 →
      read cursor = readFrame cursor.occurrence.1) :
    ∀ fuel (cursor : Cursor), cursor.occurrence.1.root = SA 0 →
      Input.buildRuleMajorCumulativeWithRead? stage read fuel cursor =
        buildRuleMajorF stage readFrame fuel cursor.occurrence.1
          (cursor.previous?.map Subtype.val) := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor rootEq
      simp only [CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?]
      rw [Input.localizedRerootChildren?_eq_some_executable]
      have mapped := Input.executableLocalizedRerootChildren_map cursor
      rw [intended_eq0 cursor rootEq] at mapped
      rw [buildRuleMajorF]
      by_cases hnil : intendedPair0 cursor.occurrence.1
          (cursor.previous?.map Subtype.val) = []
      · change intendedPair0 cursor.occurrence.1
          cursor.previous?.unattach = [] at hnil
        have actualNil : Input.executableLocalizedRerootChildren cursor = [] := by
          have := congrArg List.length mapped
          have len : (Input.executableLocalizedRerootChildren cursor).length = 0 := by
            simpa [hnil] using this
          exact List.eq_nil_iff_length_eq_zero.mpr len
        simp [actualNil, hnil, readAgreement cursor rootEq,
          ruleMajorTerminalFrameKey]
      · have actualNe : Input.executableLocalizedRerootChildren cursor ≠ [] := by
          change ¬ intendedPair0 cursor.occurrence.1
            cursor.previous?.unattach = [] at hnil
          intro e
          have := congrArg List.length mapped
          rw [e] at this
          have empty : intendedPair0 cursor.occurrence.1
              cursor.previous?.unattach = [] := by
            exact List.eq_nil_iff_length_eq_zero.mpr this.symm
          exact hnil empty
        have hnil' : intendedPair0 cursor.occurrence.1
            cursor.previous?.unattach ≠ [] := by simpa using hnil
        simp [actualNe, hnil']
  | succ fuel ih =>
      intro cursor rootEq
      simp only [CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?]
      rw [Input.localizedRerootChildren?_eq_some_executable]
      have mapped := Input.executableLocalizedRerootChildren_map cursor
      rw [intended_eq0 cursor rootEq] at mapped
      rw [buildRuleMajorF]
      by_cases hnil : intendedPair0 cursor.occurrence.1
          (cursor.previous?.map Subtype.val) = []
      · change intendedPair0 cursor.occurrence.1
          cursor.previous?.unattach = [] at hnil
        have actualNil : Input.executableLocalizedRerootChildren cursor = [] := by
          have := congrArg List.length mapped
          have len : (Input.executableLocalizedRerootChildren cursor).length = 0 := by
            simpa [hnil] using this
          exact List.eq_nil_iff_length_eq_zero.mpr len
        simp [actualNil, hnil, readAgreement cursor rootEq,
          ruleMajorTerminalFrameKey]
      · have actualNe : Input.executableLocalizedRerootChildren cursor ≠ [] := by
          change ¬ intendedPair0 cursor.occurrence.1
            cursor.previous?.unattach = [] at hnil
          intro e
          have := congrArg List.length mapped
          rw [e] at this
          have empty : intendedPair0 cursor.occurrence.1
              cursor.previous?.unattach = [] := by
            exact List.eq_nil_iff_length_eq_zero.mpr this.symm
          exact hnil empty
        have hnil' : intendedPair0 cursor.occurrence.1
            cursor.previous?.unattach ≠ [] := by simpa using hnil
        have childrenEq :
            (Input.executableLocalizedRerootChildren cursor).mapM
                (Input.buildRuleMajorCumulativeWithRead? stage read fuel) =
              (intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val)).mapM
                (fun child => buildRuleMajorF stage readFrame fuel child
                  (some cursor.occurrence.1)) := by
          rw [← mapped, mapM_map']
          apply mapM_congr_mem
          intro child childMem
          have childRoot : child.occurrence.1.root = SA 0 := by
            apply subtree0_root
            apply mem_subtree0_of_mem_intendedPair0
            rw [← mapped]
            exact List.mem_map_of_mem childMem
          have childIH := ih child childRoot
          rw [Input.executableLocalizedRerootChildren_previous cursor child childMem] at childIH
          simpa using childIH
        simp [actualNe, hnil', childrenEq, ruleMajorStepFrameKey,
          readAgreement cursor rootEq]
        unfold localizedCumulativeRule45StepKey
        rfl

/-! ## Concrete root-0 frames -/

def rootNode : OfficialCIPNode Atom := OfficialCIPNode.root (SA 0)
def node2 : OfficialCIPNode Atom := rootNode.extend (SA 2) 0
def node4 : OfficialCIPNode Atom := rootNode.extend (SA 4) 0
def node24 : OfficialCIPNode Atom := node2.extend (SA 4) 0
def node42 : OfficialCIPNode Atom := node4.extend (SA 2) 0

def rootF : Frame :=
  { root := SA 0, address := [], node := rootNode, remaining := Fuel + 1 }
def rootFluorineF : Frame :=
  { root := SA 0, address := [0], node := rootNode.extend (SA 1) 0, remaining := Fuel }
def armF : Frame :=
  { root := SA 0, address := [1], node := node2, remaining := Fuel }
def closeF : Frame :=
  { root := SA 0, address := [2], node := node4, remaining := Fuel }
def rootHydrogenF : Frame :=
  { root := SA 0, address := [3], node := rootNode.extend (SA 5) 0, remaining := Fuel }
def via24F : Frame :=
  { root := SA 0, address := [1, 1], node := node24, remaining := Fuel - 1 }
def via42F : Frame :=
  { root := SA 0, address := [2, 0], node := node42, remaining := Fuel - 1 }

def armClF : Frame :=
  { root := SA 0, address := [1, 0], node := node2.extend (SA 3) 0, remaining := Fuel - 1 }
def armHF : Frame :=
  { root := SA 0, address := [1, 2], node := node2.extend (SA 6) 0, remaining := Fuel - 1 }
def closeClF : Frame :=
  { root := SA 0, address := [2, 2], node := node4.extend (SA 8) 0, remaining := Fuel - 1 }
def closeHF : Frame :=
  { root := SA 0, address := [2, 1], node := node4.extend (SA 7) 0, remaining := Fuel - 1 }
def via24ClF : Frame :=
  { root := SA 0, address := [1, 1, 2], node := node24.extend (SA 8) 0, remaining := Fuel - 2 }
def via24DupF : Frame :=
  { root := SA 0, address := [1, 1, 0], node := node24.extend (SA 0) 0, remaining := Fuel - 2 }
def via24HF : Frame :=
  { root := SA 0, address := [1, 1, 1], node := node24.extend (SA 7) 0, remaining := Fuel - 2 }
def via42ClF : Frame :=
  { root := SA 0, address := [2, 0, 1], node := node42.extend (SA 3) 0, remaining := Fuel - 2 }
def via42DupF : Frame :=
  { root := SA 0, address := [2, 0, 0], node := node42.extend (SA 0) 0, remaining := Fuel - 2 }
def via42HF : Frame :=
  { root := SA 0, address := [2, 0, 2], node := node42.extend (SA 6) 0, remaining := Fuel - 2 }

def evalFuel : Nat := 2 * (Fuel + 1)

theorem rootNeighborFrames_eq :
    neighborFrames0 rootF = [rootFluorineF, armF, closeF, rootHydrogenF] := by
  decide +kernel

def constKey (frame previous : Frame) : Option (OfficialRuleMajorKey Atom) :=
  (buildF .rule4a evalFuel frame (some previous)).map fun key => key.constitutional

def decidedGt (left right previous : Frame) : Bool :=
  match constKey left previous, constKey right previous with
  | some keyL, some keyR => OfficialRuleMajorKey.compare keyL keyR == Ordering.gt
  | _, _ => false

theorem root_arm_close_const_non_gt :
    decidedGt armF closeF rootF = false ∧ decidedGt closeF armF rootF = false := by
  decide +kernel

theorem root_arm_close_const_tie_bool :
    (match constKey armF rootF, constKey closeF rootF with
      | some left, some right =>
          OfficialRuleMajorKey.compare left right == Ordering.eq
      | _, _ => false) = true := by
  decide +kernel

theorem direct_arm_const_order :
    decidedGt armClF via24F armF && decidedGt armClF rootF armF &&
      decidedGt armClF armHF armF && decidedGt via24F rootF armF &&
      decidedGt via24F armHF armF && decidedGt rootF armHF armF = true := by
  decide +kernel

theorem direct_closing_const_order :
    decidedGt closeClF via42F closeF && decidedGt closeClF rootF closeF &&
      decidedGt closeClF closeHF closeF && decidedGt via42F rootF closeF &&
      decidedGt via42F closeHF closeF && decidedGt rootF closeHF closeF = true := by
  decide +kernel

theorem via_arm_const_order :
    decidedGt via24ClF armF via24F && decidedGt via24ClF via24DupF via24F &&
      decidedGt via24ClF via24HF via24F && decidedGt armF via24DupF via24F &&
      decidedGt armF via24HF via24F && decidedGt via24DupF via24HF via24F = true := by
  decide +kernel

theorem via_closing_const_order :
    decidedGt via42ClF closeF via42F && decidedGt via42ClF via42DupF via42F &&
      decidedGt via42ClF via42HF via42F && decidedGt closeF via42DupF via42F &&
      decidedGt closeF via42HF via42F && decidedGt via42DupF via42HF via42F = true := by
  decide +kernel

/-! ## Concrete auxiliary reader

The reader below decides only root, depth, provenance and the final atom of the molecular unit.
It names no occurrence unit and no classical choice. Its agreement with the generated-map reader
on `subtree0` is a theorem of `LocalizedCyclicPseudoActualEvaluation`; it is not assumed here. -/

/-- A real strict-depth occurrence whose molecular unit ends at atom 2 reads `R`; one ending at
atom 4 reads `S`; every other frame reads nothing. -/
def concreteReadFrame (frame : Frame) : Option Label :=
  if frame.root = SA 0 ∧ 0 < frame.address.length then
    if frame.node.provenance = OfficialCIPNodeProvenance.realAtom then
      if (pseudoSpatialCertified.molecularFrameUnit frame).atom = SA 2 then
        some (.chiral RS.R : Label)
      else if (pseudoSpatialCertified.molecularFrameUnit frame).atom = SA 4 then
        some (.chiral RS.S : Label)
      else none
    else none
  else none

/-- Readers that agree on the finite root-zero tree build the same rule-major stage key from any
frame of that tree. -/
theorem buildRuleMajorF_congr (stage : LocalizedCumulativeRule45Stage)
    (left right : Frame → Option Label)
    (agree : ∀ frame ∈ subtree0, left frame = right frame) (fuel : Nat) :
    ∀ (frame : Frame) (previous? : Option Frame), frame ∈ subtree0 →
      buildRuleMajorF stage left fuel frame previous? =
        buildRuleMajorF stage right fuel frame previous? := by
  induction fuel with
  | zero =>
      intro frame previous? member
      simp only [buildRuleMajorF, agree frame member]
  | succ fuel ih =>
      intro frame previous? member
      have children :
          (intendedPair0 frame previous?).mapM
              (fun child => buildRuleMajorF stage left fuel child (some frame)) =
            (intendedPair0 frame previous?).mapM
              (fun child => buildRuleMajorF stage right fuel child (some frame)) :=
        mapM_congr_mem _ _ _ fun child childMem =>
          ih child (some frame) (mem_subtree0_of_mem_intendedPair0 childMem)
      simp only [buildRuleMajorF, agree frame member, children]

/-- The four root ligand frames belong to the root-zero tree. -/
theorem rootLigandFrames_mem_subtree0 :
    rootFluorineF ∈ subtree0 ∧ armF ∈ subtree0 ∧ closeF ∈ subtree0 ∧
      rootHydrogenF ∈ subtree0 := by
  decide +kernel

end TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.neighborSort_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.subtree0_nodup
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.build_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.subtree0_centerAddressCheck_all
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF_eq_actual
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.rootNeighborFrames_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.direct_arm_const_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.direct_closing_const_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.via_arm_const_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.via_closing_const_order
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.concreteReadFrame
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF_congr
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation.rootLigandFrames_mem_subtree0
