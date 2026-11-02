import TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance
import TetraStereo.Examples.TwoReferenceSupport.FixturePhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

































namespace TetraStereo.OneCenter
namespace LocalizedTwoReferenceFixtureRootLetter

open CertifiedLocalizedCIPInput
open RootedTetrahedralBranchSymmetry
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance
open FixtureOccurrences
open Rule4aTableBridge (ActualCentrePhysicalSetup)

abbrev Input := input.certified
abbrev Atom := input.certified.Atom
abbrev Frame := Input.LocalizedCIPOccurrenceFrame
abbrev Fuel := LocalizedUniversalReference.carrierFuel input
abbrev Cursor := Input.LocalizedRerootCursor Fuel
abbrev Key := Input.LocalizedRerootCumulativeRule45Key
abbrev Label := LocalizedAuxiliaryLabel

/-! ## Generic list facts -/

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

/-! ## Kernel twins of the occurrence carrier

The executable official enumeration sorts neighbor finsets, which the kernel does not unfold.
The accepted `FixtureOccurrences.neighborSort_eq` gives the exact sorted neighbor table of
every atom; the twins below are the production definitions with that table substituted. -/

/-- The accepted exact neighbor table as a function. -/
def neighborsOf (a : Atom) : List Atom :=
  match a.val with
  | 0 => [atom1, atom2, atom3, atom18]
  | 1 => [atom0]
  | 2 => [atom0]
  | 3 => [atom0, atom4, atom11]
  | 4 => [atom3, atom5, atom6, atom7]
  | 5 => [atom4]
  | 6 => [atom4]
  | 7 => [atom4, atom8, atom9, atom10]
  | 8 => [atom7]
  | 9 => [atom7]
  | 10 => [atom7]
  | 11 => [atom3, atom12, atom13, atom14]
  | 12 => [atom11]
  | 13 => [atom11]
  | 14 => [atom11, atom15, atom16, atom17]
  | 15 => [atom14]
  | 16 => [atom14]
  | 17 => [atom14]
  | 18 => [atom0, atom19, atom26]
  | 19 => [atom18, atom20, atom21, atom22]
  | 20 => [atom19]
  | 21 => [atom19]
  | 22 => [atom19, atom23, atom24, atom25]
  | 23 => [atom22]
  | 24 => [atom22]
  | 25 => [atom22]
  | 26 => [atom18, atom27, atom28, atom29]
  | 27 => [atom26]
  | 28 => [atom26]
  | 29 => [atom26, atom30, atom31, atom32]
  | 30 => [atom29]
  | 31 => [atom29]
  | _ => [atom29]

theorem neighborSort_eq' (a : Atom) :
    (Input.moleculeGraph.neighborFinset a).sort (· ≤ ·) = neighborsOf a :=
  FixtureOccurrences.neighborSort_eq a

def neighborCopiesT (atom : Atom) : List (Atom × ℕ) :=
  (neighborsOf atom).flatMap fun neighbor =>
    (List.range (Input.moleculeGraph.bond atom neighbor)).map fun copyIndex =>
      (neighbor, copyIndex)

theorem neighborCopies_eq (atom : Atom) :
    Input.executableOfficialNeighborCopies atom = neighborCopiesT atom := by
  unfold CertifiedLocalizedCIPInput.executableOfficialNeighborCopies neighborCopiesT
  rw [neighborSort_eq']

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
  unfold CertifiedLocalizedCIPInput.executableOfficialChildCopies childCopiesT
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
  unfold CertifiedLocalizedCIPInput.executableOfficialCIPChildren childrenT
  rw [childCopies_eq]

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
      rw [CertifiedLocalizedCIPInput.localizedOccurrenceSubtree, subtreeT, children_eq]
      congr 1
      congr 1
      funext child
      exact subtree_eq root fuel _ _

theorem subtreeT_root (a : Atom) :
    ∀ (fuel : Nat) (path : List Nat) (node : OfficialCIPNode Atom),
      ∀ f ∈ subtreeT a fuel path node, f.root = a
  | 0, path, node, f, hf => by
      simp only [subtreeT, List.mem_singleton] at hf
      rw [hf]
  | fuel + 1, path, node, f, hf => by
      simp only [subtreeT, List.mem_cons, List.mem_flatMap] at hf
      rcases hf with rfl | ⟨child, _, hchild⟩
      · rfl
      · exact subtreeT_root a fuel _ _ f hchild

/-- The carrier before duplicate removal. -/
def carrierRaw (fuel : Nat) : List Frame :=
  (List.finRange Input.certified.input.molecule.atomCount).flatMap fun a =>
    subtreeT a (fuel + 1) [] (OfficialCIPNode.root a)

theorem carrier_eq (fuel : Nat) : Input.localizedOccurrences fuel = (carrierRaw fuel).dedup := by
  unfold CertifiedLocalizedCIPInput.localizedOccurrences
    CertifiedLocalizedCIPInput.localizedOccurrencesAtAtom carrierRaw
  simp only [subtree_eq]

/-! ## The root-0 component of the carrier -/

/-- The official expansion from the root atom: the only part of the carrier an arm of the root
ever consults. -/
def subtree0 : List Frame := subtreeT atom0 (Fuel + 1) [] (OfficialCIPNode.root atom0)

theorem subtree0_nodup : subtree0.Nodup := by decide +kernel

theorem subtree0_root : ∀ f ∈ subtree0, f.root = atom0 := subtreeT_root atom0 _ _ _

theorem carrierRaw_filter0 (p : Frame → Bool) (hp : ∀ c, p c = true → c.root = atom0) :
    (carrierRaw Fuel).filter p = subtree0.filter p := by
  unfold carrierRaw
  rw [List.filter_flatMap]
  exact flatMap_eq_single _ atom0 _ (List.nodup_finRange _) (List.mem_finRange _)
    (fun x _ hx => List.filter_eq_nil_iff.2 fun f hf hpf =>
      hx ((subtreeT_root x _ _ _ f hf).symm.trans (hp f hpf)))

/-- Any root-0 filter of the carrier is the same filter of the root-0 component. -/
theorem carrier_filter0 (p : Frame → Bool) (hp : ∀ c, p c = true → c.root = atom0) :
    (Input.localizedOccurrences Fuel).filter p = subtree0.filter p := by
  rw [carrier_eq, filter_dedup, carrierRaw_filter0 p hp,
    List.dedup_eq_self.2 (subtree0_nodup.filter p)]

theorem mem_carrier_of_mem_subtree0 {f : Frame} (hf : f ∈ subtree0) :
    f ∈ Input.localizedOccurrences Fuel := by
  rw [carrier_eq, List.mem_dedup]
  exact List.mem_flatMap.2 ⟨atom0, List.mem_finRange _, hf⟩

theorem mem_subtree0_of_mem_carrier {f : Frame} (hf : f ∈ Input.localizedOccurrences Fuel)
    (hroot : f.root = atom0) : f ∈ subtree0 := by
  have h : f ∈ (Input.localizedOccurrences Fuel).filter (fun c => c.root == atom0) :=
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

def neighborFrames0 (frame : Frame) : List Frame := parentFrames0 frame ++ outward0 frame

theorem root_of_pred {frame candidate : Frame} (h : frame.root = atom0) {P : Prop}
    (hc : candidate.root = frame.root ∧ P) : candidate.root = atom0 :=
  hc.1.trans h

theorem neighborFrames_eq0 (frame : Frame) (h : frame.root = atom0) :
    Input.localizedRerootNeighborFrames (fuel := Fuel) frame = neighborFrames0 frame := by
  unfold CertifiedLocalizedCIPInput.localizedRerootNeighborFrames
    CertifiedLocalizedCIPInput.localizedCarrierParentFrames
    CertifiedLocalizedCIPInput.localizedCarrierOutwardChildFrames
    neighborFrames0 parentFrames0 outward0
  rw [carrier_filter0 _ (fun c hc => root_of_pred h (by simpa [and_assoc] using hc)),
    carrier_filter0 _ (fun c hc => root_of_pred h (by simpa [and_assoc] using hc))]

/-- The intended child frames of a cursor, from its frame and its incoming cut. -/
def intendedPair0 (frame : Frame) (previous? : Option Frame) : List Frame :=
  if frame.node.isDuplicateLeaf then []
  else
    match previous? with
    | none => neighborFrames0 frame
    | some previous =>
        (neighborFrames0 frame).filter fun candidate =>
          candidate.address != previous.address

theorem intended_eq0 (cursor : Cursor) (h : cursor.occurrence.1.root = atom0) :
    Input.intendedLocalizedRerootChildFrames cursor =
      intendedPair0 cursor.occurrence.1 (cursor.previous?.map Subtype.val) := by
  unfold CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames intendedPair0
  cases cursor.previous? <;>
    simp only [neighborFrames_eq0 _ h, Option.map_none, Option.map_some]

theorem mem_subtree0_of_mem_intendedPair0 {frame : Frame} {previous? : Option Frame} {f : Frame}
    (hf : f ∈ intendedPair0 frame previous?) : f ∈ subtree0 := by
  unfold intendedPair0 at hf
  split at hf
  · simp at hf
  · cases previous? with
    | none =>
      simp only [neighborFrames0, parentFrames0, outward0, List.mem_append, List.mem_filter] at hf
      rcases hf with h | h <;> exact h.1
    | some previous =>
      simp only [neighborFrames0, parentFrames0, outward0, List.mem_filter, List.mem_append] at hf
      rcases hf.1 with h | h <;> exact h.1

/-! ## The concrete reader

The setup's reader is the molecular reader over the actual descriptor map.  Its values at the
root's arms are the eight derived map entries of the physical instance; `mapT` is that table. -/

def eightUnits : List (DeclarativeCIP.OccurrenceUnit Atom) :=
  [⟨atom0, [atom3, atom4]⟩, ⟨atom0, [atom3, atom11]⟩, ⟨atom0, [atom18, atom19]⟩,
    ⟨atom0, [atom18, atom26]⟩, ⟨atom0, [atom3, atom4, atom7]⟩, ⟨atom0, [atom3, atom11, atom14]⟩,
    ⟨atom0, [atom18, atom19, atom22]⟩, ⟨atom0, [atom18, atom26, atom29]⟩]

def mapT (u : DeclarativeCIP.OccurrenceUnit Atom) : Option DeclarativeCIP.Descriptor :=
  if u = ⟨atom0, [atom3, atom4]⟩ then some .R
  else if u = ⟨atom0, [atom3, atom11]⟩ then some .S
  else if u = ⟨atom0, [atom18, atom19]⟩ then some .S
  else if u = ⟨atom0, [atom18, atom26]⟩ then some .R
  else if u = ⟨atom0, [atom3, atom4, atom7]⟩ then some .R
  else if u = ⟨atom0, [atom3, atom11, atom14]⟩ then some .R
  else if u = ⟨atom0, [atom18, atom19, atom22]⟩ then some .S
  else if u = ⟨atom0, [atom18, atom26, atom29]⟩ then some .S
  else none

def readFrameT (f : Frame) : Option Label :=
  if f.root = atom0 ∧ 0 < f.address.length then
    if f.node.provenance = .realAtom then
      if DeclarativeCIP.IsDetectedCenter Input.moleculeGraph (Input.molecularFrameUnit f).atom then
        (mapT (Input.molecularFrameUnit f)).bind DeclarativeCIP.Descriptor.toLocalizedLabel
      else none
    else none
  else none

def readT (c : Cursor) : Option Label := readFrameT c.occurrence.1

/-! ## Frame-level kernel twin of the cumulative builder -/

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

/-- **The twin is the production builder** at the concrete reader, at every cursor rooted at the
root atom. -/
theorem build_eq (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (cursor : Cursor), cursor.occurrence.1.root = atom0 →
      Input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage readT fuel cursor =
        buildF stage fuel cursor.occurrence.1 (cursor.previous?.map Subtype.val)
  | 0, cursor, h => by
      rw [CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?,
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
      rw [CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?,
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
          have hroot : child.occurrence.1.root = atom0 := by
            apply subtree0_root
            apply mem_subtree0_of_mem_intendedPair0
            rw [← hmap]
            exact List.mem_map_of_mem hchild
          rw [build_eq stage fuel child hroot, hprev]
          rfl
        rw [if_neg hnil, if_neg (fun e => hne (List.isEmpty_iff.1 e)), hchildren]
        rfl

/-! ## The setup's reader is the concrete reader on the root's arms -/

noncomputable section

/-- The physical setup of the root (the physical instance's `setup`). -/
abbrev S : ActualCentrePhysicalSetup input := setup

/-- The setup's reader, at the frame level. -/
def readFrameActual (f : Frame) : Option Label :=
  if f.root = atom0 ∧ 0 < f.address.length then
    if f.node.provenance = .realAtom then
      if h : DeclarativeCIP.IsDetectedCenter Input.moleculeGraph
          (Input.molecularFrameUnit f).atom then
        (actualReferenceDescriptorMap input ⟨Input.molecularFrameUnit f, h⟩).bind
          DeclarativeCIP.Descriptor.toLocalizedLabel
      else none
    else none
  else none

theorem read_eq_readFrameActual (c : Cursor) : S.read c = readFrameActual c.occurrence.1 := by
  show Input.molecularReader (actualReferenceDescriptorMap input)
    (ActualReaderPhysicalBranchInverse.topTarget input rootP) c = _
  unfold CertifiedLocalizedCIPInput.molecularReader
    CertifiedLocalizedCIPInput.localizedDependencyLabel readFrameActual
  have hdep : Input.LocalizedDepthDependency c.occurrence
      (ActualReaderPhysicalBranchInverse.topTarget input rootP) ↔
        (c.occurrence.1.root = atom0 ∧ 0 < c.occurrence.1.address.length) := by
    unfold CertifiedLocalizedCIPInput.LocalizedDepthDependency
    rw [ActualReaderPhysicalBranchInverse.topTarget_root,
      ActualReaderPhysicalBranchInverse.topTarget_address]
    exact Iff.rfl
  by_cases h : c.occurrence.1.root = atom0 ∧ 0 < c.occurrence.1.address.length
  · rw [dif_pos (hdep.2 h), if_pos h]
    rfl
  · rw [dif_neg (fun d => h (hdep.1 d)), if_neg h]

/-- Every real-atom detected centre below the root in the root-0 component is one of the eight
molecular units of the physical instance. -/
theorem subtree0_centers :
    ∀ f ∈ subtree0, 0 < f.address.length → f.node.provenance = .realAtom →
      DeclarativeCIP.IsDetectedCenter Input.moleculeGraph (Input.molecularFrameUnit f).atom →
        Input.molecularFrameUnit f ∈ eightUnits := by
  decide +kernel

theorem map_eq_mapT (u : DeclarativeCIP.OccurrenceUnit Atom) (hu : u ∈ eightUnits)
    (h : DeclarativeCIP.IsDetectedCenter Input.moleculeGraph u.atom) :
    (actualReferenceDescriptorMap input ⟨u, h⟩).bind DeclarativeCIP.Descriptor.toLocalizedLabel =
      (mapT u).bind DeclarativeCIP.Descriptor.toLocalizedLabel := by
  simp only [eightUnits, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show _ = _ from mapLabel4).trans rfl
  · exact (show _ = _ from mapLabel11).trans rfl
  · exact (show _ = _ from mapLabel19).trans rfl
  · exact (show _ = _ from mapLabel26).trans rfl
  · exact (show _ = _ from mapLabel7).trans rfl
  · exact (show _ = _ from mapLabel14).trans rfl
  · exact (show _ = _ from mapLabel22).trans rfl
  · exact (show _ = _ from mapLabel29).trans rfl

/-- **Reader agreement.**  At every cursor rooted at the root atom, the setup's reader is the
concrete reader. -/
theorem read_eq_readT (c : Cursor) (hroot : c.occurrence.1.root = atom0) : S.read c = readT c := by
  rw [read_eq_readFrameActual]
  unfold readFrameActual readT readFrameT
  have hmem : c.occurrence.1 ∈ subtree0 := mem_subtree0_of_mem_carrier c.occurrence.2 hroot
  by_cases h1 : c.occurrence.1.root = atom0 ∧ 0 < c.occurrence.1.address.length
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : c.occurrence.1.node.provenance = .realAtom
    · rw [if_pos h2, if_pos h2]
      by_cases h3 : DeclarativeCIP.IsDetectedCenter Input.moleculeGraph
          (Input.molecularFrameUnit c.occurrence.1).atom
      · rw [dif_pos h3, if_pos h3]
        exact map_eq_mapT _ (subtree0_centers _ hmem h1.2 h2 h3) h3
      · rw [dif_neg h3, if_neg h3]
    · rw [if_neg h2, if_neg h2]
  · rw [if_neg h1, if_neg h1]

theorem root_of_reachable (start : Cursor) (hstart : start.occurrence.1.root = atom0) :
    ∀ c : Cursor, Relation.ReflTransGen (Input.E) start c → c.occurrence.1.root = atom0 := by
  intro c h
  induction h with
  | refl => exact hstart
  | @tail b c' _ hstep ih =>
    have hmem : c'.occurrence.1 ∈ Input.intendedLocalizedRerootChildFrames b := by
      rw [← Input.executableLocalizedRerootChildren_map]
      exact List.mem_map_of_mem hstep
    rw [intended_eq0 b ih] at hmem
    exact subtree0_root _ (mem_subtree0_of_mem_intendedPair0 hmem)

/-- **The production build at the setup's reader is the kernel twin**, at every cursor rooted at
the root atom. -/
theorem build_read_eq (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) (start : Cursor)
    (hstart : start.occurrence.1.root = atom0) :
    Input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage S.read fuel start =
      buildF stage fuel start.occurrence.1 (start.previous?.map Subtype.val) := by
  rw [Input.buildLocalizedRerootCumulativeRule45KeyWithRead?_congr_of_reachable stage S.read readT
    start (fun c hc => read_eq_readT c (root_of_reachable start hstart c hc)) fuel start
    Relation.ReflTransGen.refl]
  exact build_eq stage fuel start hstart

/-! ## The four ligand-root cursors of the root -/

def rootFrameT : Frame :=
  { root := atom0, address := [], node := OfficialCIPNode.root atom0, remaining := Fuel + 1 }

def ligandFrameT (slot : Nat) (ligand : Atom) : Frame :=
  { root := atom0, address := [slot], node := (OfficialCIPNode.root atom0).extend ligand 0,
    remaining := Fuel }

theorem ligandFrameT_mem_H : ligandFrameT 0 atom1 ∈ subtree0 := by decide +kernel
theorem ligandFrameT_mem_Cl : ligandFrameT 1 atom2 ∈ subtree0 := by decide +kernel
theorem ligandFrameT_mem_N3 : ligandFrameT 2 atom3 ∈ subtree0 := by decide +kernel
theorem ligandFrameT_mem_N18 : ligandFrameT 3 atom18 ∈ subtree0 := by decide +kernel
theorem rootFrameT_mem : rootFrameT ∈ subtree0 := by decide +kernel

def cursorH : Cursor :=
  { occurrence := ⟨_, mem_carrier_of_mem_subtree0 ligandFrameT_mem_H⟩
    previous? := some ⟨_, mem_carrier_of_mem_subtree0 rootFrameT_mem⟩ }
def cursorCl : Cursor :=
  { occurrence := ⟨_, mem_carrier_of_mem_subtree0 ligandFrameT_mem_Cl⟩
    previous? := some ⟨_, mem_carrier_of_mem_subtree0 rootFrameT_mem⟩ }
def cursorN3 : Cursor :=
  { occurrence := ⟨_, mem_carrier_of_mem_subtree0 ligandFrameT_mem_N3⟩
    previous? := some ⟨_, mem_carrier_of_mem_subtree0 rootFrameT_mem⟩ }
def cursorN18 : Cursor :=
  { occurrence := ⟨_, mem_carrier_of_mem_subtree0 ligandFrameT_mem_N18⟩
    previous? := some ⟨_, mem_carrier_of_mem_subtree0 rootFrameT_mem⟩ }

theorem ligandRootNode_zero :
    Input.localizedLigandRootNode S.center 0 = (OfficialCIPNode.root atom0).extend atom1 0 := by
  show (OfficialCIPNode.root atom0).extend
    (FixtureInventory.Input.canonicalLigandAtom FixtureRootGeometry.rootCenter 0) 0 = _
  rw [FixtureRootGeometry.canonicalLigandAtom_zero]
  rfl
theorem ligandRootNode_one :
    Input.localizedLigandRootNode S.center 1 = (OfficialCIPNode.root atom0).extend atom2 0 := by
  show (OfficialCIPNode.root atom0).extend
    (FixtureInventory.Input.canonicalLigandAtom FixtureRootGeometry.rootCenter 1) 0 = _
  rw [FixtureRootGeometry.canonicalLigandAtom_one]
  rfl
theorem ligandRootNode_two :
    Input.localizedLigandRootNode S.center 2 = (OfficialCIPNode.root atom0).extend atom3 0 := by
  show (OfficialCIPNode.root atom0).extend
    (FixtureInventory.Input.canonicalLigandAtom FixtureRootGeometry.rootCenter 2) 0 = _
  rw [FixtureRootGeometry.canonicalLigandAtom_two]
  rfl
theorem ligandRootNode_three :
    Input.localizedLigandRootNode S.center 3 = (OfficialCIPNode.root atom0).extend atom18 0 := by
  show (OfficialCIPNode.root atom0).extend
    (FixtureInventory.Input.canonicalLigandAtom FixtureRootGeometry.rootCenter 3) 0 = _
  rw [FixtureRootGeometry.canonicalLigandAtom_three]
  rfl

theorem rootChildren' :
    Input.executableOfficialCIPChildren (OfficialCIPNode.root atom0) =
      [(OfficialCIPNode.root atom0).extend atom1 0, (OfficialCIPNode.root atom0).extend atom2 0,
        (OfficialCIPNode.root atom0).extend atom3 0, (OfficialCIPNode.root atom0).extend atom18 0] :=
  FixtureOccurrences.rootChildren

theorem ligandRootSlot_zero : Input.localizedLigandRootSlot S.center 0 = 0 := by
  unfold CertifiedLocalizedCIPInput.localizedLigandRootSlot
  rw [ligandRootNode_zero]
  show List.idxOf _ (Input.executableOfficialCIPChildren (OfficialCIPNode.root atom0)) = 0
  rw [rootChildren']
  decide +kernel
theorem ligandRootSlot_one : Input.localizedLigandRootSlot S.center 1 = 1 := by
  unfold CertifiedLocalizedCIPInput.localizedLigandRootSlot
  rw [ligandRootNode_one]
  show List.idxOf _ (Input.executableOfficialCIPChildren (OfficialCIPNode.root atom0)) = 1
  rw [rootChildren']
  decide +kernel
theorem ligandRootSlot_two : Input.localizedLigandRootSlot S.center 2 = 2 := by
  unfold CertifiedLocalizedCIPInput.localizedLigandRootSlot
  rw [ligandRootNode_two]
  show List.idxOf _ (Input.executableOfficialCIPChildren (OfficialCIPNode.root atom0)) = 2
  rw [rootChildren']
  decide +kernel
theorem ligandRootSlot_three : Input.localizedLigandRootSlot S.center 3 = 3 := by
  unfold CertifiedLocalizedCIPInput.localizedLigandRootSlot
  rw [ligandRootNode_three]
  show List.idxOf _ (Input.executableOfficialCIPChildren (OfficialCIPNode.root atom0)) = 3
  rw [rootChildren']
  decide +kernel

theorem cursor_eq_of (k : Fin 4) (c : Cursor) (slot : Nat) (ligand : Atom)
    (hslot : Input.localizedLigandRootSlot S.center k = slot)
    (hnode : Input.localizedLigandRootNode S.center k = (OfficialCIPNode.root atom0).extend ligand 0)
    (hc : c.occurrence.1 = ligandFrameT slot ligand)
    (hprev : c.previous? = some ⟨rootFrameT, mem_carrier_of_mem_subtree0 rootFrameT_mem⟩) :
    Input.localizedLigandRootCursor S.center k = c := by
  apply LocalizedRerootCursor.ext
  · apply Subtype.ext
    rw [hc]
    apply LocalizedCIPOccurrenceFrame.ext
    · rfl
    · show [Input.localizedLigandRootSlot S.center k] = [slot]
      rw [hslot]
    · exact hnode
    · rfl
  · rw [hprev]
    exact congrArg some (Subtype.ext rfl)

theorem cursor_H : Input.localizedLigandRootCursor S.center 0 = cursorH :=
  cursor_eq_of 0 cursorH 0 atom1 ligandRootSlot_zero ligandRootNode_zero rfl rfl
theorem cursor_Cl : Input.localizedLigandRootCursor S.center 1 = cursorCl :=
  cursor_eq_of 1 cursorCl 1 atom2 ligandRootSlot_one ligandRootNode_one rfl rfl
theorem cursor_N3 : Input.localizedLigandRootCursor S.center 2 = cursorN3 :=
  cursor_eq_of 2 cursorN3 2 atom3 ligandRootSlot_two ligandRootNode_two rfl rfl
theorem cursor_N18 : Input.localizedLigandRootCursor S.center 3 = cursorN18 :=
  cursor_eq_of 3 cursorN18 3 atom18 ligandRootSlot_three ligandRootNode_three rfl rfl

/-! ## The actual arm keys are the twin's values -/

abbrev armFuel : Nat := 2 * (Fuel + 1)

theorem arm_key_eq {stage : LocalizedCumulativeRule45Stage} {k : Fin 4}
    (arm : Input.OriginalRootArm S.center k stage S.read) (c : Cursor)
    (hc : Input.localizedLigandRootCursor S.center k = c) (hroot : c.occurrence.1.root = atom0) :
    buildF stage armFuel c.occurrence.1 (c.previous?.map Subtype.val) = some arm.key := by
  rw [← build_read_eq stage armFuel c hroot, ← hc]
  exact arm.built

/-- The stage-`.rule4a` arms of the four ligands and the two stage-`.rule4b` arms of the N3 ligand
(the setup's own arms). -/
abbrev arm4a (k : Fin 4) := S.arm4a k
abbrev armR := S.arm4b 2 RS.R
abbrev armS := S.arm4b 2 RS.S

theorem key4a_H :
    buildF .rule4a armFuel (ligandFrameT 0 atom1) (some rootFrameT) = some (arm4a 0).key :=
  arm_key_eq (arm4a 0) cursorH cursor_H rfl
theorem key4a_Cl :
    buildF .rule4a armFuel (ligandFrameT 1 atom2) (some rootFrameT) = some (arm4a 1).key :=
  arm_key_eq (arm4a 1) cursorCl cursor_Cl rfl
theorem key4a_N3 :
    buildF .rule4a armFuel (ligandFrameT 2 atom3) (some rootFrameT) = some (arm4a 2).key :=
  arm_key_eq (arm4a 2) cursorN3 cursor_N3 rfl
theorem key4a_N18 :
    buildF .rule4a armFuel (ligandFrameT 3 atom18) (some rootFrameT) = some (arm4a 3).key :=
  arm_key_eq (arm4a 3) cursorN18 cursor_N18 rfl
theorem keyR_N3 :
    buildF (.rule4b .R) armFuel (ligandFrameT 2 atom3) (some rootFrameT) = some armR.key :=
  arm_key_eq armR cursorN3 cursor_N3 rfl
theorem keyS_N3 :
    buildF (.rule4b .S) armFuel (ligandFrameT 2 atom3) (some rootFrameT) = some armS.key :=
  arm_key_eq armS cursorN3 cursor_N3 rfl

/-! ## The finite facts, by kernel evaluation of the twin -/

theorem F_references :
    (buildF .rule4a armFuel (ligandFrameT 2 atom3) (some rootFrameT)).map
      (fun k => localizedRule4bReferencesFromRankedLabels k.rankedLabels) = some [RS.R, RS.S] := by
  decide +kernel

theorem F_headReading :
    (do
      let kR ← buildF (.rule4b .R) armFuel (ligandFrameT 2 atom3) (some rootFrameT)
      let kS ← buildF (.rule4b .S) armFuel (ligandFrameT 2 atom3) (some rootFrameT)
      pure (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        kR.descriptor kS.descriptor)) = some .gt := by
  decide +kernel

theorem F_firstChiral :
    (buildF (.rule4b .R) armFuel (ligandFrameT 2 atom3) (some rootFrameT)).map (fun k =>
      (SparsePhysicalFirstDifference.tableValue (Rule4aTableBridge.scalar4a k) [0],
        SparsePhysicalFirstDifference.tableValue (Rule4aTableBridge.scalar4b k) [0],
        SparsePhysicalFirstDifference.tableValue (Rule4aTableBridge.scalar4a k) [])) =
      some (2, 1, 0) := by
  decide +kernel

def compare4aT (a b : Frame) : Option Ordering := do
  let ka ← buildF .rule4a armFuel a (some rootFrameT)
  let kb ← buildF .rule4a armFuel b (some rootFrameT)
  pure (Input.compareLocalizedRerootCumulativeRule45Keys ka kb)

theorem F_H_lt_Cl : compare4aT (ligandFrameT 0 atom1) (ligandFrameT 1 atom2) = some .lt := by
  decide +kernel
theorem F_H_lt_N3 : compare4aT (ligandFrameT 0 atom1) (ligandFrameT 2 atom3) = some .lt := by
  decide +kernel
theorem F_H_lt_N18 : compare4aT (ligandFrameT 0 atom1) (ligandFrameT 3 atom18) = some .lt := by
  decide +kernel
theorem F_N3_lt_Cl : compare4aT (ligandFrameT 2 atom3) (ligandFrameT 1 atom2) = some .lt := by
  decide +kernel
theorem F_N18_lt_Cl : compare4aT (ligandFrameT 3 atom18) (ligandFrameT 1 atom2) = some .lt := by
  decide +kernel

/-! ## Transfer to the actual arm keys -/

theorem references_arm4a_N3 :
    localizedRule4bReferencesFromRankedLabels (arm4a 2).key.rankedLabels = [RS.R, RS.S] := by
  have h := F_references
  rw [key4a_N3] at h
  exact Option.some.inj h

theorem compare4b_R_S :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      armR.key.descriptor armS.key.descriptor = .gt := by
  have h := F_headReading
  rw [keyR_N3, keyS_N3] at h
  exact Option.some.inj h

theorem firstChiral_armR :
    SparsePhysicalFirstDifference.tableValue (Rule4aTableBridge.scalar4a armR.key) [0] = 2 ∧
      SparsePhysicalFirstDifference.tableValue (Rule4aTableBridge.scalar4b armR.key) [0] = 1 ∧
      SparsePhysicalFirstDifference.tableValue (Rule4aTableBridge.scalar4a armR.key) [] = 0 := by
  have h := F_firstChiral
  rw [keyR_N3] at h
  have h' := Option.some.inj h
  exact ⟨congrArg Prod.fst h', congrArg (fun p => p.2.1) h', congrArg (fun p => p.2.2) h'⟩

theorem compare4a_of {a b : Frame} {ka kb : Key}
    (ha : buildF .rule4a armFuel a (some rootFrameT) = some ka)
    (hb : buildF .rule4a armFuel b (some rootFrameT) = some kb)
    (h : compare4aT a b = some .lt) :
    Input.compareLocalizedRerootCumulativeRule45Keys ka kb = .lt := by
  unfold compare4aT at h
  rw [ha, hb] at h
  exact Option.some.inj h

theorem key4a_H_lt_Cl :
    Input.compareLocalizedRerootCumulativeRule45Keys (arm4a 0).key (arm4a 1).key = .lt :=
  compare4a_of key4a_H key4a_Cl F_H_lt_Cl
theorem key4a_H_lt_N3 :
    Input.compareLocalizedRerootCumulativeRule45Keys (arm4a 0).key (arm4a 2).key = .lt :=
  compare4a_of key4a_H key4a_N3 F_H_lt_N3
theorem key4a_H_lt_N18 :
    Input.compareLocalizedRerootCumulativeRule45Keys (arm4a 0).key (arm4a 3).key = .lt :=
  compare4a_of key4a_H key4a_N18 F_H_lt_N18
theorem key4a_N3_lt_Cl :
    Input.compareLocalizedRerootCumulativeRule45Keys (arm4a 2).key (arm4a 1).key = .lt :=
  compare4a_of key4a_N3 key4a_Cl F_N3_lt_Cl
theorem key4a_N18_lt_Cl :
    Input.compareLocalizedRerootCumulativeRule45Keys (arm4a 3).key (arm4a 1).key = .lt :=
  compare4a_of key4a_N18 key4a_Cl F_N18_lt_Cl

/-! ## The independent keys of the non-tied slots -/

theorem independentKey_lt_of {k m : Fin 4}
    (h : Input.compareLocalizedRerootCumulativeRule45Keys (arm4a k).key (arm4a m).key = .lt) :
    S.independentKey k < S.independentKey m := by
  rw [← S.independentCompare_eq_lt_iff]
  unfold ActualCentrePhysicalSetup.independentCompare
  rw [S.rule4aKey_eq (arm4a k), S.rule4aKey_eq (arm4a m), h]
  rfl

theorem indKey_H_lt_Cl : S.independentKey 0 < S.independentKey 1 := independentKey_lt_of key4a_H_lt_Cl
theorem indKey_H_lt_N3 : S.independentKey 0 < S.independentKey 2 := independentKey_lt_of key4a_H_lt_N3
theorem indKey_H_lt_N18 : S.independentKey 0 < S.independentKey 3 :=
  independentKey_lt_of key4a_H_lt_N18
theorem indKey_N3_lt_Cl : S.independentKey 2 < S.independentKey 1 := independentKey_lt_of key4a_N3_lt_Cl
theorem indKey_N18_lt_Cl : S.independentKey 3 < S.independentKey 1 :=
  independentKey_lt_of key4a_N18_lt_Cl

/-! ## The N3 slot: both references, and the `R`-reading heads the outcome order -/

theorem references_N3 : (S.slotKey 2).prior.references = [RS.R, RS.S] := by
  have h := (Rule4aTableBridge.compound_built_components _ _ _ _ (S.prior_built 2)).2.1
  rw [h, S.rule4aKey_eq (arm4a 2)]
  exact references_arm4a_N3

theorem selection_both : S.selection (arm4a 2) = .both := by
  have h := S.references_eq (arm4a 2)
  rw [references_N3] at h
  rcases hsel : S.selection (arm4a 2) with _ | ⟨_ | _⟩ | _
  · rw [hsel] at h; cases h
  · rw [hsel] at h; cases h
  · rw [hsel] at h; cases h
  · rfl

theorem readings_N3 :
    ∃ r s : Input.LocalizedRerootRule4bcReading,
      (S.slotKey 2).prior.readings = [r, s] ∧ r.reference? = some RS.R ∧
        s.reference? = some RS.S ∧ r.rule4bKey = armR.key ∧ s.rule4bKey = armS.key := by
  have h := S.readings_shape (arm4a 2) armR armS
  rw [selection_both] at h
  exact h

theorem complete_gt {r s : Input.LocalizedRerootRule4bcReading}
    (hr : r.rule4bKey = armR.key) (hs : s.rule4bKey = armS.key) :
    Input.compareRule4bcReadingsComplete r s = .gt := by
  have h4b : Input.compareLocalizedRerootRule4bcReadingsByRule4b r s = .gt := by
    show OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      r.rule4bKey.descriptor s.rule4bKey.descriptor = .gt
    rw [hr, hs]
    exact compare4b_R_S
  unfold CertifiedLocalizedCIPInput.compareRule4bcReadingsComplete
  rw [ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _ (by rw [h4b]; decide), h4b]

/-- The head of the N3 slot's outcome-ordered Rule-5 readings is its `R`-reading. -/
theorem head_N3 :
    ∃ (u : Input.LocalizedRerootRule5Reading) (tail : List Input.LocalizedRerootRule5Reading),
      (orderedKeys Input S.frameKey (S.slot 2)).rule5Readings = u :: tail ∧
        u.prior.reference? = some RS.R := by
  obtain ⟨r, s, hreadings, hr, hs, hr4b, hs4b⟩ := readings_N3
  have hmap := (S.frameKey_readings (S.slot 2)).1
  rw [← S.slotKey_eq_frameKey, hreadings] at hmap
  obtain ⟨u₁, rest, hcons, hu₁, hrest⟩ := List.map_eq_cons_iff.1 hmap
  obtain ⟨u₂, rest', hcons', hu₂, hrest'⟩ := List.map_eq_cons_iff.1 hrest
  rw [List.map_eq_nil_iff] at hrest'
  subst hrest'
  have hkey : (S.slotKey 2).rule5Readings = [u₁, u₂] := by rw [hcons, hcons']
  refine ⟨u₁, [u₂], ?_, ?_⟩
  · show Input.rankRule5Readings (S.slotKey 2).rule5Readings = _
    rw [hkey]
    show (if Input.compareRule4bcReadingsComplete u₁.prior u₂.prior = .lt then [u₂, u₁]
      else [u₁, u₂]) = _
    rw [hu₁, hu₂, if_neg (by rw [complete_gt hr4b hs4b]; decide)]
  · rw [hu₁, hr]

/-! ## The mirror pair at the root -/

theorem slotEquiv_symm_slot (k : Fin 4) : S.slotEquiv.symm (S.slot k) = k := by
  have : S.slotEquiv k = S.slot k := rfl
  rw [← this, Equiv.symm_apply_apply]

theorem alpha_slot (k : Fin 4) :
    S.alpha (S.slot k) = (Input.canonicalLigandReindex rootP)⁻¹ k := by
  apply Physical.ligandAtomAt_injective rootP
  have h1 := S.slotSpec (S.slot k)
  rw [S.cursorAt_slot] at h1
  have h2 : Physical.ligandAtomAt rootP ((Input.canonicalLigandReindex rootP)⁻¹ k) =
      Input.canonicalLigandAtom rootP k := by
    rw [Input.canonicalLigandReindex_spec]
    simp
  have h3 : Input.canonicalLigandAtom rootP k = Input.canonicalLigandAtom S.center k := rfl
  rw [h2, h3]
  exact Option.some.inj h1.symm

theorem enantiomorphic_N :
    Enantiomorphic Physical cfg rootP (S.alpha (S.slot 2)) (S.alpha (S.slot 3)) := by
  rw [alpha_slot 2, alpha_slot 3]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := (Input.canonicalLigandReindex rootP)⁻¹.injective h
    exact absurd this (by decide)
  · exact FixturePhysicalTransport.mirrorTransport_actual_root
  · exact FixturePhysicalTransport.pairwiseProperDistinguishable_actual_root _ _ (by
      intro h
      have := (Input.canonicalLigandReindex rootP)⁻¹.injective h
      exact absurd this (by decide))

theorem slot_ne : S.slot 2 ≠ S.slot 3 := S.slot_injective.ne (by decide)

/-- The accepted pairwise proper-distinguishability of the root's branches. -/
theorem distinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport Physical cfg rootP i j :=
  FixturePhysicalTransport.pairwiseProperDistinguishable_actual_root

theorem tie_N : priorKeyTie Input (orderedKeys Input S.frameKey) (S.slot 2) (S.slot 3) :=
  ((S.orderedPriorTie_iff_enantiomorphic distinct (S.slot 2) (S.slot 3)).2 enantiomorphic_N).2

theorem tie_N' : priorKeyTie Input (orderedKeys Input S.frameKey) (S.slot 3) (S.slot 2) :=
  ((S.orderedPriorTie_iff_enantiomorphic distinct (S.slot 3) (S.slot 2)).2
    (enantiomorphic_symm _ _ _ enantiomorphic_N)).2

theorem head_N18 :
    ∃ (v : Input.LocalizedRerootRule5Reading) (tail : List Input.LocalizedRerootRule5Reading),
      (orderedKeys Input S.frameKey (S.slot 3)).rule5Readings = v :: tail := by
  have hm := CertifiedLocalizedCIPInput.orderedPriorTie_matched Input (S.frameKey (S.slot 2))
    (S.frameKey (S.slot 3)) tie_N (S.frameKey_readings (S.slot 2)).1
    (S.frameKey_readings (S.slot 3)).1
  have hlen := hm.2.2.length_eq
  obtain ⟨u, tail, hu, _⟩ := head_N3
  have hu' : (Input.outcomeOrdered45 (S.frameKey (S.slot 2))).rule5Readings = u :: tail := hu
  rw [hu'] at hlen
  rcases h : (Input.outcomeOrdered45 (S.frameKey (S.slot 3))).rule5Readings with _ | ⟨v, tail'⟩
  · rw [h] at hlen; simp at hlen
  · exact ⟨v, tail', h⟩

theorem addressBefore_zero {earlier : List ℕ}
    (h : Certificate.CanonicalSphereKey.AddressBefore earlier [0]) : earlier = [] := by
  unfold Certificate.CanonicalSphereKey.AddressBefore at h
  rcases h with h | ⟨hlen, hlt⟩
  · exact List.length_eq_zero_iff.1 (Nat.lt_one_iff.1 h)
  · exfalso
    rcases earlier with _ | ⟨x, rest⟩
    · simp at hlen
    · simp at hlen
      subst hlen
      simp [List.cons_lt_cons_iff] at hlt

/-- **The Rule-5 decision inside the mirror pair, at the fixture.**  The N3 head reading's
common-`R` key is senior to the N18 head reading's. -/
theorem decision_N3_N18 {u : Input.LocalizedRerootRule5Reading} {tailU}
    (hu : (orderedKeys Input S.frameKey (S.slot 2)).rule5Readings = u :: tailU)
    {v : Input.LocalizedRerootRule5Reading} {tailV}
    (hv : (orderedKeys Input S.frameKey (S.slot 3)).rule5Readings = v :: tailV) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      u.commonR.descriptor v.commonR.descriptor = .gt := by
  have hρ : u.prior.reference? = some RS.R := by
    obtain ⟨u', tail', hu', href⟩ := head_N3
    rw [hu] at hu'
    cases hu'
    exact href
  rw [S.commonR_decision_gt_iff distinct slot_ne tie_N hu hv hρ]
  obtain ⟨h4a, h4b, hroot⟩ := firstChiral_armR
  refine ⟨[0], ?_, ?_, ?_⟩
  · rw [slotEquiv_symm_slot]
    exact h4a
  · rw [slotEquiv_symm_slot, h4b]
    rfl
  · intro earlier hearlier
    rw [slotEquiv_symm_slot, addressBefore_zero hearlier, hroot]
    decide

/-- In the root's order the N3 slot cannot follow the N18 slot. -/
theorem not_N18_before_N3 :
    ¬ (compoundPriorTieRelation Input (orderedKeys Input S.frameKey) (S.slot 3) (S.slot 2) →
      ∀ (u : Input.LocalizedRerootRule5Reading) tailU (v : Input.LocalizedRerootRule5Reading) tailV,
        (orderedKeys Input S.frameKey (S.slot 3)).rule5Readings = u :: tailU →
        (orderedKeys Input S.frameKey (S.slot 2)).rule5Readings = v :: tailV →
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          u.commonR.descriptor v.commonR.descriptor = .gt) := by
  intro hwrong
  obtain ⟨u, tailU, hu, _⟩ := head_N3
  obtain ⟨v, tailV, hv⟩ := head_N18
  have hgt := decision_N3_N18 hu hv
  have hgt' := hwrong ⟨slot_ne.symm, tie_N'⟩ v tailV u tailU hv hu
  have h1 := (S.rank_lt_iff_commonR_gt distinct slot_ne tie_N hu hv).2 hgt
  have h2 := (S.rank_lt_iff_commonR_gt distinct slot_ne.symm tie_N' hv hu).2 hgt'
  exact lt_asymm h1 h2

/-! ## The order of the four slots -/

/-- Position in the target order `[Cl, N3, N18, H]` of the canonical ligand indices
`H = 0, Cl = 1, N3 = 2, N18 = 3`. -/
def rank4 : Fin 4 → ℕ
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2

theorem list_eq_of_pairwise {Q : Fin 4 → Fin 4 → Prop} {l : List (Fin 4)}
    (hp : l.Perm (List.finRange 4)) (hl : l.Pairwise Q)
    (h01 : ¬ Q 0 1) (h02 : ¬ Q 0 2) (h03 : ¬ Q 0 3) (h21 : ¬ Q 2 1) (h31 : ¬ Q 3 1)
    (h32 : ¬ Q 3 2) : l = [1, 2, 3, 0] := by
  have hrank : ∀ a b : Fin 4, a ≠ b → Q a b → rank4 a < rank4 b := by
    intro a b hne hq
    fin_cases a <;> fin_cases b <;>
      first
      | exact absurd rfl hne
      | exact absurd hq h01
      | exact absurd hq h02
      | exact absurd hq h03
      | exact absurd hq h21
      | exact absurd hq h31
      | exact absurd hq h32
      | decide
  have hnd : l.Nodup := hp.nodup_iff.2 (List.nodup_finRange 4)
  have hsorted : l.Pairwise (fun a b => rank4 a < rank4 b) :=
    (hl.and hnd).imp (fun h => hrank _ _ h.2 h.1)
  have htarget : ([1, 2, 3, 0] : List (Fin 4)).Pairwise (fun a b => rank4 a < rank4 b) := by
    decide
  have hperm : l.Perm [1, 2, 3, 0] := hp.trans (by decide)
  haveI : Std.Antisymm (fun a b : Fin 4 => rank4 a < rank4 b) :=
    ⟨fun a b h1 h2 => absurd (h1.trans h2) (lt_irrefl _)⟩
  exact List.Perm.eq_of_pairwise' hsorted htarget hperm

/-- The R4 pairwise predicate, in canonical ligand indices. -/
def Q' (ℓ m : Fin 4) : Prop :=
  (S.independentKey ℓ ≠ S.independentKey m → S.independentKey m < S.independentKey ℓ) ∧
    (compoundPriorTieRelation Input (orderedKeys Input S.frameKey) (S.slot ℓ) (S.slot m) →
      ∀ (u : Input.LocalizedRerootRule5Reading) tailU (v : Input.LocalizedRerootRule5Reading) tailV,
        (orderedKeys Input S.frameKey (S.slot ℓ)).rule5Readings = u :: tailU →
        (orderedKeys Input S.frameKey (S.slot m)).rule5Readings = v :: tailV →
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          u.commonR.descriptor v.commonR.descriptor = .gt)

theorem not_Q'_of_lt {ℓ m : Fin 4} (h : S.independentKey ℓ < S.independentKey m) : ¬ Q' ℓ m :=
  fun hq => absurd (hq.1 (ne_of_lt h)) (not_lt.2 h.le)

theorem not_Q'_32 : ¬ Q' 3 2 := fun hq => not_N18_before_N3 hq.2

/-! ## The letter -/

theorem points_slot_of (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      Input.localizedRerootCursorSpatialPoint? (S.frame.cursorAt index) = some (pointsAt index))
    (k : Fin 4) (atom : Atom) (pt : CartesianPoint3)
    (hlig : Input.canonicalLigandAtom S.center k = atom)
    (hsp : Input.spatialPointAt? atom = some pt) : pointsAt (S.slot k) = pt := by
  have h := spatial (S.slot k)
  rw [S.spatialPoint_cursorAt, slotEquiv_symm_slot, hlig, hsp] at h
  exact (Option.some.inj h).symm

/-- **The concrete letter of the fixture.**  The ordered evaluator's own fixed point at the root
of the 33-atom two-reference pseudoasymmetry fixture is `r`. -/
theorem root_letter :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
        (ActualReaderPhysicalBranchInverse.topTarget input rootP) =
      some (.pseudoasymmetric .r) := by
  obtain ⟨tracked, normalizedRS, pointsAt, stateEq, spatial, perm, rational, _, _, indep, rule5⟩ :=
    S.orderedReferenceState_top_eq_classify_physical_rule5
      FixturePhysicalTransport.pairwiseProperDistinguishable_actual_root
      FixtureRootGeometry.actualCanonicalRootCoordinates
  have hl' : (tracked.highestFirst.map S.slotEquiv.symm).Pairwise Q' := by
    refine List.Pairwise.and indep ?_
    rw [List.pairwise_map]
    refine rule5.imp ?_
    intro i j h
    rwa [S.slot_slotEquiv_symm, S.slot_slotEquiv_symm]
  have hp' : (tracked.highestFirst.map S.slotEquiv.symm).Perm (List.finRange 4) :=
    (perm.map _).trans (Rule4aTableBridge.finRange_map_perm _)
  have hmapped := list_eq_of_pairwise hp' hl' (not_Q'_of_lt indKey_H_lt_Cl)
    (not_Q'_of_lt indKey_H_lt_N3) (not_Q'_of_lt indKey_H_lt_N18) (not_Q'_of_lt indKey_N3_lt_Cl)
    (not_Q'_of_lt indKey_N18_lt_Cl) not_Q'_32
  have horder : tracked.highestFirst = [S.slot 1, S.slot 2, S.slot 3, S.slot 0] := by
    have h := congrArg (List.map S.slotEquiv) hmapped
    rw [List.map_map] at h
    simpa [Function.comp_def] using h
  rw [horder] at rational
  simp only [List.map_cons, List.map_nil] at rational
  rw [points_slot_of pointsAt spatial 1 atom2 FixtureRootGeometry.rootPoint1
      FixtureRootGeometry.canonicalLigandAtom_one FixtureRootGeometry.spatialRootPoint1,
    points_slot_of pointsAt spatial 2 atom3 FixtureRootGeometry.rootPoint2
      FixtureRootGeometry.canonicalLigandAtom_two FixtureRootGeometry.spatialRootPoint2,
    points_slot_of pointsAt spatial 3 atom18 FixtureRootGeometry.rootPoint3
      FixtureRootGeometry.canonicalLigandAtom_three FixtureRootGeometry.spatialRootPoint3,
    points_slot_of pointsAt spatial 0 atom1 FixtureRootGeometry.rootPoint0
      FixtureRootGeometry.canonicalLigandAtom_zero FixtureRootGeometry.spatialRootPoint0]
    at rational
  have hR : normalizedRS = RS.R := by
    obtain ⟨a, b, c, e, hpts, hsign⟩ := rational
    simp only [List.cons.injEq, and_true] at hpts
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpts
    cases normalizedRS with
    | R => rfl
    | S =>
      exfalso
      norm_num [FixtureRootGeometry.rootPoint0, FixtureRootGeometry.rootPoint1,
        FixtureRootGeometry.rootPoint2, FixtureRootGeometry.rootPoint3,
        CartesianPoint3.orientedVolume] at hsign
  have hcount : physicalEnantiomorphicPairCount Physical cfg rootP = 1 :=
    FixturePhysicalTransport.physicalEnantiomorphicPairCount_actual_root_eq_one
  have stateEq' : input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
      (ActualReaderPhysicalBranchInverse.topTarget input rootP) =
        some (classifyTetrahedralRSPseudo normalizedRS
          (physicalEnantiomorphicPairCount Physical cfg rootP)) := stateEq
  rw [stateEq', hcount, hR]
  rfl

end

end LocalizedTwoReferenceFixtureRootLetter
end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.build_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.read_eq_readT
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.build_read_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.compare4b_R_S
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.head_N3
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.enantiomorphic_N
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.decision_N3_N18
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.indKey_H_lt_Cl
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.list_eq_of_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter.root_letter
