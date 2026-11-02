import TetraStereo.OneCenter.LocalizedUnbranchedExtendedDemandRank
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedAxialRootPerception
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable
import TetraStereo.OneCenter.LocalizedUniversalDescriptorEvaluation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Root-local double-bond-neighbour bound from an actual tetrahedral ligand frame

The global unbranched graph domain of the extended Rule-3 demand rank,
`LocalizedUnbranchedDoubleBondGraph`, requires *every* atom of the molecule to have at most two
distinct order-two neighbours.  A tetrahedral descriptor, however, is only evaluated at its own
root occurrence.  This module proves the concrete combinatorial bridge that turns an actually
computed four-ligand first reroot frame at an original carrier-root occurrence into a bound on the
root atom alone.

The general counting statement proved first is

`2 * card(orderTwoNeighbours root) ≤ length(executable official children of root)`.

It is derived from the executable child-copy enumeration: every distinct order-two neighbour
contributes exactly the two copies `0` (the real graph edge) and `1` (the multiple-bond duplicate)
of `executableOfficialNeighborCopies`.  Bond orders above two and all other atoms contribute
additional children and are harmless.

The second step embeds every executable official child of the root node into the finite carrier's
outward child frames at address `[slot]`.  The carrier retains those children because the root
occurrence has positive remaining depth.  The actual first reroot frame is exactly the executable
cut-neighbourhood expansion, so its length dominates the official child count.

Consequently an actual root four-ligand frame bounds the root atom's double-bond neighbour count
by two.  No claim is made for internal targets.  No geometry, no descriptor success, no valence
computation and no desired label is assumed.

## Kernel authority

Every exported declaration is guarded by `assert_kernel_only`.
-/

namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! ## A list-counting core -/

/-- **Two copies per order-two neighbour.**  In any list, the number of elements whose image under
`b` is exactly two is at most half the total sum of the images. -/
theorem list_two_mul_length_filter_beq_two_le_sum {α : Type*} (l : List α) (b : α → Nat) :
    2 * (l.filter fun a => b a == 2).length ≤ (l.map b).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases h : b a = 2
      · have hb : (b a == 2) = true := by simpa using h
        simp only [List.filter_cons, hb, ↓reduceIte, List.length_cons, List.map_cons,
          List.sum_cons]
        omega
      · have hb : (b a == 2) = false := by
          simp [h]
        simp only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte,
          List.map_cons, List.sum_cons]
        omega

/-- The length of the executable neighbor-copy enumeration is the sum of the bond orders over all
neighbors. -/
theorem executableOfficialNeighborCopies_length_eq_sum
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    (input.executableOfficialNeighborCopies atom).length =
      (((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)).map
        fun neighbor => input.moleculeGraph.bond atom neighbor).sum := by
  unfold executableOfficialNeighborCopies
  simp only [List.length_flatMap, List.length_map, List.length_range]

/-- The double-bond-neighbour finset cardinality is the length of the filtered sorted neighbor
list used by the executable copy enumeration. -/
theorem localizedDoubleBondNeighbourFinset_card_eq_sorted_filter_length
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    (input.localizedDoubleBondNeighbourFinset atom).card =
      (((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)).filter
        fun neighbor => input.moleculeGraph.bond atom neighbor == 2).length := by
  have filteredNodup : (((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)).filter
      fun neighbor => input.moleculeGraph.bond atom neighbor == 2).Nodup :=
    (Finset.sort_nodup (input.moleculeGraph.neighborFinset atom) (· ≤ ·)).filter _
  have toFinsetEq :
      ((((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·)).filter
          fun neighbor => input.moleculeGraph.bond atom neighbor == 2).toFinset) =
        input.localizedDoubleBondNeighbourFinset atom := by
    rw [List.toFinset_filter, Finset.sort_toFinset]
    unfold localizedDoubleBondNeighbourFinset
    ext neighbor
    simp
  rw [← toFinsetEq]
  exact List.toFinset_card_of_nodup filteredNodup

/-- **The root child-count bound.**  The root atom has at most half as many distinct order-two
neighbors as the official root node has executable children.  Every order-two neighbor occurs as
the real zero-copy child and as the first multiple-bond duplicate. -/
theorem doubleBondNeighbourFinset_card_two_mul_le_executableOfficialCIPChildren_root
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    2 * (input.localizedDoubleBondNeighbourFinset atom).card ≤
      (input.executableOfficialCIPChildren (OfficialCIPNode.root atom)).length := by
  have count := list_two_mul_length_filter_beq_two_le_sum
    ((input.moleculeGraph.neighborFinset atom).sort (· ≤ ·))
    (fun neighbor => input.moleculeGraph.bond atom neighbor)
  have childrenLength :
      (input.executableOfficialCIPChildren (OfficialCIPNode.root atom)).length =
        (input.executableOfficialNeighborCopies atom).length := by
    unfold executableOfficialCIPChildren executableOfficialChildCopies
    simp [OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf, OfficialCIPNode.parent?]
  have copiesLength := input.executableOfficialNeighborCopies_length_eq_sum atom
  have cardEq := input.localizedDoubleBondNeighbourFinset_card_eq_sorted_filter_length atom
  rw [← cardEq, ← copiesLength, ← childrenLength] at count
  exact count

/-- The finset-cardinality bound is the sorted-neighbor-list length bound used by the unbranched
graph domain. -/
theorem localizedRootDoubleBondNeighbourBound_iff_orderTwoNeighbors_length
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    (input.localizedDoubleBondNeighbourFinset atom).card ≤ 2 ↔
      (input.localizedOrderTwoNeighbors atom).length ≤ 2 := by
  unfold localizedOrderTwoNeighbors localizedDoubleBondNeighbourFinset
  rw [Finset.length_sort]

/-- Root-local double-bond-neighbour domain for one designated root atom. -/
def LocalizedRootDoubleBondNeighbourBound
    (input : CertifiedLocalizedCIPInput) (root : input.Atom) : Prop :=
  (input.localizedDoubleBondNeighbourFinset root).card ≤ 2

/-! ## Original root occurrences and their carrier children -/

/-- An original carrier-root occurrence has no carrier parent. -/
theorem localizedCarrierParentFrames_eq_nil_of_address_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = []) :
    input.localizedCarrierParentFrames (fuel := carrierFuel) target.1 = [] := by
  unfold localizedCarrierParentFrames
  apply List.filter_eq_nil_iff.mpr
  intro candidate _
  simp [rootAddress]

/-- At an original root occurrence the uncut carrier neighborhood is exactly its outward child
frames: there is no incoming carrier parent to cut. -/
theorem localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = []) :
    input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 =
      input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1 := by
  unfold localizedRerootNeighborFrames
  rw [input.localizedCarrierParentFrames_eq_nil_of_address_nil target rootAddress,
    List.nil_append]

/-- The intended first reroot child frames of an original root occurrence are its outward child
frames.  The root node is a real-atom node, so it is not a duplicate leaf. -/
theorem intendedLocalizedRerootChildFrames_eq_outwardChildFrames_of_address_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = []) :
    input.intendedLocalizedRerootChildFrames
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel) =
      input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1 := by
  have targetDerived :
      input.DeclarativeLocalizedOccurrence carrierFuel target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have rootEq :=
    input.declarativeLocalizedOccurrence_eq_root_of_address_nil targetDerived rootAddress
  have nodeEq : target.1.node = OfficialCIPNode.root target.1.root := by
    have := congrArg (fun frame => frame.node) rootEq
    simpa using this
  have neighborEq :=
    input.localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil target rootAddress
  simp [intendedLocalizedRerootChildFrames, nodeEq, neighborEq, OfficialCIPNode.root,
    OfficialCIPNode.isDuplicateLeaf]

/-- **Carrier retention of official root children.**  Every executable official child of the root
occurrence's node appears in the finite carrier as an outward child frame at address `[slot]`.
The root occurrence has positive remaining depth, and the normal carrier derivation rule closes
under every immediate official child. -/
theorem executableOfficialCIPChildren_length_le_outwardChildFrames_of_address_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = []) :
    (input.executableOfficialCIPChildren target.1.node).length ≤
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).length := by
  have targetDerived :
      input.DeclarativeLocalizedOccurrence carrierFuel target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have grade := input.localizedCIPOccurrence_depthGrade target
  have positive : 0 < target.1.remaining := by
    have height : target.1.remaining = carrierFuel + 1 := by
      rw [rootAddress] at grade
      simpa using grade
    omega
  let children := input.executableOfficialCIPChildren target.1.node
  let f : Fin children.length → input.LocalizedCIPOccurrenceFrame := fun i =>
    { root := target.1.root
      address := target.1.address ++ [i.val]
      node := children[i]
      remaining := target.1.remaining - 1 }
  have hmem : ∀ i : Fin children.length,
      f i ∈ input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1 := by
    intro i
    have childAtSlot : (children[i], i.val) ∈ children.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem i.isLt)
    have derived := DeclarativeLocalizedOccurrence.immediateChild
      input targetDerived positive childAtSlot
    have member : f i ∈ input.localizedOccurrences carrierFuel :=
      (input.mem_localizedOccurrences_iff carrierFuel (f i)).mpr derived
    rw [localizedCarrierOutwardChildFrames, List.mem_filter]
    exact ⟨member, by simp [f, rootAddress]⟩
  have hinj : Set.InjOn f (↑(Finset.univ : Finset (Fin children.length))) := by
    intro i _ j _ hij
    have addressEq : target.1.address ++ [i.val] = target.1.address ++ [j.val] := by
      have := congrArg (fun frame => frame.address) hij
      simpa [f] using this
    have valueEq : i.val = j.val := by
      have := List.append_cancel_left addressEq
      simpa using this
    exact Fin.ext valueEq
  have imageCard : (Finset.univ.image f).card = children.length := by
    rw [Finset.card_image_of_injOn hinj]
    simp
  have imageSubset : Finset.univ.image f ⊆
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).toFinset := by
    intro frame present
    rw [Finset.mem_image] at present
    rcases present with ⟨i, _mem, rfl⟩
    exact List.mem_toFinset.mpr (hmem i)
  have outwardCard :
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).toFinset.card =
        (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).length :=
    List.toFinset_card_of_nodup
      ((input.localizedOccurrences_nodup carrierFuel).filter _)
  calc (input.executableOfficialCIPChildren target.1.node).length
      = children.length := rfl
    _ = (Finset.univ.image f).card := imageCard.symm
    _ ≤ (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).toFinset.card :=
        Finset.card_le_card imageSubset
    _ = (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).length :=
        outwardCard

/-- **The root-local double-bond bound from an actual first ligand frame.**  For an original
carrier-root occurrence whose actual first reroot expansion is the list `cursors`, twice the
number of distinct order-two neighbours of the molecule's root atom is at most the frame length.
No assumption is made about internal targets, about the rest of the molecule, or about
descriptor success. -/
theorem two_mul_doubleBondNeighbourFinset_card_le_ligandFrame_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedOccurrenceLigandFrame? target = some cursors) :
    2 * (input.localizedDoubleBondNeighbourFinset target.1.root).card ≤ cursors.length := by
  have targetDerived :
      input.DeclarativeLocalizedOccurrence carrierFuel target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have rootEq :=
    input.declarativeLocalizedOccurrence_eq_root_of_address_nil targetDerived rootAddress
  have nodeEq : target.1.node = OfficialCIPNode.root target.1.root := by
    have := congrArg (fun frame => frame.node) rootEq
    simpa using this
  have intendedEq :=
    input.intendedLocalizedRerootChildFrames_eq_outwardChildFrames_of_address_nil
      target rootAddress
  have sound := input.localizedOccurrenceLigandFrame?_sound target cursors computed
  have frameLength : cursors.length =
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).length := by
    have h := congrArg List.length sound.1
    rw [List.length_map, intendedEq] at h
    exact h
  have childBound :=
    input.doubleBondNeighbourFinset_card_two_mul_le_executableOfficialCIPChildren_root
      target.1.root
  have embedded :=
    input.executableOfficialCIPChildren_length_le_outwardChildFrames_of_address_nil
      target rootAddress
  rw [nodeEq] at embedded
  have combined : 2 * (input.localizedDoubleBondNeighbourFinset target.1.root).card ≤
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).length :=
    le_trans childBound embedded
  rwa [← frameLength] at combined

/-- **Four actual ligands force the root-local bound.**  The actual first ligand frame of an
original carrier-root occurrence has length four, hence the root atom has at most two distinct
order-two neighbours. -/
theorem doubleBondNeighbourFinset_card_le_two_of_ligandFrame_length_four
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedOccurrenceLigandFrame? target = some cursors)
    (lengthFour : cursors.length = 4) :
    input.LocalizedRootDoubleBondNeighbourBound target.1.root := by
  have bound :=
    input.two_mul_doubleBondNeighbourFinset_card_le_ligandFrame_length
      target rootAddress cursors computed
  unfold LocalizedRootDoubleBondNeighbourBound
  omega

/-- The executable first expansion's length is the intended frame length, hence the carrier
outward child-frame length at an original root occurrence. -/
theorem executableLocalizedRerootChildren_length_eq_outwardChildFrames_of_address_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = []) :
    (input.executableLocalizedRerootChildren
        ({ occurrence := target, previous? := none } :
          input.LocalizedRerootCursor carrierFuel)).length =
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).length := by
  have intendedEq :=
    input.intendedLocalizedRerootChildFrames_eq_outwardChildFrames_of_address_nil
      target rootAddress
  unfold executableLocalizedRerootChildren
  simp only [List.length_map, List.length_attach]
  rw [intendedEq]

/-- **Four-ligand-frame form.**  A computed `LocalizedOccurrenceFourLigandFrame` for an original
carrier-root occurrence has its frame equal to the executable expansion, so twice the root
double-bond neighbour count is at most four. -/
theorem two_mul_doubleBondNeighbourFinset_card_le_fourLigandFrame_cursors_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    2 * (input.localizedDoubleBondNeighbourFinset target.1.root).card ≤
      frame.cursors.length := by
  have targetDerived :
      input.DeclarativeLocalizedOccurrence carrierFuel target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have rootEq :=
    input.declarativeLocalizedOccurrence_eq_root_of_address_nil targetDerived rootAddress
  have nodeEq : target.1.node = OfficialCIPNode.root target.1.root := by
    have := congrArg (fun frame => frame.node) rootEq
    simpa using this
  have executableLength :=
    input.executableLocalizedRerootChildren_length_eq_outwardChildFrames_of_address_nil
      target rootAddress
  have childBound :=
    input.doubleBondNeighbourFinset_card_two_mul_le_executableOfficialCIPChildren_root
      target.1.root
  have embedded :=
    input.executableOfficialCIPChildren_length_le_outwardChildFrames_of_address_nil
      target rootAddress
  rw [nodeEq] at embedded
  have combined : 2 * (input.localizedDoubleBondNeighbourFinset target.1.root).card ≤
      (input.localizedCarrierOutwardChildFrames (fuel := carrierFuel) target.1).length :=
    le_trans childBound embedded
  rw [input.localizedOccurrenceFourLigandFrame_cursors_eq_executable target frame computed,
    executableLength]
  exact combined

/-- A computed four-ligand frame at an original root occurrence is already enough: its four
recorded cursors bound the root double-bond neighbour count by two. -/
theorem doubleBondNeighbourFinset_card_le_two_of_fourLigandFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    input.LocalizedRootDoubleBondNeighbourBound target.1.root := by
  have bound :=
    input.two_mul_doubleBondNeighbourFinset_card_le_fourLigandFrame_cursors_length
      target rootAddress frame computed
  have lengthFour := frame.length_eq
  unfold LocalizedRootDoubleBondNeighbourBound
  omega

/-! ## Descriptor backends -/

/-- A successful parameterized descriptor evaluation yields an actual four-ligand frame.  The
descriptor pipeline binds the same executable four-ligand frame that
`localizedOccurrenceFourLigandFrame?` computes, so a successful evaluation cannot coexist with a
missing frame. -/
theorem exists_fourLigandFrame_of_descriptorAt?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorAt? target view evaluationBudget = some descriptor) :
    ∃ base : input.LocalizedOccurrenceFourLigandFrame carrierFuel,
      input.localizedOccurrenceFourLigandFrame? target = some base := by
  cases baseEq : input.localizedNoDoubleFourLigandFrameExec? target with
  | none =>
      have refused :=
        input.descriptorAt?_eq_none_of_base_none target view evaluationBudget baseEq
      rw [refused] at computed
      cases computed
  | some base =>
      refine ⟨base, ?_⟩
      rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
        target]
      exact baseEq

/-- **Root-local bound from actual parameterized descriptor success.**  If the production
descriptor backend succeeds at an original carrier-root occurrence, then the molecule's root atom
has at most two distinct order-two neighbours.  Only the four-ligand base is used; no desired
label, coordinate or refusal outcome enters the combinatorial bound. -/
theorem LocalizedRootDoubleBondNeighbourBound_of_descriptorAt?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorAt? target view evaluationBudget = some descriptor) :
    input.LocalizedRootDoubleBondNeighbourBound target.1.root := by
  obtain ⟨base, frameSome⟩ :=
    input.exists_fourLigandFrame_of_descriptorAt?_eq_some
      target view evaluationBudget descriptor computed
  exact input.doubleBondNeighbourFinset_card_le_two_of_fourLigandFrame
    target rootAddress base frameSome

/-- **Root-local bound from actual universal descriptor success.**  A successful universal
descriptor also carries a successful parameterized evaluation at the computed budget, hence an
actual four-ligand frame at the original root occurrence. -/
theorem LocalizedRootDoubleBondNeighbourBound_of_universalDescriptor?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.universalDescriptor? target view = some descriptor) :
    input.LocalizedRootDoubleBondNeighbourBound target.1.root := by
  obtain ⟨base, evaluationBudget, baseSome, _descriptorSome⟩ :=
    input.universalDescriptor?_some_imp_exists_descriptorAt?_some
      target view descriptor computed
  have frameSome : input.localizedOccurrenceFourLigandFrame? target = some base := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact baseSome
  exact input.doubleBondNeighbourFinset_card_le_two_of_fourLigandFrame
    target rootAddress base frameSome

/-! ## List-form statements for the root-local unbranched domain -/

/-- The filtered-sorted list used by the unbranched graph domain has the same length as the
double-bond-neighbour finset cardinality. -/
theorem localizedDoubleBondNeighbourFinset_card_eq_localizedOrderTwoNeighbors_length
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    (input.localizedDoubleBondNeighbourFinset atom).card =
      (input.localizedOrderTwoNeighbors atom).length := by
  unfold localizedOrderTwoNeighbors localizedDoubleBondNeighbourFinset
  rw [Finset.length_sort]

/-- List form of the general actual-frame bound. -/
theorem two_mul_orderTwoNeighbors_length_le_ligandFrame_length
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedOccurrenceLigandFrame? target = some cursors) :
    2 * (input.localizedOrderTwoNeighbors target.1.root).length ≤ cursors.length := by
  have bound :=
    input.two_mul_doubleBondNeighbourFinset_card_le_ligandFrame_length
      target rootAddress cursors computed
  rwa [input.localizedDoubleBondNeighbourFinset_card_eq_localizedOrderTwoNeighbors_length]
    at bound



theorem orderTwoNeighbors_length_le_two_of_ligandFrame_length_four
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (cursors : List (input.LocalizedRerootCursor carrierFuel))
    (computed : input.localizedOccurrenceLigandFrame? target = some cursors)
    (lengthFour : cursors.length = 4) :
    (input.localizedOrderTwoNeighbors target.1.root).length ≤ 2 :=
  (input.localizedRootDoubleBondNeighbourBound_iff_orderTwoNeighbors_length
    target.1.root).mp
    (input.doubleBondNeighbourFinset_card_le_two_of_ligandFrame_length_four
      target rootAddress cursors computed lengthFour)

/-- List form of the actual four-ligand-frame bound. -/
theorem orderTwoNeighbors_length_le_two_of_fourLigandFrame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame) :
    (input.localizedOrderTwoNeighbors target.1.root).length ≤ 2 :=
  (input.localizedRootDoubleBondNeighbourBound_iff_orderTwoNeighbors_length
    target.1.root).mp
    (input.doubleBondNeighbourFinset_card_le_two_of_fourLigandFrame
      target rootAddress frame computed)

/-- List form of the parameterized-descriptor corollary. -/
theorem orderTwoNeighbors_length_le_two_of_descriptorAt?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (view : input.LocalizedDependencyView target)
    (evaluationBudget : Nat) (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.descriptorAt? target view evaluationBudget = some descriptor) :
    (input.localizedOrderTwoNeighbors target.1.root).length ≤ 2 :=
  (input.localizedRootDoubleBondNeighbourBound_iff_orderTwoNeighbors_length
    target.1.root).mp
    (input.LocalizedRootDoubleBondNeighbourBound_of_descriptorAt?_eq_some
      target rootAddress view evaluationBudget descriptor computed)

/-- List form of the universal-descriptor corollary. -/
theorem orderTwoNeighbors_length_le_two_of_universalDescriptor?_eq_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (rootAddress : target.1.address = [])
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.universalDescriptor? target view = some descriptor) :
    (input.localizedOrderTwoNeighbors target.1.root).length ≤ 2 :=
  (input.localizedRootDoubleBondNeighbourBound_iff_orderTwoNeighbors_length
    target.1.root).mp
    (input.LocalizedRootDoubleBondNeighbourBound_of_universalDescriptor?_eq_some
      target rootAddress view descriptor computed)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.list_two_mul_length_filter_beq_two_le_sum
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialNeighborCopies_length_eq_sum
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDoubleBondNeighbourFinset_card_eq_sorted_filter_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.doubleBondNeighbourFinset_card_two_mul_le_executableOfficialCIPChildren_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRootDoubleBondNeighbourBound_iff_orderTwoNeighbors_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRootDoubleBondNeighbourBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCarrierParentFrames_eq_nil_of_address_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames_eq_outwardChildFrames_of_address_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableOfficialCIPChildren_length_le_outwardChildFrames_of_address_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.two_mul_doubleBondNeighbourFinset_card_le_ligandFrame_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.doubleBondNeighbourFinset_card_le_two_of_ligandFrame_length_four
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableLocalizedRerootChildren_length_eq_outwardChildFrames_of_address_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.two_mul_doubleBondNeighbourFinset_card_le_fourLigandFrame_cursors_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.doubleBondNeighbourFinset_card_le_two_of_fourLigandFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_fourLigandFrame_of_descriptorAt?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRootDoubleBondNeighbourBound_of_descriptorAt?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRootDoubleBondNeighbourBound_of_universalDescriptor?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDoubleBondNeighbourFinset_card_eq_localizedOrderTwoNeighbors_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.two_mul_orderTwoNeighbors_length_le_ligandFrame_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderTwoNeighbors_length_le_two_of_ligandFrame_length_four
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderTwoNeighbors_length_le_two_of_fourLigandFrame
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderTwoNeighbors_length_le_two_of_descriptorAt?_eq_some
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.orderTwoNeighbors_length_le_two_of_universalDescriptor?_eq_some
