import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerOperations
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution
import TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport
import TetraStereo.OneCenter.LocalizedChemicalRingStateTransport
import TetraStereo.OneCenter.LocalizedChemicalRingFrameComparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3000000



































namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge DeclarativeCIP.PromotedCanonical
open LocalizedChemicalRingJointMarkerKey
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedMolecularRule5
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedVirtualTarget
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedCanonicalFrame
open LocalizedChemicalRingRetainedKeyTransport
open LocalizedChemicalRingPromotedTransport
open LocalizedChemicalRingJointMarkerOperations
open LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingStateTransport
open LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingRelabel
open LocalizedChemicalRingFrameComparison

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-- The ordered reference-bit vector transports along the same atom permutation. -/
theorem referenceVector_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut) {fuel : Nat} (references : List input.Atom)
    (cursor : input.LocalizedRerootCursor fuel) :
    referenceVector input (references.map (e : Equiv.Perm input.Atom))
        (input.transportCursor single e cursor) =
      referenceVector input references cursor := by
  unfold referenceVector
  rw [List.map_map]
  apply List.map_congr_left
  intro reference _
  simpa only [Function.comp_apply] using
    referenceBit_transport input single e reference cursor

/-! ## The accumulated mark context

Marks are atom indices. The accumulated context attached to a reference column is that column's
indices. Under the same molecular atom permutation the image context is the relabelled index
list, and it decodes to the ordered image of the reference column. -/

/-- Relabelling the atom indices of a reference column is the index encoding of the image column. -/
theorem referenceMarks_relabel (e : input.moleculeGraph.Aut) (references : List input.Atom) :
    (references.map (e : Equiv.Perm input.Atom)).map Fin.val =
      (references.map Fin.val).map
        (relabelOf input (e : Equiv.Perm input.Atom)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro reference _
  exact (relabelOf_val input (e : Equiv.Perm input.Atom) reference).symm

/-- The transported accumulated mark context is the relabelled source context and still decodes to
the ordered image reference column. Uses the accepted `referenceAtoms?_map`; no other decoding is
assumed. -/
theorem referenceAtoms?_relabel_marks (e : input.moleculeGraph.Aut)
    (references : List input.Atom) :
    referenceAtoms? input ((references.map Fin.val).map
        (relabelOf input (e : Equiv.Perm input.Atom))) =
      some (references.map (e : Equiv.Perm input.Atom)) := by
  rw [← referenceMarks_relabel input e references]
  exact LocalizedChemicalRingJointMarkerFrameExecution.referenceAtoms?_map input
    (references.map (e : Equiv.Perm input.Atom))

/-! ## Sorting one projection of the actual joint keys -/

private theorem mapM_forall₂ {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) (ys : List β), xs.mapM f = some ys →
      List.Forall₂ (fun x y => f x = some y) xs ys
  | [], ys, h => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at h
      subst h
      exact .nil
  | x :: xs, ys, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
        Option.some.injEq] at h
      obtain ⟨y, hy, rest, hrest, rfl⟩ := h
      exact .cons hy (mapM_forall₂ f xs rest hrest)

private theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} :
    ∀ {l : List α} {m : List β}, (∀ a ∈ l, ∀ b, R a b → S a b) →
      List.Forall₂ R l m → List.Forall₂ S l m
  | [], [], _, _ => .nil
  | a :: _, _ :: _, h, .cons hab rest =>
      .cons (h a (by simp) _ hab)
        (forall₂_imp_mem (fun x hx y hy => h x (by simp [hx]) y hy) rest)

private theorem exists_of_mem_forall₂_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → ∀ b ∈ m, ∃ a ∈ l, R a b
  | [], [], _, b, hb => by simp at hb
  | a :: _, _ :: _, .cons h rest, b, hb => by
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨a, by simp, h⟩
      · obtain ⟨a', ha', h'⟩ := exists_of_mem_forall₂_right rest b hb
        exact ⟨a', by simp [ha'], h'⟩

private theorem map_eq_of_forall₂ {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => f a = g b) l m → l.map f = m.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, .cons h rest => by
      simp only [List.map_cons, h, map_eq_of_forall₂ rest]

/-- Project the actual joint sorting to the independent complete-key sort. The hypotheses concern
individual builds and the immutable ordinary comparison only; tied actual keys may appear in any
order. All marker columns share the same child layout and stay in one vector. -/
theorem sorted_joint_markers_mapM
    {α P : Type} [LinearOrder P] (xs : List α)
    (f : α → Option (JointPromotedKey input)) (keys : List (JointPromotedKey input))
    (built : xs.mapM f = some keys) (prior : α → P) (fallback : P) (mark : α → JointMarker)
    (priorCmp : ∀ a ∈ xs, ∀ b ∈ xs, ∀ ka kb, f a = some ka → f b = some kb →
      (input.compareLocalizedRerootCompoundThroughRule5 ka.prior kb.prior).ordering =
        compare (prior a) (prior b))
    (markEq : ∀ a ∈ xs, ∀ k, f a = some k → k.markers = mark a) :
    (sortJointKeys input keys).map JointPromotedKey.markers =
      (Certificate.CanonicalSphereKey.sortDesc
        (xs.map fun a => toLex (prior a, mark a))).map (fun k => (ofLex k).2) := by
  classical
  have related := mapM_forall₂ f xs keys built
  let priorOf : JointPromotedKey input → P := fun k =>
    if h : ∃ a ∈ xs, f a = some k then prior (Classical.choose h) else fallback
  have priorOf_eq : ∀ a ∈ xs, ∀ k, f a = some k → priorOf k = prior a := by
    intro a member k builtA
    have present : ∃ a ∈ xs, f a = some k := ⟨a, member, builtA⟩
    simp only [priorOf, dif_pos present]
    obtain ⟨member', built'⟩ := Classical.choose_spec present
    have cross := priorCmp _ member' a member k k built' builtA
    have self := priorCmp a member a member k k builtA builtA
    rw [show compare (prior a) (prior a) = .eq from compare_eq_iff_eq.2 rfl] at self
    exact compare_eq_iff_eq.1 (cross.symm.trans self)
  let φ : JointPromotedKey input → Lex (P × JointMarker) := fun k => toLex (priorOf k, k.markers)
  have order : ∀ x ∈ keys, ∀ y ∈ keys, compareJointKeys input x y ≠ .lt ↔ φ y ≤ φ x := by
    intro x hx y hy
    obtain ⟨a, ha, builtA⟩ := exists_of_mem_forall₂_right related x hx
    obtain ⟨b, hb, builtB⟩ := exists_of_mem_forall₂_right related y hy
    simp only [φ, priorOf_eq a ha x builtA, priorOf_eq b hb y builtB]
    exact compareJointKeys_ne_lt_iff input x y (prior a) (prior b)
      (priorCmp a ha b hb x y builtA builtB)
  rw [sortJointKeys_markers_eq input keys φ (fun _ => rfl) order]
  have mapped : xs.map (fun a => toLex (prior a, mark a)) = keys.map φ := by
    apply map_eq_of_forall₂
    refine forall₂_imp_mem ?_ related
    intro a ha k hk
    simp only [φ, priorOf_eq a ha k hk, markEq a ha k hk]
  rw [mapped]

/-- Actual successful joint builds transport at every reached cursor: the complete ordered marker
vector agrees. The image reference list is the pointwise image of the source list, in the same
order; the one shared child layout is sorted by the whole vector on both sides. -/
theorem build_joint_markers_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat) :
    ∀ fuel (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input)),
      Relation.ReflTransGen (E input) ⟨t, none⟩ cursor →
      ∀ a b : JointPromotedKey input,
        buildJoint? input t (input.molecularView descriptorMap t) references W D fuel cursor =
            some a →
        buildJoint? input (input.transportOccurrence single e t)
          (input.molecularView (input.transportDescriptorMap e descriptorMap)
            (input.transportOccurrence single e t)) (references.map (e : Equiv.Perm input.Atom))
          W D fuel (input.transportCursor single e cursor) = some b →
        b.markers = a.markers := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor reach a b ha hb
      simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at ha hb
      obtain ⟨pa, _, ca, _, restA⟩ := ha
      obtain ⟨pb, _, cb, _, restB⟩ := hb
      split at restA
      · split at restB
        · cases Option.some.inj restA
          cases Option.some.inj restB
          change jointMarkers input (references.map (e : Equiv.Perm input.Atom)) W D []
              (input.transportCursor single e cursor) =
            jointMarkers input references W D [] cursor
          simp only [jointMarkers]
          rw [referenceVector_transport input single e references cursor, List.length_map]
        · cases restB
      · cases restA
  | succ fuel ih =>
      intro cursor reach a b ha hb
      simp only [buildJoint?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at ha hb
      obtain ⟨pa, _, ca, caEq, keys, keysEq, sameA⟩ := ha
      obtain ⟨pb, _, cb, cbEq, imageKeys, imageKeysEq, sameB⟩ := hb
      subst caEq
      subst cbEq
      subst sameA
      subst sameB
      let f := buildJoint? input t (input.molecularView descriptorMap t) references W D fuel
      let f' := buildJoint? input (input.transportOccurrence single e t)
        (input.molecularView (input.transportDescriptorMap e descriptorMap)
          (input.transportOccurrence single e t))
        (references.map (e : Equiv.Perm input.Atom)) W D fuel
      let prior := deepKey descriptorMap t (default : CompleteLigandRule5Key) cursor
      let mark := fun c => ((f c).map JointPromotedKey.markers).getD []
      let image := input.transportCursor single e (fuel := retainedCarrierFuel input)
      let preimage := input.transportCursor single (e⁻¹) (fuel := retainedCarrierFuel input)
      have aligned := aligned_of_reach input t reach
      have preMember : ∀ c ∈ input.executableLocalizedRerootChildren (image cursor),
          preimage c ∈ input.executableLocalizedRerootChildren cursor := by
        intro c hc
        apply (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned
          (preimage c)).mpr
        simpa only [image, preimage, transportCursor_apply_inv] using hc
      have sourceSorted := sorted_joint_markers_mapM input
        (input.executableLocalizedRerootChildren cursor) f keys keysEq prior default mark
        (by
          intro x hx y hy kx ky hkx hky
          exact deepKey_compare input single descriptorMap tetra t cursor x y reach hx hy _ _ _
            (buildJoint?_prior input t _ references W D fuel x kx hkx)
            (buildJoint?_prior input t _ references W D fuel y ky hky))
        (by
          intro x _ k hk
          simp only [mark, hk, Option.map_some, Option.getD_some])
      have imageSorted := sorted_joint_markers_mapM input
        (input.executableLocalizedRerootChildren (image cursor)) f' imageKeys imageKeysEq
        (fun c => prior (preimage c)) default (fun c => mark (preimage c))
        (by
          intro x hx y hy kx ky hkx hky
          have hx₀ := preMember x hx
          have hy₀ := preMember y hy
          obtain ⟨kx₀, hkx₀⟩ := mapM_available f _ _ keysEq _ hx₀
          obtain ⟨ky₀, hky₀⟩ := mapM_available f _ _ keysEq _ hy₀
          have ox := buildJoint?_prior input t _ references W D fuel (preimage x) kx₀ hkx₀
          have oy := buildJoint?_prior input t _ references W D fuel (preimage y) ky₀ hky₀
          have ox' := buildJoint?_prior input (input.transportOccurrence single e t) _
            (references.map (e : Equiv.Perm input.Atom)) W D fuel x kx hkx
          have oy' := buildJoint?_prior input (input.transportOccurrence single e t) _
            (references.map (e : Equiv.Perm input.Atom)) W D fuel y ky hky
          have transported := ordinary_pair_transport input single e descriptorMap tetra t cursor
            (preimage x) (preimage y) reach hx₀ hy₀ kx₀.prior ky₀.prior kx.prior ky.prior ox oy
            (by simpa only [preimage, transportCursor_apply_inv] using ox')
            (by simpa only [preimage, transportCursor_apply_inv] using oy')
          exact transported.trans
            (deepKey_compare input single descriptorMap tetra t cursor _ _ reach hx₀ hy₀ _ _ _
              ox oy))
        (by
          intro x hx k hk
          have hx₀ := preMember x hx
          obtain ⟨k₀, hk₀⟩ := mapM_available f _ _ keysEq _ hx₀
          have eq := ih (preimage x) (reach.tail hx₀) k₀ k hk₀
            (by simpa only [preimage, transportCursor_apply_inv] using hk)
          simpa only [mark, hk₀, Option.map_some, Option.getD_some] using eq)
      have childrenPerm := input.executableLocalizedRerootChildren_transport_perm single e aligned
      have columnPerm :
          ((input.executableLocalizedRerootChildren (image cursor)).map
            fun c => toLex (prior (preimage c), mark (preimage c))).Perm
          ((input.executableLocalizedRerootChildren cursor).map
            fun c => toLex (prior c, mark c)) := by
        simpa only [List.map_map, Function.comp_def, image, preimage, transportCursor_inv_apply]
          using childrenPerm.symm.map (fun c => toLex (prior (preimage c), mark (preimage c)))
      change jointMarkers input (references.map (e : Equiv.Perm input.Atom)) W D
          (sortJointKeys input imageKeys) (image cursor) =
        jointMarkers input references W D (sortJointKeys input keys) cursor
      have vectorEq : referenceVector input (references.map (e : Equiv.Perm input.Atom))
          (image cursor) = referenceVector input references cursor := by
        simpa only [image] using referenceVector_transport input single e references cursor
      simp only [jointMarkers]
      rw [vectorEq, List.length_map, sourceSorted, imageSorted,
        Certificate.CanonicalSphereKey.sortDesc_eq_of_perm columnPerm]

/-- The actual joint comparison of root-frame children transports. Child build success is derived
from executable membership, and the image reference list is the ordered pointwise image. -/
theorem compareJointAt?_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (references : List input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (childL : left ∈ input.executableLocalizedRerootChildren ⟨t, none⟩)
    (childR : right ∈ input.executableLocalizedRerootChildren ⟨t, none⟩) :
    compareJointAt? input (input.transportOccurrence single e t)
      (input.molecularView (input.transportDescriptorMap e descriptorMap)
        (input.transportOccurrence single e t)) (references.map (e : Equiv.Perm input.Atom)) W D
      (input.transportCursor single e left) (input.transportCursor single e right) =
    compareJointAt? input t (input.molecularView descriptorMap t) references W D left right := by
  have aligned : input.cursorPreviousRootAligned (⟨t, none⟩ : input.LocalizedRerootCursor _) :=
    input.cursorPreviousRootAligned_of_none _ rfl
  have childL' :=
    (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned left).mp childL
  have childR' :=
    (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned right).mp childR
  have validL := input.localizedRerootChild_valid _ left _
    (input.executableLocalizedRerootChildren_declarative _) childL
  have validR := input.localizedRerootChild_valid _ right _
    (input.executableLocalizedRerootChildren_declarative _) childR
  have validL' := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative _) childL'
  have validR' := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative _) childR'
  obtain ⟨a, ha⟩ := buildJoint?_exists input t (input.molecularView descriptorMap t)
    references W D left validL
  obtain ⟨b, hb⟩ := buildJoint?_exists input t (input.molecularView descriptorMap t)
    references W D right validR
  obtain ⟨a', ha'⟩ := buildJoint?_exists input (input.transportOccurrence single e t)
    (input.molecularView (input.transportDescriptorMap e descriptorMap)
      (input.transportOccurrence single e t)) (references.map (e : Equiv.Perm input.Atom)) W D
    (input.transportCursor single e left) validL'
  obtain ⟨b', hb'⟩ := buildJoint?_exists input (input.transportOccurrence single e t)
    (input.molecularView (input.transportDescriptorMap e descriptorMap)
      (input.transportOccurrence single e t)) (references.map (e : Equiv.Perm input.Atom)) W D
    (input.transportCursor single e right) validR'
  have markerL := build_joint_markers_transport input single e descriptorMap tetra t references W D
    _ left (Relation.ReflTransGen.single childL) a a' ha ha'
  have markerR := build_joint_markers_transport input single e descriptorMap tetra t references W D
    _ right (Relation.ReflTransGen.single childR) b b' hb hb'
  have ordinary := ordinary_pair_transport input single e descriptorMap tetra t ⟨t, none⟩ left right
    Relation.ReflTransGen.refl childL childR a.prior b.prior a'.prior b'.prior
    (buildJoint?_prior input t _ references W D _ left a ha)
    (buildJoint?_prior input t _ references W D _ right b hb)
    (buildJoint?_prior input _ _ (references.map (e : Equiv.Perm input.Atom)) W D _ _ a' ha')
    (buildJoint?_prior input _ _ (references.map (e : Equiv.Perm input.Atom)) W D _ _ b' hb')
  simp only [compareJointAt?, ha, hb, ha', hb', Option.bind_eq_bind, Option.bind_some]
  simp only [compareJointKeys, ordinary, markerL, markerR]

/-- The concrete frame-level joint comparator transports across an actual frame-slot transport.
The accumulated reference list is mapped by the same atom permutation, preserving its order. -/
theorem jointBefore_transport {mol : RawMolecule}
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (center : input.TetrahedralCenter)
    (frames : input.ActualFrameSlotTransport single e target center)
    (references : List input.Atom) (W D : Nat) (left right : Fin 4) :
    jointBefore input state' (input.transportOccurrence single e target)
      frames.imageFrame (references.map (e : Equiv.Perm input.Atom)) W D
      (frames.slotPerm left) (frames.slotPerm right) =
    jointBefore input state target frames.sourceFrame references W D left right := by
  have comparison := compareJointAt?_transport input single e (rawStateDescriptorMap input state)
    (rawStateDescriptorMap_tetrahedral input state) target references W D
    (frames.sourceFrame.cursorAt left) (frames.sourceFrame.cursorAt right)
    (frame_child input target frames.sourceFrame frames.sourceComputed left)
    (frame_child input target frames.sourceFrame frames.sourceComputed right)
  unfold jointBefore
  rw [rawStateBefore_transport input single e sym state state' perm unique target center frames
    left right]
  apply congrArg (fun k => Option.bind
    (rawStateBefore input state target frames.sourceFrame left right) k)
  funext prior
  by_cases tie : prior = Ordering.eq
  · rw [if_pos tie, if_pos tie]
    rw [rawStateView_eq_molecularView, rawStateView_eq_molecularView,
      rawStateDescriptorMap_transport input e sym state state' perm unique]
    simp only [frames.cursorAt_eq]
    exact comparison
  · rw [if_neg tie, if_neg tie]

/-- The joint callback's tie eligibility is preserved in both directions: an actual frame-slot
transport carries a joint tie at the source to a joint tie at the image, and back. -/
theorem jointBefore_tie_iff {mol : RawMolecule}
    (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    (sym : StructuralSymmetry mol (relabelOf input (e : Equiv.Perm input.Atom)))
    (state state' : OccurrenceAuxState)
    (perm : state'.Perm (state.map (mapFact (relabelOf input (e : Equiv.Perm input.Atom)))))
    (unique : (state.map (·.key)).Nodup)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (center : input.TetrahedralCenter)
    (frames : input.ActualFrameSlotTransport single e target center)
    (references : List input.Atom) (W D : Nat) (left right : Fin 4) :
    (jointBefore input state' (input.transportOccurrence single e target)
        frames.imageFrame (references.map (e : Equiv.Perm input.Atom)) W D
        (frames.slotPerm left) (frames.slotPerm right) = some Ordering.eq) ↔
      (jointBefore input state target frames.sourceFrame references W D left right
        = some Ordering.eq) := by
  rw [jointBefore_transport input single e sym state state' perm unique target center frames
    references W D left right]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.referenceVector_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.referenceMarks_relabel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.referenceAtoms?_relabel_marks
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.sorted_joint_markers_mapM
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.build_joint_markers_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.compareJointAt?_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.jointBefore_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerCovariance.jointBefore_tie_iff
