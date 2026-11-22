import TetraStereo.Engine.RingReferenceFirstSphere
import TetraStereo.Engine.LocalizedChemicalRingPublic

set_option autoImplicit false
set_option maxHeartbeats 150000
set_option Elab.async false

namespace TetraStereo.Engine.RingReferenceObservationSupport
open OneCenter CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.RetainedOccurrenceCarrier
open LocalizedRetainedSourceCutFrames RetainedCutArm
open LocalizedChemicalRingSourceCutWindows LocalizedChemicalRingSourceCutMarker
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointPreparedIndependentModelSourceJointKey
open LocalizedChemicalRingJointPreparedSourceKeys LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingJointPreparedSourceQueries LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingRegeneratedLifetime LocalizedChemicalRingInheritedRefusalCases
open LocalizedGenericMarkedRecalculation (Geometry)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open RingReachableReferencePolicy
noncomputable section
open scoped Classical

private def headBit (columns : JointMarker) (n : Nat) : Nat :=
  ((columns.getD n []).getD 0 []).getD 0 0

private theorem assembled {A : Type} (refs : List A) (n : Fin refs.length)
    (f : A → Nat) (cs : List JointMarker) (W D : Nat) :
    headBit (assembleJointMarker W D refs.length (refs.map f) cs) n = f refs[n] := by
  unfold headBit
  rw [assembleJointMarker_getD W D _ _ _ n.isLt]
  simp [PromotedCanonical.assembleMarker,List.getD_eq_getElem?_getD,n.isLt]

/-- The root address reads the atom named by an arbitrary inherited column,
including when the arm is a terminal ring duplicate. The other descriptors
and all lower addresses are unrestricted. -/
theorem cut_head {A : Type} [Fintype A] [DecidableEq A] (graph : MoleculeGraph A) (root : A)
    (f a : CarrierNode A) (valid : SourceCutAdmissible graph root f a)
    (labels : DescriptorMap (DetectedOccurrence graph)) (refs : List A) (n : Fin refs.length) (W D : Nat) :
    headBit (sourceCutMarker graph root labels f a refs W D) n =
      if CarrierNode.atomOf f = some refs[n] then 1 else 0 := by
  cases f with
  | ring path atom =>
    simp only [sourceCutMarker,if_pos valid]
    rw [assembled]
    simp [CarrierNode.atomOf]
  | real path =>
    simp only [sourceCutMarker,dif_pos valid]
    unfold RealCutArm.markerAt
    rw [jointMarkerKey_eq]
    exact assembled refs n (fun atom => if CarrierNode.atomOf (.real path) = some atom then 1 else 0) _ W D

variable {i : CertifiedLocalizedCIPInput} {m : RawMolecule}
variable (single : i.moleculeGraph.SimpleBonded) (frame : FrameFamily i m)

def ligand (q : SourceQuery i m) (j : Fin 4) : i.Atom :=
  i.detectedMultiCenterMolecule.ligandAtomAt (frame q).1 ((frame q).2.ligandOf j)

private theorem ligand_injective (q : SourceQuery i m) : Function.Injective (ligand frame q) :=
  (i.detectedMultiCenterMolecule.ligandAtomAt_injective (frame q).1).comp (frame q).2.ligandOf.injective

private theorem slot_atom (q : SourceQuery i m) (j : Fin 4) :
    frameAtom? i (frame q).2.frame j = some (ligand frame q j) :=
  Option.map_injective Fin.val_injective ((frame q).2.atomAt_eq j)

private abbrev keys (p : Profile i m) (u : Call i m) (g : Geometry) :=
  sourceKeysAt i single (profileFamily i m p u.query) (frame u.query).2.target
    (frame u.query).2.frame g u.references

private theorem slot_cut_valid (q : SourceQuery i m) (j : Fin 4) :
    let d := (frame q).2
    let cur := d.frame.cursorAt j
    SourceCutAdmissible i.moleculeGraph cur.occurrence.1.root
      (i.occurrenceCarrierNode single cur.occurrence) (i.occurrenceCarrierNode single d.target) := by
  let d := (frame q).2
  have frameExec := (i.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? d.target).symm.trans d.frameExec
  apply sourceCutAdmissible_of_executableChild i single ⟨d.target,none⟩
  rw [← i.localizedOccurrenceFourLigandFrame_cursors_eq_executable d.target d.frame frameExec]
  exact List.get_mem d.frame.cursors (Fin.cast d.frame.length_eq.symm j)

private theorem slot_carrier_atom (q : SourceQuery i m) (j : Fin 4) :
    let cur := (frame q).2.frame.cursorAt j
    CarrierNode.atomOf (i.occurrenceCarrierNode single cur.occurrence) = some (ligand frame q j) := by
  let cur := (frame q).2.frame.cursorAt j
  have carrierAtom (c : CarrierNode i.Atom) : (CarrierNode.label c).atom? = CarrierNode.atomOf c := by cases c <;> rfl
  have atom := congrArg NodeLabel.atom? (i.occurrenceCarrierNode_label single cur.occurrence)
  simp only [carrierAtom,OfficialCIPNode.toDeclarativeLabel] at atom
  exact atom.trans (slot_atom frame q j)

private theorem slot_head (p : Profile i m) (u : Call i m) (g : Geometry) (j : Fin 4) (n : Fin u.references.length) :
    headBit (ofLex (keys single frame p u g j)).2 n =
      if ligand frame u.query j = u.references[n] then 1 else 0 := by
  change headBit (sourceCutMarker _ _ _ _ _ _ _ _) n = _
  rw [cut_head _ _ _ _ (slot_cut_valid single frame u.query j),slot_carrier_atom single frame u.query j]
  simp

/-- A structural collision records both named physical ligands, independently
of geometry, references, or temporary descriptor tables. -/
def Pair (q : SourceQuery i m) (a b : i.Atom) : Prop :=
  ∃ j k : Fin 4, j ≠ k ∧ ligand frame q j = a ∧ ligand frame q k = b ∧
    structuralColumn single frame q j = structuralColumn single frame q k

private theorem cut_label {A : Type} [Fintype A] [DecidableEq A] (graph : MoleculeGraph A)
    (root : A) (f a : CarrierNode A) (valid : SourceCutAdmissible graph root f a) :
    let g := sourceCutArm graph root f a
    g.label g.root = CarrierNode.label f := by
  obtain ⟨hf,ha,anchor⟩ := valid
  rw [sourceCutArm_eq graph root (focus := ⟨f,hf⟩) (incoming := ⟨a,ha⟩) anchor]
  cases f <;> rfl

private theorem pair_number {q : SourceQuery i m} {a b : i.Atom}
    (pair : Pair single frame q a b) : i.moleculeGraph.atomZ a = i.moleculeGraph.atomZ b := by
  let headZ (column : List (Certificate.CanonicalSphereKey.Key ℤ)) : WithBot ℤ :=
    (((column.getD 0 []).getD 0 []).getD 0 ⊥)
  have observe (j : Fin 4) : headZ (structuralColumn single frame q j) =
      ((Int.ofNat (i.moleculeGraph.atomZ (ligand frame q j))) : WithBot ℤ) := by
    let d := (frame q).2
    let cur := d.frame.cursorAt j
    let graph := sourceCutArm i.moleculeGraph cur.occurrence.1.root
      (i.occurrenceCarrierNode single cur.occurrence) (i.occurrenceCarrierNode single d.target)
    have label : graph.label graph.root = CarrierNode.label (i.occurrenceCarrierNode single cur.occurrence) :=
      cut_label _ _ _ _ (slot_cut_valid single frame q j)
    have atom : (graph.label graph.root).atom? = some (ligand frame q j) := by
      rw [label]
      have atomLabel (c : CarrierNode i.Atom) : (CarrierNode.label c).atom? = CarrierNode.atomOf c := by cases c <;> rfl
      exact (atomLabel _).trans (slot_carrier_atom single frame q j)
    change headZ (ruleKeyWithObservations graph _ _ (retainedContextNodeObservation i.moleculeGraph graph
      (i.molecularFrameUnit d.target.1)) graph.root) = _
    rw [ruleKeyWithObservations_eq]
    change (retainedContextNodeObservation i.moleculeGraph graph (i.molecularFrameUnit d.target.1)
      .rule1aAtomicNumber graph.root : WithBot ℤ) = _
    simp [retainedContextNodeObservation,retainedContextRuleValue,priorityValue,ruleValue,nodeAtomicNumber,atom]
  obtain ⟨j,k,_,rfl,rfl,eqn⟩ := pair
  exact Int.ofNat.inj (WithBot.coe_injective ((observe j).symm.trans ((congrArg headZ eqn).trans (observe k))))

/-- The two members of an actual tied pair have equal unmarked columns. Neither
ligand can be a retained reference, even for an arbitrary candidate auxiliary profile. -/
theorem selection_support {p : Profile i m} {u : Call i m} {g a}
    (chosen : Selected single frame p u g a) :
    ∃ b, Pair single frame u.query a b ∧ a ≠ b ∧ a ∉ u.references ∧ b ∉ u.references := by
  obtain ⟨_,j,mem,hj⟩ := chosen
  obtain ⟨_,k,_,apart,tie⟩ := (sourceSelectedSlots_mem_iff _ _).mp mem
  have ne := Ne.symm apart
  have same : keys single frame p u g j = keys single frame p u g k := tie.symm
  have named := Option.some.inj ((slot_atom frame u.query j).symm.trans hj)
  have diff : ligand frame u.query j ≠ ligand frame u.query k := fun e => ne (ligand_injective frame u.query e)
  have marked (n : Fin u.references.length) := congrArg (fun x : LocalizedChemicalRingJointMarkerRanking.RefinedKey =>
    headBit (ofLex x).2 n) same
  have bits (n : Fin u.references.length) : (if ligand frame u.query j = u.references[n] then 1 else 0 : Nat) =
      (if ligand frame u.query k = u.references[n] then 1 else 0 : Nat) :=
    (slot_head single frame p u g j n).symm.trans ((marked n).trans (slot_head single frame p u g k n))
  have projections := congrArg (fun key : LocalizedChemicalRingJointMarkerRanking.RefinedKey =>
    (ofLex ((ofLex ((ofLex ((ofLex key).1)).1)).1)).1) same
  have raw := (structuralColumn_independent single frame p u.query g u.references j).symm.trans
    (projections.trans (structuralColumn_independent single frame p u.query g u.references k))
  subst a
  refine ⟨_,⟨j,k,ne,rfl,rfl,raw⟩,diff,?_,?_⟩
  · intro present
    obtain ⟨index,bound,found⟩ := List.mem_iff_getElem.mp present
    have no := bits ⟨index,bound⟩
    simp [found,Ne.symm diff] at no
  · intro present
    obtain ⟨index,bound,found⟩ := List.mem_iff_getElem.mp present
    have no := bits ⟨index,bound⟩
    simp [found,diff] at no

/-- A report difference requires an ancestor ambiguity containing the older
mark and a descendant ambiguity containing two distinct physical atoms that
both differ from it. All selections survive actual descendant regeneration. -/
theorem disagreement_pairs (admit : m.StereochemicalAdmissible) (q : SourceQuery i m) (g : Geometry)
    (diff : accumulated single frame g [] q ≠ replaced single frame g [] q) :
    ∃ p u : SourceQuery i m, (p = q ∨ StrictDescendant m q.val p.val) ∧ StrictDescendant m p.val u.val ∧
      ∃ old peer fresh other : i.Atom, Pair single frame p old peer ∧ Pair single frame u fresh other ∧
        old ≠ fresh ∧ old ≠ other ∧ fresh ≠ other := by
  obtain ⟨p,u,g₁,g₂,old,fresh,reach,_,below,_,_,first,refs,second,_⟩ :=
    nested_selections single frame admit ⟨q,g,[]⟩ rfl diff
  obtain ⟨tied,j,chosen,atom,_⟩ := second
  have selected : Selected single frame (accumulated single frame) u g₂ fresh := ⟨tied,j,chosen,atom⟩
  obtain ⟨peer,earlier,_,_,_⟩ := selection_support single frame first
  obtain ⟨other,later,different,na,nb⟩ := selection_support single frame selected
  rw [refs] at na nb
  exact ⟨p.query,u.query,reach_descends single frame reach,below,old,peer,fresh,other,earlier,later,
    fun e => na (by simp [e]),fun e => nb (by simp [e]),different⟩

/-- If every descendant ambiguity shares the atom of either possible ancestor
mark, both lifetime policies return the same descriptor at every unmarked call. -/
theorem agree_of_shared_pairs (admit : m.StereochemicalAdmissible)
    (shared : ∀ p u : SourceQuery i m, StrictDescendant m p.val u.val →
      ∀ a b c d, Pair single frame p a b → Pair single frame u c d → a = c ∨ a = d)
    (q : SourceQuery i m) (g : Geometry) :
    accumulated single frame g [] q = replaced single frame g [] q := by
  by_contra diff
  obtain ⟨p,u,_,below,a,b,c,d,earlier,later,ac,ad,_⟩ := disagreement_pairs single frame admit q g diff
  exact (shared p u below a b c d earlier later).elim ac ad

/-- Under shared collision supports a reached nonempty replacement context
already gives four distinct slot keys. This holds for every candidate
descriptor table, before taking a consensus or testing a final report. -/
theorem strict_after_first {p : Profile i m} {root u : Call i m}
    (shared : ∀ parent child : SourceQuery i m, StrictDescendant m parent.val child.val →
      ∀ a b c d, Pair single frame parent a b → Pair single frame child c d → a = c ∨ a = d)
    (empty : root.references = []) (reach : Reach single frame p root u)
    (marked : u.references ≠ []) (g : Geometry) :
    Function.Injective (sourceKeysAt i single (profileFamily i m p u.query)
      (frame u.query).2.target (frame u.query).2.frame g u.references) := by
  obtain unmarked | ⟨old,parent,_,refs,_,_,below,_,chosen⟩ := origin single frame empty reach
  · contradiction
  · by_contra bad
    change ¬ Function.Injective (keys single frame p u g) at bad
    have ex : ∃ j k : Fin 4, keys single frame p u g j = keys single frame p u g k ∧ j ≠ k := by
      by_contra! apart
      exact bad (fun _ _ h => apart _ _ h)
    obtain ⟨j,k,same,ne⟩ := ex
    have tied : j ∈ sourceSelectedSlots (keys single frame p u g) :=
      (sourceSelectedSlots_mem_iff _ _).mpr ⟨List.mem_finRange _,k,List.mem_finRange _,ne.symm,same.symm⟩
    have fresh : Selected single frame p u g (ligand frame u.query j) := ⟨bad,j,tied,slot_atom frame _ _⟩
    obtain ⟨other,earlier,_,_,_⟩ := selection_support single frame chosen
    obtain ⟨later,child,_,left,right⟩ := selection_support single frame fresh
    rw [refs] at left right
    exact (shared _ _ below _ _ _ _ earlier child).elim
      (fun h => left (by simp [h])) (fun h => right (by simp [h]))

/-- A graph-only test. Any number of ambiguous centers is allowed when every
equal-element pair of distinct neighbors consists of the same two actual atoms. -/
theorem agree_of_common_equal_element_neighbors (admit : m.StereochemicalAdmissible)
    (x y : i.Atom)
    (common : ∀ c : i.detectedMultiCenterMolecule.Center, ∀ a b : i.Atom,
      i.moleculeGraph.Adj c.val a → i.moleculeGraph.Adj c.val b → a ≠ b →
      i.moleculeGraph.atomZ a = i.moleculeGraph.atomZ b → (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (q : SourceQuery i m) (g : Geometry) :
    accumulated single frame g [] q = replaced single frame g [] q := by
  have forms {p a b} (ab : Pair single frame p a b) : (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
    have z := pair_number single frame ab
    obtain ⟨j,k,ne,rfl,rfl,_⟩ := ab
    exact common (frame p).1 _ _ (i.detectedMultiCenterMolecule.ligandAtomAt_adj ..)
      (i.detectedMultiCenterMolecule.ligandAtomAt_adj ..) (fun h => ne (ligand_injective frame p h)) z
  apply agree_of_shared_pairs single frame admit _ q g
  intro p u _ a b c d ab cd
  rcases forms ab with ⟨ax,_⟩ | ⟨ay,_⟩ <;> rcases forms cd with ⟨cx,dy⟩ | ⟨cy,dx⟩ <;> simp_all

open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- The common-neighbor-pair condition gives exact membership in the public
whole-molecule report, including both cased descriptors and refusal rows. -/
theorem report_of_common_equal_element_neighbors (input : LocalizedChemicalRing.Input)
    (profile : LocalizedChemicalRing.Profile) (x y : input.certified.Atom)
    (common : ∀ c : input.certified.detectedMultiCenterMolecule.Center, ∀ a b : input.certified.Atom,
      input.certified.moleculeGraph.Adj c.val a → input.certified.moleculeGraph.Adj c.val b → a ≠ b →
      input.certified.moleculeGraph.atomZ a = input.certified.moleculeGraph.atomZ b →
        (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (c : input.certified.detectedMultiCenterMolecule.Center) (value : Option LocalizedTetrahedralRSPseudoDescriptor) :
    (c.val.val,value) ∈ LocalizedChemicalRing.analyze profile input ↔
      replaced input.single (frames input.certified input.molecule input.agreement input.admissible input.supported input.single)
        (inputGeometry input.certified) [] (finalQuery input.certified input.molecule input.agreement c) = value := by
  let fr := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
  have model := actualQueryProfile_sourceModel input.certified input.molecule input.agreement input.admissible input.supported input.single
  have eqn := accumulated_eq_sourceModel input.certified input.molecule input.admissible input.single fr _ model
  rw [LocalizedChemicalRing.analyze_eq_prepared,LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    assignCenter_eq_sourceModel input.certified input.molecule input.agreement input.admissible input.supported input.single model,← eqn]
  exact Eq.congr_left (agree_of_common_equal_element_neighbors input.single fr input.admissible x y common _ _)

end
end TetraStereo.Engine.RingReferenceObservationSupport
assert_kernel_only TetraStereo.Engine.RingReferenceObservationSupport.cut_head
assert_kernel_only TetraStereo.Engine.RingReferenceObservationSupport.selection_support
assert_kernel_only TetraStereo.Engine.RingReferenceObservationSupport.agree_of_common_equal_element_neighbors
assert_kernel_only TetraStereo.Engine.RingReferenceObservationSupport.disagreement_pairs
assert_kernel_only TetraStereo.Engine.RingReferenceObservationSupport.agree_of_shared_pairs
assert_kernel_only TetraStereo.Engine.RingReferenceObservationSupport.strict_after_first
assert_kernel_only TetraStereo.Engine.RingReferenceObservationSupport.report_of_common_equal_element_neighbors
