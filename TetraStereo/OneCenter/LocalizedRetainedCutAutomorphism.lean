import TetraStereo.OneCenter.DeclarativeCIPRetainedCutArm
import TetraStereo.OneCenter.DeclarativeCIPRetainedRelabelTransport
import TetraStereo.OneCenter.LocalizedRetainedOccurrenceTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Forward automorphism of a retained predecessor cut

One `moleculeGraph.Aut` moves every carrier history. The same map sends a predecessor cut to the
predecessor cut of the image focus: kept nodes, the cut anchor, the incoming parent, and cut
children. Ring-duplicate distance is the outer-root index and is unchanged.

`mapCarrier` is the history map already used by `CertifiedLocalizedCIPInput.mapCarrierNode`.
Occurrence and cursor transport are reused. No cut isomorphism and no occurrence matching are
assumed. The resulting `RootedDigraph.Relabel` is not a `RootedDigraph.Iso`, because the atom
changes. Rings remain. There is no acyclic restriction.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
namespace RetainedCutAutomorphism

open RetainedOccurrenceCarrier
open RetainedCutArm
open scoped Classical

noncomputable section

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

def mapCarrier (perm : Equiv.Perm Atom) : CarrierNode Atom → CarrierNode Atom
  | .real path => .real (path.map perm)
  | .ring path atom => .ring (path.map perm) (perm atom)

@[simp] theorem mapCarrier_real (perm : Equiv.Perm Atom) (path : List Atom) :
    mapCarrier perm (.real path) = .real (path.map perm) := rfl

@[simp] theorem mapCarrier_ring (perm : Equiv.Perm Atom) (path : List Atom) (atom : Atom) :
    mapCarrier perm (.ring path atom) = .ring (path.map perm) (perm atom) := rfl

theorem mapCarrier_injective (perm : Equiv.Perm Atom) : Function.Injective (mapCarrier perm) := by
  intro a b h
  cases a with
  | real path =>
      cases b with
      | real path' =>
          apply congrArg CarrierNode.real
          exact (List.map_injective_iff.mpr (Equiv.injective perm)) (by simpa [mapCarrier] using h)
      | ring _ _ =>
          simp [mapCarrier] at h
  | ring path atom =>
      cases b with
      | real _ => simp [mapCarrier] at h
      | ring path' atom' =>
          simp [mapCarrier] at h
          exact congrArg₂ CarrierNode.ring
            ((List.map_injective_iff.mpr (Equiv.injective perm)) h.1) h.2

theorem rawNewParent_map (perm : Equiv.Perm Atom) (focus : List Atom) (node : CarrierNode Atom) :
    rawNewParent (focus.map perm) (mapCarrier perm node) =
      (rawNewParent focus node).map (mapCarrier perm) := by
  cases node with
  | ring path atom => simp [rawNewParent, mapCarrier]
  | real path =>
      by_cases hpath : path = focus
      · subst hpath
        simp [rawNewParent, mapCarrier]
      · have hnode : CarrierNode.real (path.map perm) ≠ CarrierNode.real (focus.map perm) := by
          intro heq
          exact hpath ((List.map_injective_iff.mpr (Equiv.injective perm)) (by injection heq))
        have hsrc : CarrierNode.real path ≠ CarrierNode.real focus := by
          intro heq
          exact hpath (by injection heq)
        simp only [rawNewParent, mapCarrier, if_neg hnode, if_neg hsrc]
        by_cases hpre : path.length < focus.length ∧ focus.take path.length = path
        · have himg : (path.map perm).length < (focus.map perm).length ∧
              (focus.map perm).take (path.map perm).length = path.map perm := by
            refine ⟨by simpa [List.length_map] using hpre.1, ?_⟩
            rw [List.length_map, take_map perm path.length focus, hpre.2]
          rw [dif_pos hpre, dif_pos himg]
          apply congrArg (fun path => some (CarrierNode.real path))
          simp only [List.map_append, List.map_cons, List.map_nil, List.getElem_map,
            List.length_map]
        · have himg : ¬ ((path.map perm).length < (focus.map perm).length ∧
              (focus.map perm).take (path.map perm).length = path.map perm) := by
            intro hp
            apply hpre
            refine ⟨by simpa [List.length_map] using hp.1, ?_⟩
            have htake := take_map perm path.length focus
            rw [List.length_map] at hp
            exact (List.map_injective_iff.mpr (Equiv.injective perm))
              (htake.symm.trans hp.2)
          rw [dif_neg hpre, dif_neg himg]
          exact congrArg (fun path => some (CarrierNode.real path)) (dropLast_map perm path)

section Molecule

variable {molecule : MoleculeGraph Atom} {root : Atom}

theorem adjacentSteps_map (e : molecule.Aut) :
    ∀ {path : List Atom}, AdjacentSteps molecule path →
      AdjacentSteps molecule (path.map (e : Equiv.Perm Atom))
  | [], _ => trivial
  | [_], _ => by simp [AdjacentSteps]
  | a :: b :: rest, h =>
      ⟨(MoleculeGraph.Aut.adj_iff molecule e a b).2 h.1,
        adjacentSteps_map e (path := b :: rest) h.2⟩

theorem chainFrom_map (e : molecule.Aut) {path : List Atom}
    (h : ChainFrom molecule root path) :
    ChainFrom molecule ((e : Equiv.Perm Atom) root) (path.map (e : Equiv.Perm Atom)) := by
  refine ⟨?_, adjacentSteps_map e h.2⟩
  cases path with
  | nil => simp [ChainFrom] at h
  | cons a as =>
      have ha : a = root := by simpa [ChainFrom] using h.1
      simp [ha]

theorem simpleFrom_map (e : molecule.Aut) {path : List Atom}
    (h : SimpleFrom molecule root path) :
    SimpleFrom molecule ((e : Equiv.Perm Atom) root) (path.map (e : Equiv.Perm Atom)) :=
  ⟨chainFrom_map e h.1,
    (List.nodup_map_iff (Equiv.injective (e : Equiv.Perm Atom))).2 h.2⟩

theorem commonPrefixLength_map (perm : Equiv.Perm Atom) :
    ∀ l r : List Atom,
      commonPrefixLength (l.map perm) (r.map perm) = commonPrefixLength l r
  | [], _ => by simp [commonPrefixLength]
  | a :: as, [] => by simp [commonPrefixLength]
  | a :: as, b :: bs => by
      by_cases h : a = b
      · subst h
        simp [commonPrefixLength, commonPrefixLength_map perm as bs]
      · have hne : perm a ≠ perm b := fun eq => h (Equiv.injective perm eq)
        simp [commonPrefixLength, h, hne]

theorem realArmDepth_map (perm : Equiv.Perm Atom) (focus path : List Atom) :
    realArmDepth (focus.map perm) (path.map perm) = realArmDepth focus path := by
  simp [realArmDepth, commonPrefixLength_map, List.length_map]

theorem armDepth_map (perm : Equiv.Perm Atom) (focus : List Atom) (node : CarrierNode Atom) :
    armDepth (focus.map perm) (mapCarrier perm node) = armDepth focus node := by
  cases node with
  | real path => simp [armDepth, mapCarrier, realArmDepth_map]
  | ring path _ => simp [armDepth, mapCarrier, realArmDepth_map]

theorem ringClosure_map (e : molecule.Aut) {path : List Atom} {atom : Atom}
    (h : RingClosure molecule path atom) :
    RingClosure molecule (path.map (e : Equiv.Perm Atom)) ((e : Equiv.Perm Atom) atom) := by
  let perm := (e : Equiv.Perm Atom)
  obtain ⟨⟨current, hlast, hadj⟩, hmem, hnot⟩ := h
  refine ⟨⟨perm current, ?_, (MoleculeGraph.Aut.adj_iff molecule e current atom).2 hadj⟩, ?_, ?_⟩
  · simp [hlast, perm]
  · exact List.mem_map.2 ⟨atom, hmem, rfl⟩
  · intro hbad
    have hdrop : (path.map perm).dropLast.getLast? = path.dropLast.getLast?.map perm := by
      rw [dropLast_map, getLast?_map]
    rw [hdrop] at hbad
    cases hsrc : path.dropLast.getLast? with
    | none => simp [hsrc] at hbad
    | some a =>
        simp [hsrc] at hbad
        exact hnot (hsrc.trans (congrArg some (Equiv.injective perm hbad)))

theorem valid_map (e : molecule.Aut) {node : CarrierNode Atom}
    (h : CarrierNode.Valid molecule root node) :
    CarrierNode.Valid molecule ((e : Equiv.Perm Atom) root) (mapCarrier (e : Equiv.Perm Atom) node) := by
  cases node with
  | real path => simpa [mapCarrier] using simpleFrom_map e h
  | ring path atom =>
      exact ⟨simpleFrom_map e h.1, ringClosure_map e h.2⟩

def imageNode (e : molecule.Aut) (node : Nodes molecule root) :
    Nodes molecule ((e : Equiv.Perm Atom) root) :=
  match node with
  | ⟨.real path, h⟩ => ⟨.real (path.map (e : Equiv.Perm Atom)), simpleFrom_map e h⟩
  | ⟨.ring path atom, h⟩ =>
      ⟨.ring (path.map (e : Equiv.Perm Atom)) ((e : Equiv.Perm Atom) atom),
        ⟨simpleFrom_map e h.1, ringClosure_map e h.2⟩⟩

def unmapNode (e : molecule.Aut) (node : Nodes molecule ((e : Equiv.Perm Atom) root)) :
    Nodes molecule root :=
  match node with
  | ⟨.real path, h⟩ =>
      ⟨.real (path.map (e : Equiv.Perm Atom).symm), by
          have h' := simpleFrom_map (e⁻¹) h
          simpa [Subgroup.coe_inv, Equiv.symm_apply_apply] using h'⟩
  | ⟨.ring path atom, h⟩ =>
      ⟨.ring (path.map (e : Equiv.Perm Atom).symm) ((e : Equiv.Perm Atom).symm atom), by
          have h' : CarrierNode.Valid molecule ((e⁻¹ : Equiv.Perm Atom) ((e : Equiv.Perm Atom) root))
              (.ring (path.map (e⁻¹ : Equiv.Perm Atom)) ((e⁻¹ : Equiv.Perm Atom) atom)) :=
            ⟨simpleFrom_map (e⁻¹) h.1, ringClosure_map (e⁻¹) h.2⟩
          simpa [Subgroup.coe_inv, Equiv.symm_apply_apply] using h'⟩

theorem imageNode_carrier (e : molecule.Aut) (node : Nodes molecule root) :
    (imageNode e node).1 = mapCarrier (e : Equiv.Perm Atom) node.1 := by
  cases node with
  | mk val hv => cases val <;> rfl

theorem unmapNode_carrier (e : molecule.Aut)
    (node : Nodes molecule ((e : Equiv.Perm Atom) root)) :
    (unmapNode e node).1 = mapCarrier (e : Equiv.Perm Atom).symm node.1 := by
  cases node with
  | mk val hv => cases val <;> rfl

theorem unmap_image (e : molecule.Aut) (node : Nodes molecule root) :
    unmapNode e (imageNode e node) = node := by
  cases node with
  | mk val hv =>
      cases val with
      | real path =>
          apply Subtype.ext
          simp [imageNode, unmapNode, List.map_map]
      | ring path atom =>
          apply Subtype.ext
          simp [imageNode, unmapNode, List.map_map, Equiv.symm_apply_apply]

theorem image_unmap (e : molecule.Aut) (node : Nodes molecule ((e : Equiv.Perm Atom) root)) :
    imageNode e (unmapNode e node) = node := by
  cases node with
  | mk val hv =>
      cases val with
      | real path =>
          apply Subtype.ext
          simp [imageNode, unmapNode, List.map_map]
      | ring path atom =>
          apply Subtype.ext
          simp [imageNode, unmapNode, List.map_map, Equiv.apply_symm_apply]

theorem label_map (perm : Equiv.Perm Atom) (node : CarrierNode Atom) :
    CarrierNode.label (mapCarrier perm node) = mapNodeLabel perm (CarrierNode.label node) := by
  cases node with
  | real path => simp [mapCarrier, CarrierNode.label, mapNodeLabel]
  | ring path atom => simp [mapCarrier, CarrierNode.label, mapNodeLabel, idxOf_map]

theorem mapCarrier_label_provenance (perm : Equiv.Perm Atom) (node : CarrierNode Atom) :
    (CarrierNode.label (mapCarrier perm node)).provenance =
      (CarrierNode.label node).provenance := by
  simpa [mapNodeLabel] using congrArg NodeLabel.provenance (label_map perm node)

theorem ringDuplicate_idxOf_map (perm : Equiv.Perm Atom) (path : List Atom) (atom : Atom) :
    (CarrierNode.label (mapCarrier perm (.ring path atom))).provenance =
      .ringDuplicate (path.idxOf atom) := by
  simp [mapCarrier, CarrierNode.label, idxOf_map]

theorem armChild_iff (e : molecule.Aut) (focus : List Atom)
    (parent node : Nodes molecule root) :
    armChild focus parent node ↔
      armChild (focus.map (e : Equiv.Perm Atom)) (imageNode e parent) (imageNode e node) := by
  let perm := (e : Equiv.Perm Atom)
  constructor
  · intro h
    unfold armChild at h ⊢
    rw [imageNode_carrier, imageNode_carrier, rawNewParent_map perm focus node.1, h]
    rfl
  · intro h
    unfold armChild at h ⊢
    rw [imageNode_carrier, imageNode_carrier, rawNewParent_map perm focus node.1] at h
    cases hraw : rawNewParent focus node.1 with
    | none => simp [hraw] at h
    | some parentNode =>
        simp [hraw] at h
        have hparent : parentNode = parent.1 := mapCarrier_injective perm h
        simpa [hraw, hparent]

theorem armChild_preimage (e : molecule.Aut) (focus : List Atom)
    {parent node : Nodes molecule ((e : Equiv.Perm Atom) root)}
    (h : armChild (focus.map (e : Equiv.Perm Atom)) parent node) :
    armChild focus (unmapNode e parent) (unmapNode e node) := by
  let perm := (e : Equiv.Perm Atom)
  unfold armChild at h ⊢
  have hraw := rawNewParent_map perm.symm (focus.map perm) node.1
  have hfocus : (focus.map perm).map perm.symm = focus := by
    simp [List.map_map]
  rw [hfocus] at hraw
  rw [← unmapNode_carrier e node] at hraw
  rw [h] at hraw
  simp only [Option.map_some] at hraw
  rw [← unmapNode_carrier e parent] at hraw
  exact hraw

theorem inArmSubtree_image (e : molecule.Aut) (focus : List Atom)
    {source node : Nodes molecule root} (h : InArmSubtree focus source node) :
    InArmSubtree (focus.map (e : Equiv.Perm Atom)) (imageNode e source) (imageNode e node) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hchild ih => exact ih.tail ((armChild_iff e focus _ _).1 hchild)

theorem inArmSubtree_unmap (e : molecule.Aut) (focus : List Atom)
    {source node : Nodes molecule ((e : Equiv.Perm Atom) root)}
    (h : InArmSubtree (focus.map (e : Equiv.Perm Atom)) source node) :
    InArmSubtree focus (unmapNode e source) (unmapNode e node) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hchild ih => exact ih.tail (armChild_preimage e focus hchild)

theorem inArmSubtree_preimage (e : molecule.Aut) (focus : List Atom)
    {source node : Nodes molecule root}
    (h : InArmSubtree (focus.map (e : Equiv.Perm Atom)) (imageNode e source) (imageNode e node)) :
    InArmSubtree focus source node := by
  simpa [unmap_image] using inArmSubtree_unmap e focus h

theorem kept_image (e : molecule.Aut) (focus : List Atom)
    (incoming : Option (Nodes molecule root)) (node : Nodes molecule root)
    (hkept : KeptAfterCut focus incoming node) :
    KeptAfterCut (focus.map (e : Equiv.Perm Atom)) (incoming.map (imageNode e))
      (imageNode e node) := by
  intro inc hinc hsub
  cases incoming with
  | none => cases hinc
  | some src =>
      cases hinc
      exact hkept src rfl (inArmSubtree_preimage e focus hsub)

theorem kept_unmap (e : molecule.Aut) (focus : List Atom)
    (incoming : Option (Nodes molecule root))
    (node : Nodes molecule ((e : Equiv.Perm Atom) root))
    (hkept : KeptAfterCut (focus.map (e : Equiv.Perm Atom)) (incoming.map (imageNode e)) node) :
    KeptAfterCut focus incoming (unmapNode e node) := by
  intro inc hinc hsub
  have hsub' := inArmSubtree_image e focus hsub
  rw [image_unmap] at hsub'
  exact hkept (imageNode e inc) (by simp [hinc]) hsub'

theorem kept_iff (e : molecule.Aut) (focus : List Atom)
    (incoming : Option (Nodes molecule root)) (node : Nodes molecule root) :
    KeptAfterCut focus incoming node ↔
      KeptAfterCut (focus.map (e : Equiv.Perm Atom)) (incoming.map (imageNode e))
        (imageNode e node) := by
  constructor
  · exact kept_image e focus incoming node
  · intro h
    simpa [unmap_image] using kept_unmap e focus incoming (imageNode e node) h

theorem cutAnchor_image (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming) :
    CutAnchor (imageNode e focus) (incoming.map (imageNode e)) := by
  cases hanchor with
  | @noCut path hpath =>
      exact CutAnchor.noCut (hpath := simpleFrom_map e hpath)
  | @realChild path hpath inc hchild =>
      exact CutAnchor.realChild ((armChild_iff e path ⟨.real path, hpath⟩ inc).1 hchild)
  | @ringParent path atom h =>
      exact CutAnchor.ringParent (h := ⟨simpleFrom_map e h.1, ringClosure_map e h.2⟩)

theorem predecessor_image (e : molecule.Aut) {focus : List Atom}
    (hfocus : SimpleFrom molecule root focus) (hlen : 1 < focus.length) :
    imageNode e ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩ =
      ⟨.real (focus.map (e : Equiv.Perm Atom)).dropLast,
        SimpleFrom.dropLast (simpleFrom_map e hfocus)
          (by simpa [List.length_map] using hlen)⟩ := by
  apply Subtype.ext
  simp only [imageNode]
  exact congrArg CarrierNode.real (dropLast_map (e : Equiv.Perm Atom) focus).symm

theorem predecessor_child_image (e : molecule.Aut) {focus : List Atom}
    (hfocus : SimpleFrom molecule root focus) (hlen : 1 < focus.length) :
    armChild (focus.map (e : Equiv.Perm Atom))
      (imageNode e ⟨.real focus, hfocus⟩)
      (imageNode e ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩) :=
  (armChild_iff e focus _ _).1 (inward_predecessor_child hfocus hlen)

theorem predecessor_excluded_image (e : molecule.Aut) {focus : List Atom}
    (hfocus : SimpleFrom molecule root focus) (hlen : 1 < focus.length) :
    ¬ KeptAfterCut (focus.map (e : Equiv.Perm Atom))
        (some (imageNode e ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩))
        (imageNode e ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩) := by
  rw [predecessor_image e hfocus hlen]
  exact inward_predecessor_excluded (simpleFrom_map e hfocus)
    (by simpa [List.length_map] using hlen)

private def realNodeEquiv (e : molecule.Aut) (path : List Atom)
    (incoming : Option (Nodes molecule root)) :
    CutNodes path incoming ≃
      CutNodes (path.map (e : Equiv.Perm Atom)) (incoming.map (imageNode e)) where
  toFun node := ⟨imageNode e node.1, kept_image e path incoming node.1 node.2⟩
  invFun node := ⟨unmapNode e node.1, kept_unmap e path incoming node.1 node.2⟩
  left_inv node := Subtype.ext (unmap_image e node.1)
  right_inv node := Subtype.ext (image_unmap e node.1)

private def realAutRelabel (e : molecule.Aut) {path : List Atom}
    (hpath : SimpleFrom molecule root path) (incoming : Option (Nodes molecule root))
    (sourceAnchor : RealCutAnchor path hpath incoming)
    (imageAnchor : RealCutAnchor (path.map (e : Equiv.Perm Atom)) (simpleFrom_map e hpath)
      (incoming.map (imageNode e))) :
    RootedDigraph.Relabel (e : Equiv.Perm Atom)
      (realCutRetainedArm molecule root hpath incoming sourceAnchor)
      (realCutRetainedArm molecule ((e : Equiv.Perm Atom) root) (simpleFrom_map e hpath)
        (incoming.map (imageNode e)) imageAnchor) where
  toEquiv := realNodeEquiv e path incoming
  map_root := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_child := by
    intro a b
    simpa [realCutRetainedArm, cutChild] using armChild_iff e path a.1 b.1
  map_label := by
    intro node
    simp only [realCutRetainedArm]
    have hc : ((realNodeEquiv e path incoming) node).1.1 =
        mapCarrier (e : Equiv.Perm Atom) node.1.1 := by
      simpa [realNodeEquiv] using imageNode_carrier e node.1
    exact hc ▸ (label_map (e : Equiv.Perm Atom) node.1.1).symm
  map_depth := by
    intro node
    simp only [realCutRetainedArm]
    have hc : ((realNodeEquiv e path incoming) node).1.1 =
        mapCarrier (e : Equiv.Perm Atom) node.1.1 := by
      simpa [realNodeEquiv] using imageNode_carrier e node.1
    exact hc ▸ (armDepth_map (e : Equiv.Perm Atom) path node.1.1).symm

private def ringAutRelabel (e : molecule.Aut) {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    RootedDigraph.Relabel (e : Equiv.Perm Atom)
      (ringTerminalArm molecule root h)
      (ringTerminalArm molecule ((e : Equiv.Perm Atom) root)
        ⟨simpleFrom_map e h.1, ringClosure_map e h.2⟩) where
  toEquiv := Equiv.refl PUnit
  map_root := rfl
  map_child := by intro _ _; exact Iff.rfl
  map_label := by
    intro _
    simpa [ringTerminalArm] using (label_map (e : Equiv.Perm Atom) (.ring path atom)).symm
  map_depth := by intro _; rfl

def cutAutRelabel (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming) :
    RootedDigraph.Relabel (e : Equiv.Perm Atom)
      (cutRetainedArm molecule root focus incoming hanchor)
      (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
        (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) :=
  Classical.choice <| by
    cases focus with
    | mk carrier hv =>
        cases carrier with
        | real path =>
            exact ⟨realAutRelabel e hv incoming (realAnchor hanchor)
              (realAnchor (cutAnchor_image e ⟨CarrierNode.real path, hv⟩ incoming hanchor))⟩
        | ring path atom =>
            cases hanchor with
            | ringParent =>
                exact ⟨ringAutRelabel e hv⟩

theorem cut_parent_unique (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (a b n : (cutRetainedArm molecule root focus incoming hanchor).Node)
    (ha : (cutRetainedArm molecule root focus incoming hanchor).child a n)
    (hb : (cutRetainedArm molecule root focus incoming hanchor).child b n) : a = b := by
  cases focus with
  | mk carrier hv =>
      cases carrier with
      | real path =>
          simpa [cutRetainedArm] using
            realCut_unique_parent (hfocus := hv) (hanchor := realAnchor hanchor) ha hb
      | ring path atom =>
          exact False.elim (by simpa [cutRetainedArm, ringTerminalArm] using ha)

theorem cut_nodeObservation (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (rule : ConstitutionalRule)
    (node : (cutRetainedArm molecule root focus incoming hanchor).Node) :
    nodeObservation molecule
        (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
          (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) rule
        ((cutAutRelabel e focus incoming hanchor).toEquiv node) =
      nodeObservation molecule (cutRetainedArm molecule root focus incoming hanchor) rule node :=
  nodeObservation_relabel molecule e (cutAutRelabel e focus incoming hanchor) rule node

theorem cut_ruleKey (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming) (W D : ℕ) :
    ∀ node : (cutRetainedArm molecule root focus incoming hanchor).Node,
      ruleKey molecule
          (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
            (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) W D
          ((cutAutRelabel e focus incoming hanchor).toEquiv node) =
        ruleKey molecule (cutRetainedArm molecule root focus incoming hanchor) W D node :=
  ruleKey_relabel molecule e (cutAutRelabel e focus incoming hanchor) W D

theorem cut_contextualRuleKey (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (outerRoot : Atom) (W D : ℕ) :
    ∀ node : (cutRetainedArm molecule root focus incoming hanchor).Node,
      contextualRuleKey molecule
          (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
            (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor))
          ((e : Equiv.Perm Atom) outerRoot) W D
          ((cutAutRelabel e focus incoming hanchor).toEquiv node) =
        contextualRuleKey molecule (cutRetainedArm molecule root focus incoming hanchor)
          outerRoot W D node :=
  contextualRuleKey_relabel molecule e (cutAutRelabel e focus incoming hanchor) outerRoot W D

theorem cut_retainedContextRuleKey (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (unit : DetectedOccurrence molecule) (W D : ℕ) :
    ∀ node : (cutRetainedArm molecule root focus incoming hanchor).Node,
      retainedContextRuleKey molecule
          (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
            (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor))
          (mapDetected molecule e unit) W D
          ((cutAutRelabel e focus incoming hanchor).toEquiv node) =
        retainedContextRuleKey molecule (cutRetainedArm molecule root focus incoming hanchor)
          unit W D node :=
  retainedContextRuleKey_relabel molecule unit e
    (fun a b n ha hb => cut_parent_unique focus incoming hanchor a b n ha hb)
    (cutAutRelabel e focus incoming hanchor) W D

theorem cut_referenceSelection (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (reads : ReadsAgree molecule e imageMap sourceMap unit
      (cutRetainedArm molecule root focus incoming hanchor)) :
    retainedReferenceSelection molecule imageMap (mapDetected molecule e unit)
        (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
          (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) =
      retainedReferenceSelection molecule sourceMap unit
        (cutRetainedArm molecule root focus incoming hanchor) :=
  retainedReferenceSelection_relabel molecule unit e
    (fun a b n ha hb => cut_parent_unique focus incoming hanchor a b n ha hb) imageMap sourceMap
    reads (cutAutRelabel e focus incoming hanchor)

theorem cut_priorKey (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (reads : ReadsAgree molecule e imageMap sourceMap unit
      (cutRetainedArm molecule root focus incoming hanchor)) (W D : ℕ) :
    retainedCompleteLigandPriorKeyAt molecule imageMap (mapDetected molecule e unit)
        (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
          (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) W D =
      retainedCompleteLigandPriorKeyAt molecule sourceMap unit
        (cutRetainedArm molecule root focus incoming hanchor) W D :=
  retainedCompleteLigandPriorKeyAt_relabel molecule unit e
    (fun a b n ha hb => cut_parent_unique focus incoming hanchor a b n ha hb) imageMap sourceMap
    reads (cutAutRelabel e focus incoming hanchor) W D

theorem cut_rule5Readings (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (reads : ReadsAgree molecule e imageMap sourceMap unit
      (cutRetainedArm molecule root focus incoming hanchor)) (W D : ℕ)
    (common : DescriptorSense) :
    retainedCompleteRule5ReadingsAt molecule imageMap (mapDetected molecule e unit)
        (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
          (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) W D common =
      retainedCompleteRule5ReadingsAt molecule sourceMap unit
        (cutRetainedArm molecule root focus incoming hanchor) W D common :=
  retainedCompleteRule5ReadingsAt_relabel molecule unit e
    (fun a b n ha hb => cut_parent_unique focus incoming hanchor a b n ha hb) imageMap sourceMap
    reads (cutAutRelabel e focus incoming hanchor) W D common

theorem cut_priorKey_mirror (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (reads : ReadsAgree molecule e imageMap sourceMap.reflect unit
      (cutRetainedArm molecule root focus incoming hanchor)) (W D : ℕ) :
    retainedCompleteLigandPriorKeyAt molecule imageMap (mapDetected molecule e unit)
        (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
          (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) W D =
      retainedCompleteLigandPriorKeyAt molecule sourceMap unit
        (cutRetainedArm molecule root focus incoming hanchor) W D :=
  retainedCompleteLigandPriorKeyAt_mirror molecule unit e
    (fun a b n ha hb => cut_parent_unique focus incoming hanchor a b n ha hb) imageMap sourceMap
    reads (cutAutRelabel e focus incoming hanchor) W D

theorem cut_rule5Readings_mirror (e : molecule.Aut) (focus : Nodes molecule root)
    (incoming : Option (Nodes molecule root)) (hanchor : CutAnchor focus incoming)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule)
    (reads : ReadsAgree molecule e imageMap sourceMap.reflect unit
      (cutRetainedArm molecule root focus incoming hanchor)) (W D : ℕ)
    (common : DescriptorSense) :
    retainedCompleteRule5ReadingsAt molecule imageMap (mapDetected molecule e unit)
        (cutRetainedArm molecule ((e : Equiv.Perm Atom) root) (imageNode e focus)
          (incoming.map (imageNode e)) (cutAnchor_image e focus incoming hanchor)) W D common =
      retainedCompleteRule5ReadingsAt molecule sourceMap.reflect unit
        (cutRetainedArm molecule root focus incoming hanchor) W D common :=
  retainedCompleteRule5ReadingsAt_mirror molecule unit e
    (fun a b n ha hb => cut_parent_unique focus incoming hanchor a b n ha hb) imageMap sourceMap
    reads (cutAutRelabel e focus incoming hanchor) W D common

end Molecule

theorem mapCarrier_eq_mapCarrierNode (input : CertifiedLocalizedCIPInput)
    (perm : Equiv.Perm input.Atom) (node : CarrierNode input.Atom) :
    mapCarrier perm node = input.mapCarrierNode perm node := by
  cases node <;> rfl

theorem real_executable_armChild_transport (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (target cursor : input.LocalizedRerootCursor fuel)
    (childMem : cursor ∈ input.executableLocalizedRerootChildren target)
    (real : cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom) :
    ∃ path hpath inc,
      input.occurrenceCarrierNode singleBonded cursor.occurrence = .real path ∧
        input.occurrenceCarrierNode singleBonded target.occurrence = inc.1 ∧
        armChild path ⟨.real path, hpath⟩ inc ∧
        input.occurrenceCarrierNode singleBonded
            (input.transportOccurrence singleBonded e cursor.occurrence) =
          .real (path.map (e : Equiv.Perm input.Atom)) ∧
        input.occurrenceCarrierNode singleBonded
            (input.transportOccurrence singleBonded e target.occurrence) =
          (imageNode (root := cursor.occurrence.1.root) e inc).1 ∧
        armChild (path.map (e : Equiv.Perm input.Atom))
          ⟨.real (path.map (e : Equiv.Perm input.Atom)),
            simpleFrom_map (root := cursor.occurrence.1.root) e hpath⟩
          (imageNode (root := cursor.occurrence.1.root) e inc) := by
  obtain ⟨path, hpath, inc, hcursor, htarget, hchild⟩ :=
    input.realExecutableChild_incomingArmChild singleBonded target cursor childMem real
  refine ⟨path, hpath, inc, hcursor, htarget, hchild, ?_, ?_, ?_⟩
  · have htransport := input.occurrenceCarrierNode_transport singleBonded e cursor.occurrence
    simpa [hcursor, mapCarrier_eq_mapCarrierNode, mapCarrier] using htransport.symm
  · have htransport := input.occurrenceCarrierNode_transport singleBonded e target.occurrence
    have himage : (imageNode (root := cursor.occurrence.1.root) e inc).1 =
        mapCarrier (e : Equiv.Perm input.Atom) inc.1 := imageNode_carrier e inc
    simpa [htarget, himage, mapCarrier_eq_mapCarrierNode] using htransport.symm
  · have hfocus : imageNode (root := cursor.occurrence.1.root) e ⟨.real path, hpath⟩ =
        ⟨.real (path.map (e : Equiv.Perm input.Atom)),
          simpleFrom_map (root := cursor.occurrence.1.root) e hpath⟩ := by
      rfl
    simpa [hfocus] using (armChild_iff (root := cursor.occurrence.1.root) e path
      ⟨.real path, hpath⟩ inc).1 hchild

end

end RetainedCutAutomorphism
end DeclarativeCIP
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.ringDuplicate_idxOf_map
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.kept_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cutAnchor_image
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.armChild_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.predecessor_image
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cutAutRelabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cut_contextualRuleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cut_retainedContextRuleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cut_ruleKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cut_priorKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.cut_rule5Readings
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutAutomorphism.real_executable_armChild_transport
