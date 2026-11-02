






import TetraStereo.OneCenter.DeclarativeCIPRetainedOccurrenceCarrier
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Predecessor cut of the retained occurrence carrier

`retainedArm` reroots the whole outer-root carrier. For a real focus the original parent is
reattached as a child, so the predecessor component remains. The ligand arm entered from a
predecessor is the focus component after that edge is deleted.

`cutRetainedArm focus incoming` is that component, oriented by the same reroot:

* `incoming = none` on a real focus deletes nothing. The result is isomorphic to `realRetainedArm`.
* `incoming = some inc`, where `inc` is any reroot-child of a real focus, deletes the subtree of
  `inc`. The inward predecessor `focus.dropLast` is one such child; an outward neighbor is another.
  Other reroot-children of the focus stay.
* A ring focus is admitted only with its carrier parent. The cut is the one-node terminal arm.

The node set is defined from `armChild` on the independent carrier, not from a production builder.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
namespace RetainedCutArm

open RetainedOccurrenceCarrier
open scoped Classical

noncomputable section

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

variable {molecule : MoleculeGraph Atom} {root : Atom}

/-- Reflexive-transitive reachability in the full reroot at a real focus. -/
def InArmSubtree (focus : List Atom) (source node : Nodes molecule root) : Prop :=
  Relation.ReflTransGen (armChild focus) source node

/-- Nodes that remain after the incoming child's subtree is deleted.
`none` deletes nothing. -/
def KeptAfterCut (focus : List Atom) (incoming : Option (Nodes molecule root))
    (node : Nodes molecule root) : Prop :=
  ∀ inc, incoming = some inc → ¬ InArmSubtree focus inc node

/-- `incoming` is a reroot-child of the real focus, or there is no cut. -/
def RealCutAnchor (focus : List Atom) (hfocus : SimpleFrom molecule root focus)
    (incoming : Option (Nodes molecule root)) : Prop :=
  ∀ inc, incoming = some inc → armChild focus ⟨.real focus, hfocus⟩ inc

/-- How an actual arm is cut out of the carrier.
A real focus may cut nothing or any one reroot-child, inward or outward.
A ring focus is cut from its unique carrier parent. -/
inductive CutAnchor : Nodes molecule root → Option (Nodes molecule root) → Prop where
  | noCut {path : List Atom} {hpath : SimpleFrom molecule root path} :
      CutAnchor ⟨.real path, hpath⟩ none
  | realChild {path : List Atom} {hpath : SimpleFrom molecule root path}
      {inc : Nodes molecule root}
      (hchild : armChild path ⟨.real path, hpath⟩ inc) :
      CutAnchor ⟨.real path, hpath⟩ (some inc)
  | ringParent {path : List Atom} {atom : Atom}
      {h : CarrierNode.Valid molecule root (.ring path atom)} :
      CutAnchor ⟨.ring path atom, h⟩ (some ⟨.real path, h.1⟩)

theorem focus_kept {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming) :
    KeptAfterCut focus incoming ⟨.real focus, hfocus⟩ := by
  intro inc hinc hsub
  have hchild : armChild focus ⟨.real focus, hfocus⟩ inc := hanchor inc hinc
  cases hsub with
  | refl =>
      exact realRetainedArm_not_child_root molecule root hfocus ⟨.real focus, hfocus⟩ hchild
  | tail _ hedge =>
      exact realRetainedArm_not_child_root molecule root hfocus _ hedge

/-- The focus component is closed under the rerooted parent. -/
theorem parent_kept {focus : List Atom} {incoming : Option (Nodes molecule root)}
    {parent node : Nodes molecule root}
    (hchild : armChild focus parent node)
    (hkept : KeptAfterCut focus incoming node) :
    KeptAfterCut focus incoming parent := by
  intro inc hinc hsub
  exact hkept inc hinc (hsub.tail hchild)

theorem realCut_excludes_incoming {focus : List Atom} (_hfocus : SimpleFrom molecule root focus)
    (inc : Nodes molecule root) :
    ¬ KeptAfterCut focus (some inc) inc := by
  intro hkept
  exact hkept inc rfl Relation.ReflTransGen.refl

/-- A different reroot-child of the focus is not in the deleted subtree. -/
theorem realCut_retains_other_neighbor {focus : List Atom}
    (hfocus : SimpleFrom molecule root focus) {inc other : Nodes molecule root}
    (hinc : armChild focus ⟨.real focus, hfocus⟩ inc)
    (hother : armChild focus ⟨.real focus, hfocus⟩ other) (hne : other ≠ inc) :
    KeptAfterCut focus (some inc) other := by
  intro inc' hsome hsub
  cases hsome
  cases hsub with
  | refl =>
      exact hne rfl
  | @tail mid _ hprev hedge =>
      have hmid : mid = ⟨.real focus, hfocus⟩ :=
        realRetainedArm_unique_parent molecule root hfocus hedge hother
      cases hmid
      cases hprev with
      | refl =>
          exact realRetainedArm_not_child_root molecule root hfocus ⟨.real focus, hfocus⟩ hinc
      | tail _ hedge2 =>
          exact realRetainedArm_not_child_root molecule root hfocus _ hedge2

theorem keptNodes_finite (focus : List Atom) (incoming : Option (Nodes molecule root)) :
    Set.Finite {node : Nodes molecule root | KeptAfterCut focus incoming node} := by
  haveI : Finite (Nodes molecule root) := (valid_finite molecule root).to_subtype
  exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)

abbrev CutNodes (focus : List Atom) (incoming : Option (Nodes molecule root)) :=
  {node : Nodes molecule root // KeptAfterCut focus incoming node}

def cutChild (focus : List Atom) (incoming : Option (Nodes molecule root))
    (parent node : CutNodes focus incoming) : Prop :=
  armChild focus parent.1 node.1

theorem cut_reachable {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    (node : CutNodes focus incoming) :
    Relation.ReflTransGen (cutChild focus incoming)
      ⟨⟨.real focus, hfocus⟩, focus_kept hfocus hanchor⟩ node := by
  suffices ∀ n, ∀ node : CutNodes focus incoming, armDepth focus node.1.1 = n →
      Relation.ReflTransGen (cutChild focus incoming)
        ⟨⟨.real focus, hfocus⟩, focus_kept hfocus hanchor⟩ node by
    exact this _ node rfl
  intro n
  induction n with
  | zero =>
      intro node hzero
      have hnode : node.1.1 = .real focus :=
        (armDepth_eq_zero_iff hfocus node.1.2).1 hzero
      have heq : node = ⟨⟨.real focus, hfocus⟩, focus_kept hfocus hanchor⟩ := by
        apply Subtype.ext
        apply Subtype.ext
        exact hnode
      rw [heq]
  | succ n ih =>
      intro node hn
      have hne : node.1.1 ≠ .real focus := by
        intro heq
        have : armDepth focus node.1.1 = 0 := by
          rw [heq]
          exact armDepth_focus focus
        omega
      obtain ⟨parent, hraw, hvalid, hdepth⟩ := rawNewParent_spec hfocus node.1.2 hne
      have hchild : armChild focus ⟨parent, hvalid⟩ node.1 := hraw
      have hparentKept : KeptAfterCut focus incoming ⟨parent, hvalid⟩ :=
        parent_kept hchild node.2
      have hdep : armDepth focus parent = n := by
        have : armDepth focus node.1.1 = n + 1 := hn
        omega
      exact Relation.ReflTransGen.tail
        (ih ⟨⟨parent, hvalid⟩, hparentKept⟩ hdep) hchild

/-- Real focus component after deleting `incoming`'s reroot subtree.
`hanchor` requires `incoming` to be a reroot-child when it is `some`. -/
def realCutRetainedArm (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (incoming : Option (Nodes molecule root))
    (hanchor : RealCutAnchor focus hfocus incoming) : RootedDigraph Atom where
  Node := CutNodes focus incoming
  nodeFintype := @Fintype.ofFinite _ (keptNodes_finite focus incoming).to_subtype
  root := ⟨⟨.real focus, hfocus⟩, focus_kept hfocus hanchor⟩
  child := cutChild focus incoming
  label := fun node => CarrierNode.label node.1.1
  depth := fun node => armDepth focus node.1.1
  root_depth := by
    exact armDepth_focus focus
  child_depth := by
    intro parent node hchild
    exact (realRetainedArm molecule root hfocus).child_depth hchild
  reachable := cut_reachable hfocus hanchor

theorem realCut_nodes_valid {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    (node : (realCutRetainedArm molecule root hfocus incoming hanchor).Node) :
    CarrierNode.Valid molecule root node.1.1 :=
  node.1.2

theorem realCut_node_finite {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming) :
    Finite (realCutRetainedArm molecule root hfocus incoming hanchor).Node := by
  haveI := (realCutRetainedArm molecule root hfocus incoming hanchor).nodeFintype
  infer_instance

theorem someAnchor {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {inc : Nodes molecule root} (hchild : armChild focus ⟨.real focus, hfocus⟩ inc) :
    RealCutAnchor focus hfocus (some inc) := by
  intro inc' h
  have heq : inc' = inc := Option.some_inj.mp h.symm
  subst heq
  exact hchild

theorem noneAnchor {focus : List Atom} (hfocus : SimpleFrom molecule root focus) :
    RealCutAnchor focus hfocus none := by
  intro _ h
  cases h

theorem realAnchor {path : List Atom} {hpath : SimpleFrom molecule root path}
    {incoming : Option (Nodes molecule root)}
    (hanchor : CutAnchor ⟨.real path, hpath⟩ incoming) :
    RealCutAnchor path hpath incoming := by
  cases hanchor with
  | noCut =>
      exact noneAnchor hpath
  | realChild hchild =>
      exact someAnchor hpath hchild

theorem realCut_excludes_incoming_node {focus : List Atom}
    (hfocus : SimpleFrom molecule root focus) {inc : Nodes molecule root}
    (hinc : armChild focus ⟨.real focus, hfocus⟩ inc)
    (node : (realCutRetainedArm molecule root hfocus (some inc) (someAnchor hfocus hinc)).Node) :
    node.1 ≠ inc := by
  intro heq
  have hsub : InArmSubtree focus inc node.1 := by
    rw [heq]
    exact Relation.ReflTransGen.refl
  exact node.2 inc rfl hsub

theorem realCut_other_neighbor_is_child {focus : List Atom}
    (hfocus : SimpleFrom molecule root focus) {inc other : Nodes molecule root}
    (hanchor : RealCutAnchor focus hfocus (some inc))
    (hother : armChild focus ⟨.real focus, hfocus⟩ other) (hne : other ≠ inc) :
    (realCutRetainedArm molecule root hfocus (some inc) hanchor).child
      (realCutRetainedArm molecule root hfocus (some inc) hanchor).root
      ⟨other, realCut_retains_other_neighbor hfocus (hanchor inc rfl) hother hne⟩ :=
  hother

theorem realCut_unique_parent {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    {first second node : (realCutRetainedArm molecule root hfocus incoming hanchor).Node}
    (hfirst : (realCutRetainedArm molecule root hfocus incoming hanchor).child first node)
    (hsecond : (realCutRetainedArm molecule root hfocus incoming hanchor).child second node) :
    first = second := by
  apply Subtype.ext
  exact realRetainedArm_unique_parent molecule root hfocus hfirst hsecond

theorem realCut_acyclic {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    {incoming : Option (Nodes molecule root)}
    (hanchor : RealCutAnchor focus hfocus incoming)
    (node : (realCutRetainedArm molecule root hfocus incoming hanchor).Node) :
    ¬ Relation.TransGen (realCutRetainedArm molecule root hfocus incoming hanchor).child
        node node := by
  intro h
  have hlt := depth_lt_of_transGen
    (graph := realCutRetainedArm molecule root hfocus incoming hanchor) h
  omega

/-- No cut on a real focus is the uncut full reroot. -/
theorem realCut_none_iso_fullReroot (molecule : MoleculeGraph Atom) (root : Atom)
    {focus : List Atom} (hfocus : SimpleFrom molecule root focus) :
    Nonempty (RootedDigraph.Iso
      (realCutRetainedArm molecule root hfocus none (noneAnchor hfocus))
      (realRetainedArm molecule root hfocus)) := by
  refine ⟨{
    toEquiv := {
      toFun := fun node => node.1
      invFun := fun node => ⟨node, by intro _ h; cases h⟩
      left_inv := fun node => Subtype.ext rfl
      right_inv := fun _ => rfl
    }
    map_root := rfl
    map_child := fun _ _ => Iff.rfl
    map_label := fun _ => rfl
    map_depth := fun _ => rfl
  }⟩

/-- Predecessor-cut arm. See `CutAnchor` for the admitted `(focus, incoming)` pairs.
This is the ligand-arm shape: the incoming neighbor's component is absent. -/
def cutRetainedArm (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (incoming : Option (Nodes molecule root))
    (hanchor : CutAnchor focus incoming) : RootedDigraph Atom :=
  match focus with
  | ⟨.real _, hpath⟩ =>
      realCutRetainedArm molecule root hpath incoming (realAnchor hanchor)
  | ⟨.ring _ _, h⟩ =>
      ringTerminalArm molecule root h

/-- A digraph is the predecessor-cut context of an occurrence when it is isomorphic to
`cutRetainedArm`. This is not `FullRerootFaithful` and not `FaithfulExactExpansion`. -/
def RetainedContextArmFaithful (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (incoming : Option (Nodes molecule root))
    (hanchor : CutAnchor focus incoming) (graph : RootedDigraph Atom) : Prop :=
  Nonempty (RootedDigraph.Iso (cutRetainedArm molecule root focus incoming hanchor) graph)

theorem RetainedContextArmFaithful_self (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (incoming : Option (Nodes molecule root))
    (hanchor : CutAnchor focus incoming) :
    RetainedContextArmFaithful molecule root focus incoming hanchor
      (cutRetainedArm molecule root focus incoming hanchor) :=
  ⟨RootedDigraph.Iso.refl _⟩

theorem RetainedContextArmFaithful_iso (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (incoming : Option (Nodes molecule root))
    (hanchor : CutAnchor focus incoming) {graph₁ graph₂ : RootedDigraph Atom}
    (h : RetainedContextArmFaithful molecule root focus incoming hanchor graph₁)
    (iso : RootedDigraph.Iso graph₁ graph₂) :
    RetainedContextArmFaithful molecule root focus incoming hanchor graph₂ := by
  rcases h with ⟨iso₁⟩
  exact ⟨iso₁.trans iso⟩

theorem cutRetainedArm_node_finite (molecule : MoleculeGraph Atom) (root : Atom)
    (focus : Nodes molecule root) (incoming : Option (Nodes molecule root))
    (hanchor : CutAnchor focus incoming) :
    Finite (cutRetainedArm molecule root focus incoming hanchor).Node := by
  match focus with
  | ⟨.real path, hpath⟩ =>
      exact realCut_node_finite hpath (realAnchor hanchor)
  | ⟨.ring _ _, h⟩ =>
      haveI : Fintype (ringTerminalArm molecule root h).Node :=
        (ringTerminalArm molecule root h).nodeFintype
      simpa [cutRetainedArm] using (inferInstance : Finite (ringTerminalArm molecule root h).Node)

theorem cutRetainedArm_real {path : List Atom} (hpath : SimpleFrom molecule root path)
    {incoming : Option (Nodes molecule root)}
    (hanchor : CutAnchor ⟨.real path, hpath⟩ incoming) :
    cutRetainedArm molecule root ⟨.real path, hpath⟩ incoming hanchor =
      realCutRetainedArm molecule root hpath incoming (realAnchor hanchor) :=
  rfl

theorem cutRetainedArm_ringParent {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom)) :
    cutRetainedArm molecule root ⟨.ring path atom, h⟩ (some ⟨.real path, h.1⟩) .ringParent =
      ringTerminalArm molecule root h :=
  rfl

theorem inward_predecessor_child {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (hlen : 1 < focus.length) :
    armChild focus ⟨.real focus, hfocus⟩
      ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩ :=
  (armChild_focus_iff hfocus _).2 (Or.inr ⟨hlen, rfl⟩)

theorem inward_predecessor_excluded {focus : List Atom} (hfocus : SimpleFrom molecule root focus)
    (hlen : 1 < focus.length) :
    ¬ KeptAfterCut focus (some ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩)
        ⟨.real focus.dropLast, SimpleFrom.dropLast hfocus hlen⟩ := by
  intro hkept
  exact hkept _ rfl Relation.ReflTransGen.refl

/-- The carrier parent is the only carrier neighbor of a ring node, and there is no outward child. -/
theorem ring_carrier_neighbor_iff {path : List Atom} {atom : Atom}
    (_h : CarrierNode.Valid molecule root (.ring path atom)) {node : Nodes molecule root} :
    (CarrierNode.Child node.1 (.ring path atom) ∨ CarrierNode.Child (.ring path atom) node.1) ↔
      node.1 = .real path := by
  constructor
  · intro hnb
    rcases hnb with hto | hfrom
    · cases node with
      | mk val hv =>
          cases val with
          | real q =>
              cases hto
              rfl
          | ring _ _ =>
              simp [CarrierNode.Child] at hto
    · simp [CarrierNode.Child] at hfrom
  · intro heq
    cases node with
    | mk val hv =>
        cases heq
        exact Or.inl rfl

theorem ring_cut_terminal {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom))
    (parent child : (cutRetainedArm molecule root ⟨.ring path atom, h⟩
      (some ⟨.real path, h.1⟩) .ringParent).Node) :
    ¬ (cutRetainedArm molecule root ⟨.ring path atom, h⟩
      (some ⟨.real path, h.1⟩) .ringParent).child parent child :=
  fun hchild => hchild

theorem ring_cut_excludes_parent {path : List Atom} {atom : Atom}
    (h : CarrierNode.Valid molecule root (.ring path atom))
    (node : (cutRetainedArm molecule root ⟨.ring path atom, h⟩
      (some ⟨.real path, h.1⟩) .ringParent).Node) :
    (cutRetainedArm molecule root ⟨.ring path atom, h⟩
      (some ⟨.real path, h.1⟩) .ringParent).label node ≠
      CarrierNode.label (.real path) := by
  intro heq
  have hprov := congrArg NodeLabel.provenance heq
  simp [cutRetainedArm, ringTerminalArm, CarrierNode.label] at hprov

/-! ## Chain discrimination

On the two-atom chain `0—1`, the full reroot at `[0,1]` has predecessor `[0]` as a child.
The cut from that predecessor does not contain it, and the two graphs are not isomorphic.
-/

def chainBond : Fin 2 → Fin 2 → Nat
  | 0, 1 => 1
  | 1, 0 => 1
  | _, _ => 0

theorem chainBond_symm (u v : Fin 2) : chainBond u v = chainBond v u := by
  match u, v with
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl

theorem chainBond_self (u : Fin 2) : chainBond u u = 0 := by
  match u with
  | 0 => rfl
  | 1 => rfl

def chainMolecule : MoleculeGraph (Fin 2) where
  atomZ := fun i => i.val + 1
  bond := chainBond
  bond_symm := chainBond_symm
  bond_self := chainBond_self

theorem chain_focus_simple : SimpleFrom chainMolecule 0 [0, 1] := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · refine ⟨?_, trivial⟩
    simp [MoleculeGraph.Adj, chainMolecule, chainBond]
  · simp [List.nodup_cons]

theorem chain_focus_long : 1 < ([0, 1] : List (Fin 2)).length := by
  decide

def chainFocus : Nodes chainMolecule 0 :=
  ⟨.real [0, 1], chain_focus_simple⟩

def chainPred : Nodes chainMolecule 0 :=
  ⟨.real [0], SimpleFrom.root_path⟩

theorem chain_predecessor_is_child : armChild [0, 1] chainFocus chainPred :=
  (armChild_focus_iff chain_focus_simple chainPred).2 (Or.inr ⟨chain_focus_long, rfl⟩)

def chainCutAnchor : CutAnchor chainFocus (some chainPred) :=
  CutAnchor.realChild chain_predecessor_is_child

theorem chain_only_child {node : Nodes chainMolecule 0}
    (hchild : armChild [0, 1] chainFocus node) : node = chainPred := by
  rcases (armChild_focus_iff chain_focus_simple node).1 hchild with hout | ⟨_, hparent⟩
  · cases node with
    | mk val hv =>
        cases val with
        | real path =>
            obtain ⟨atom, rfl⟩ := hout
            have hnot : atom ∉ ([0, 1] : List (Fin 2)) :=
              ((SimpleFrom.append_iff chain_focus_simple).1 hv).2
            match atom with
            | 0 => exact (hnot (by simp)).elim
            | 1 => exact (hnot (by simp)).elim
        | ring path atom =>
            cases hout
            obtain ⟨⟨current, hlast, hadj⟩, _hmem, hpen⟩ := hv.2
            have hcurrent : 1 = current := by
              simpa using hlast
            subst hcurrent
            have hatom : atom = 1 := by
              have hne0 : atom ≠ 0 := by
                intro hz
                apply hpen
                simpa [hz]
              match atom with
              | 0 => exact (hne0 rfl).elim
              | 1 => rfl
            subst hatom
            simp [MoleculeGraph.Adj, chainMolecule, chainBond] at hadj
  · exact Subtype.ext (by simpa [chainPred] using hparent)

theorem chain_cut_omits
    (node : (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor).Node) :
    node.1 ≠ chainPred := by
  intro heq
  have hsub : InArmSubtree [0, 1] chainPred node.1 := by
    rw [heq]
    exact Relation.ReflTransGen.refl
  exact node.2 chainPred rfl hsub

theorem chain_cut_only_root
    (node : (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor).Node) :
    node = (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor).root := by
  have hreach :=
    (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor).reachable node
  induction hreach with
  | refl => rfl
  | @tail _ current _ hedge ih =>
      cases ih
      exact ((chain_cut_omits current) (chain_only_child hedge)).elim

theorem chain_predecessor_depth :
    (realRetainedArm chainMolecule 0 chain_focus_simple).depth chainPred = 1 := by
  simp [realRetainedArm, chainPred, armDepth, realArmDepth, commonPrefixLength]

theorem chain_full_not_cut_iso :
    ¬ Nonempty (RootedDigraph.Iso
        (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor)
        (realRetainedArm chainMolecule 0 chain_focus_simple)) := by
  intro ⟨iso⟩
  have hdepth := (iso.symm.map_depth chainPred).symm
  rw [chain_predecessor_depth] at hdepth
  have honly := chain_cut_only_root (iso.symm.toEquiv chainPred)
  rw [honly] at hdepth
  have hzero :=
    (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor).root_depth
  rw [hzero] at hdepth
  cases hdepth

/-- On `0—1`, the uncut reroot at `B = [0,1]` contains predecessor `A = [0]` as a child.
The cut entered from `A` omits `A`, so the cut is not the full reroot. -/
theorem chain_discrimination :
    armChild [0, 1] chainFocus chainPred ∧
      (∀ node : (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor).Node,
        node.1 ≠ chainPred) ∧
      ¬ Nonempty (RootedDigraph.Iso
          (cutRetainedArm chainMolecule 0 chainFocus (some chainPred) chainCutAnchor)
          (realRetainedArm chainMolecule 0 chain_focus_simple)) :=
  ⟨chain_predecessor_is_child, chain_cut_omits, chain_full_not_cut_iso⟩

end

end RetainedCutArm
end DeclarativeCIP
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.focus_kept
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.parent_kept
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_excludes_incoming
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_retains_other_neighbor
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_excludes_incoming_node
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_other_neighbor_is_child
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_unique_parent
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_acyclic
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_none_iso_fullReroot
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.realCut_node_finite
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.RetainedContextArmFaithful_self
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.RetainedContextArmFaithful_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.cutRetainedArm_node_finite
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.inward_predecessor_child
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.inward_predecessor_excluded
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.ring_carrier_neighbor_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.ring_cut_terminal
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.ring_cut_excludes_parent
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.RetainedCutArm.chain_discrimination
