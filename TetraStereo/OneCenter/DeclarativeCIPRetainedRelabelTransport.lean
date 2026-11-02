import TetraStereo.OneCenter.DeclarativeCIPObservedOrdinaryKey
import TetraStereo.OneCenter.DeclarativeCIPObservedReadingKeyProjection
import TetraStereo.OneCenter.DeclarativeCIPRetainedCompleteSignatures
import TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport
import TetraStereo.OneCenter.Symmetry
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Relabel transport for one molecular automorphism

`RootedDigraph.Iso.map_label` keeps the atom. A molecular automorphism sends that atom to a
different atom, so the carrier here is `RootedDigraph.Relabel`, not an isomorphism. Provenance,
including a ring-duplicate distance, is copied. Atomic number, mass, charge, bond order, and
simple-graph distance agree because the permutation is a `MoleculeGraph.Aut`.

Constitutional, contextual, and retained-context keys use only that preservation and, for the
retained walk, unique parents. Ordinary, rank, reference, prior, and Rule 5 keys add `ReadsAgree`:
each real node whose context occurrence is read uses the image descriptor map at the transported
occurrence. That hypothesis is one reachable read, not a selected reference, a canonical order,
or a comparator result. Mirror covariance is this transport into `descriptorMap.reflect`, then
the existing reflection lemmas.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP

open Certificate.CanonicalSphereKey (sortDesc)
open scoped Classical
open LocalizedRetainedDescriptorTransport

noncomputable section

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

def mapNodeLabel (perm : Equiv.Perm Atom) (label : NodeLabel Atom) : NodeLabel Atom where
  atom? := label.atom?.map perm
  provenance := label.provenance

@[simp] theorem mapNodeLabel_atom (perm : Equiv.Perm Atom) (label : NodeLabel Atom) :
    (mapNodeLabel perm label).atom? = label.atom?.map perm := rfl

@[simp] theorem mapNodeLabel_provenance (perm : Equiv.Perm Atom) (label : NodeLabel Atom) :
    (mapNodeLabel perm label).provenance = label.provenance := rfl

theorem mapNodeLabel_symm_apply (perm : Equiv.Perm Atom) (label : NodeLabel Atom) :
    mapNodeLabel perm.symm (mapNodeLabel perm label) = label := by
  cases label with
  | mk atom? provenance =>
      cases atom? <;> simp [mapNodeLabel, Equiv.symm_apply_apply]

namespace RootedDigraph

/-- Rooted-digraph transport that moves atom names by one permutation and keeps provenance. -/
structure Relabel (perm : Equiv.Perm Atom) (left right : RootedDigraph Atom) where
  toEquiv : left.Node ≃ right.Node
  map_root : toEquiv left.root = right.root
  map_child : ∀ a b, left.child a b ↔ right.child (toEquiv a) (toEquiv b)
  map_label : ∀ node, mapNodeLabel perm (left.label node) = right.label (toEquiv node)
  map_depth : ∀ node, left.depth node = right.depth (toEquiv node)

def Relabel.symm {perm : Equiv.Perm Atom} {left right : RootedDigraph Atom}
    (relabel : Relabel perm left right) : Relabel perm.symm right left where
  toEquiv := relabel.toEquiv.symm
  map_root := by
    apply relabel.toEquiv.injective
    simp [relabel.map_root]
  map_child := by
    intro a b
    simpa using (relabel.map_child (relabel.toEquiv.symm a) (relabel.toEquiv.symm b)).symm
  map_label := by
    intro node
    have h := relabel.map_label (relabel.toEquiv.symm node)
    simp only [Equiv.apply_symm_apply] at h
    have h' := congrArg (mapNodeLabel perm.symm) h
    simp only [mapNodeLabel_symm_apply] at h'
    exact h'.symm
  map_depth := by
    intro node
    simpa using (relabel.map_depth (relabel.toEquiv.symm node)).symm

end RootedDigraph

section Distance

variable (molecule : MoleculeGraph Atom)

private def mapWalk (G : SimpleGraph Atom) (perm : Equiv.Perm Atom)
    (preserve : ∀ u v, G.Adj u v → G.Adj (perm u) (perm v)) :
    ∀ {u v : Atom}, G.Walk u v → G.Walk (perm u) (perm v)
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons (preserve _ _ h) (mapWalk G perm preserve p)

private theorem mapWalk_length (G : SimpleGraph Atom) (perm : Equiv.Perm Atom)
    (preserve : ∀ u v, G.Adj u v → G.Adj (perm u) (perm v)) {u v : Atom}
    (p : G.Walk u v) : (mapWalk G perm preserve p).length = p.length := by
  induction p with
  | nil => simp [mapWalk]
  | cons h p ih => simp [mapWalk, ih]

private theorem dist_le_of_perm (G : SimpleGraph Atom) (perm : Equiv.Perm Atom)
    (hadj : ∀ u v, G.Adj (perm u) (perm v) ↔ G.Adj u v) (u v : Atom) :
    G.dist (perm u) (perm v) ≤ G.dist u v := by
  by_cases hreach : G.Reachable u v
  · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
    have hlen := mapWalk_length G perm (fun a b hab => (hadj a b).2 hab) p
    simpa [hlen, hp] using G.dist_le (mapWalk G perm (fun a b hab => (hadj a b).2 hab) p)
  · have hnot : ¬ G.Reachable (perm u) (perm v) := by
      intro hr
      rcases hr with ⟨p⟩
      apply hreach
      have preserve : ∀ a b, G.Adj a b → G.Adj (perm.symm a) (perm.symm b) := by
        intro a b hab
        exact (hadj (perm.symm a) (perm.symm b)).1
          (by simpa [Equiv.apply_symm_apply] using hab)
      exact ⟨(Equiv.symm_apply_apply perm u) ▸ (Equiv.symm_apply_apply perm v) ▸
        mapWalk G perm.symm preserve p⟩
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hnot,
      SimpleGraph.dist_eq_zero_of_not_reachable hreach]

theorem dist_perm (G : SimpleGraph Atom) (perm : Equiv.Perm Atom)
    (hadj : ∀ u v, G.Adj (perm u) (perm v) ↔ G.Adj u v) (u v : Atom) :
    G.dist (perm u) (perm v) = G.dist u v := by
  apply le_antisymm
  · exact dist_le_of_perm G perm hadj u v
  · have hsymm : ∀ a b, G.Adj (perm.symm a) (perm.symm b) ↔ G.Adj a b := by
      intro a b
      simpa using (hadj (perm.symm a) (perm.symm b)).symm
    simpa using dist_le_of_perm G perm.symm hsymm (perm u) (perm v)

theorem dist_aut (e : molecule.Aut) (u v : Atom) :
    molecule.underlyingSimpleGraph.dist ((e : Equiv.Perm Atom) u) ((e : Equiv.Perm Atom) v) =
      molecule.underlyingSimpleGraph.dist u v :=
  dist_perm molecule.underlyingSimpleGraph (e : Equiv.Perm Atom)
    (fun a b => by simpa using MoleculeGraph.Aut.adj_iff molecule e a b) u v

end Distance

section Lists

theorem reverse_map (perm : Equiv.Perm Atom) (l : List Atom) :
    (l.map perm).reverse = l.reverse.map perm := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.reverse_cons, List.map_append, List.map_nil, ih]

theorem getLast?_map (perm : Equiv.Perm Atom) :
    ∀ l : List Atom, (l.map perm).getLast? = l.getLast?.map perm
  | [] => rfl
  | [_] => rfl
  | _ :: b :: rest => getLast?_map perm (b :: rest)

theorem dropLast_map (perm : Equiv.Perm Atom) (l : List Atom) :
    (l.map perm).dropLast = l.dropLast.map perm := by
  induction l with
  | nil => rfl
  | cons _ as _ =>
      cases as with
      | nil => rfl
      | cons _ _ => simp [List.map_cons]

theorem take_map (perm : Equiv.Perm Atom) :
    ∀ (n : Nat) (l : List Atom), (l.map perm).take n = (l.take n).map perm
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: as => congrArg (List.cons (perm a)) (take_map perm n as)

theorem idxOf_map (perm : Equiv.Perm Atom) (atom : Atom) :
    ∀ path : List Atom, (path.map perm).idxOf (perm atom) = path.idxOf atom
  | [] => by simp
  | head :: tail => by
      simp only [List.map_cons]
      by_cases h : head = atom
      · subst h
        rw [List.idxOf_cons_eq (tail.map perm) rfl, List.idxOf_cons_eq tail rfl]
      · have hne : perm head ≠ perm atom := fun eq => h (Equiv.injective perm eq)
        rw [List.idxOf_cons_ne (tail.map perm) hne, List.idxOf_cons_ne tail h,
          idxOf_map perm atom tail]

end Lists

section Constitution

variable (molecule : MoleculeGraph Atom)

theorem ruleValue_mapLabel (e : molecule.Aut) (rule : ConstitutionalRule) (position : List ℕ)
    (label : NodeLabel Atom) :
    ruleValue molecule rule position (some (mapNodeLabel (e : Equiv.Perm Atom) label)) =
      ruleValue molecule rule position (some label) := by
  cases rule with
  | rule1aAtomicNumber =>
      cases label with
      | mk atom? _ =>
          cases atom? with
          | none => simp [ruleValue, nodeAtomicNumber, mapNodeLabel]
          | some atom =>
              simp [ruleValue, nodeAtomicNumber, mapNodeLabel, MoleculeGraph.Aut.atomZ_eq]
  | rule1bDuplicateNodeProximity =>
      cases label with
      | mk _ provenance =>
          cases provenance <;> simp [ruleValue, nodeRule1bRootDistance, mapNodeLabel]
  | rule2AtomicMass =>
      cases label with
      | mk atom? provenance =>
          cases atom? <;> cases provenance <;>
            simp [ruleValue, nodeAtomicMass, mapNodeLabel, MoleculeGraph.Aut.atomMass_eq]

variable {left right : RootedDigraph Atom}

theorem nodeObservation_relabel (e : molecule.Aut)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right)
    (rule : ConstitutionalRule) (node : left.Node) :
    nodeObservation molecule right rule (relabel.toEquiv node) =
      nodeObservation molecule left rule node := by
  simp only [nodeObservation]
  rw [← relabel.map_depth node, ← relabel.map_label node]
  exact congrArg (priorityValue rule) (ruleValue_mapLabel molecule e rule _ _)

local instance relabelLeftNode (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem childList_relabel_perm {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right) (node : left.Node) :
    (right.childList (relabel.toEquiv node)).Perm ((left.childList node).map relabel.toEquiv) := by
  apply (List.perm_ext_iff_of_nodup (right.childList_nodup _)
      ((left.childList_nodup node).map (Equiv.injective relabel.toEquiv))).2
  intro child
  rw [right.mem_childList, List.mem_map]
  constructor
  · intro h
    refine ⟨relabel.toEquiv.symm child, ?_, by simp⟩
    rw [left.mem_childList, relabel.map_child]
    simpa using h
  · rintro ⟨original, horiginal, rfl⟩
    exact (relabel.map_child node original).1 ((left.mem_childList).1 horiginal)

theorem width_eq_of_relabel {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right) : left.width = right.width :=
  Fintype.card_congr relabel.toEquiv

theorem height_eq_of_relabel {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right) : left.height = right.height := by
  apply le_antisymm
  · apply Finset.sup_le
    intro node _
    rw [relabel.map_depth node]
    exact right.depth_le_height _
  · apply Finset.sup_le
    intro node _
    have h := relabel.map_depth (relabel.toEquiv.symm node)
    simp only [Equiv.apply_symm_apply] at h
    rw [← h]
    exact left.depth_le_height _

theorem ruleKeyWithObservations_relabel {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right)
    (leftObserve : ConstitutionalRule → left.Node → ℤ)
    (rightObserve : ConstitutionalRule → right.Node → ℤ) (W D : ℕ)
    (observeEq : ∀ rule node, rightObserve rule (relabel.toEquiv node) = leftObserve rule node) :
    ∀ node : left.Node,
      ruleKeyWithObservations right W D rightObserve (relabel.toEquiv node) =
        ruleKeyWithObservations left W D leftObserve node := by
  refine node_induction left (motive := fun node =>
    ruleKeyWithObservations right W D rightObserve (relabel.toEquiv node) =
      ruleKeyWithObservations left W D leftObserve node) ?_
  intro node ih
  rw [ruleKeyWithObservations_eq, ruleKeyWithObservations_eq]
  have hchildren :
      sortDesc ((right.childList (relabel.toEquiv node)).map
        (ruleKeyWithObservations right W D rightObserve)) =
      sortDesc ((left.childList node).map (ruleKeyWithObservations left W D leftObserve)) := by
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_relabel_perm relabel node).map
        (ruleKeyWithObservations right W D rightObserve)), List.map_map]
    congr 1
    exact List.map_congr_left fun child hchild => ih child ((left.mem_childList).1 hchild)
  simp only [ruleComponentWithObservations, observeEq, hchildren]

theorem ruleKey_relabel (e : molecule.Aut)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    ∀ node : left.Node,
      ruleKey molecule right W D (relabel.toEquiv node) = ruleKey molecule left W D node := by
  intro node
  rw [← ruleKeyWithObservations_eq_ruleKey, ← ruleKeyWithObservations_eq_ruleKey]
  exact ruleKeyWithObservations_relabel relabel (nodeObservation molecule left)
    (nodeObservation molecule right) W D
    (fun rule current => nodeObservation_relabel molecule e relabel rule current) node

end Constitution

section Context

variable (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}

local instance relabelContextNode (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem contextualRuleValue_relabel (e : molecule.Aut)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (outerRoot : Atom)
    (rule : ConstitutionalRule) (node : left.Node) :
    contextualRuleValue molecule right ((e : Equiv.Perm Atom) outerRoot) rule
        (relabel.toEquiv node) =
      contextualRuleValue molecule left outerRoot rule node := by
  cases rule with
  | rule1aAtomicNumber =>
      simp only [contextualRuleValue]
      rw [← relabel.map_depth node, ← relabel.map_label node]
      exact ruleValue_mapLabel molecule e .rule1aAtomicNumber _ _
  | rule2AtomicMass =>
      simp only [contextualRuleValue]
      rw [← relabel.map_depth node, ← relabel.map_label node]
      exact ruleValue_mapLabel molecule e .rule2AtomicMass _ _
  | rule1bDuplicateNodeProximity =>
      simp only [contextualRuleValue]
      rw [← relabel.map_label node]
      cases hlabel : left.label node with
      | mk atom? provenance =>
          cases atom? with
          | none =>
              rw [← relabel.map_depth node]
              simp [ruleValue, nodeRule1bRootDistance, mapNodeLabel]
          | some atom =>
              cases provenance with
              | realAtom =>
                  simp [mapNodeLabel, dist_aut molecule e outerRoot atom]
              | multipleBondDuplicate distance =>
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .multipleBondDuplicate distance⟩
              | ringDuplicate distance =>
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .ringDuplicate distance⟩
              | phantom distance =>
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .phantom distance⟩
              | lonePair distance =>
                  rw [← relabel.map_depth node]
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .lonePair distance⟩
              | auxiliary distance =>
                  rw [← relabel.map_depth node]
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .auxiliary distance⟩

theorem contextualNodeObservation_relabel (e : molecule.Aut)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (outerRoot : Atom)
    (rule : ConstitutionalRule) (node : left.Node) :
    contextualNodeObservation molecule right ((e : Equiv.Perm Atom) outerRoot) rule
        (relabel.toEquiv node) =
      contextualNodeObservation molecule left outerRoot rule node := by
  simp [contextualNodeObservation, contextualRuleValue_relabel molecule e relabel outerRoot]

theorem contextualRuleKey_relabel (e : molecule.Aut)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (outerRoot : Atom)
    (W D : ℕ) :
    ∀ node : left.Node,
      contextualRuleKey molecule right ((e : Equiv.Perm Atom) outerRoot) W D
          (relabel.toEquiv node) =
        contextualRuleKey molecule left outerRoot W D node := by
  intro node
  unfold contextualRuleKey
  exact ruleKeyWithObservations_relabel relabel
    (contextualNodeObservation molecule left outerRoot)
    (contextualNodeObservation molecule right ((e : Equiv.Perm Atom) outerRoot)) W D
    (fun rule current =>
      contextualNodeObservation_relabel molecule e relabel outerRoot rule current) node

end Context

section Ancestors

variable {left right : RootedDigraph Atom}

theorem no_parent_root (graph : RootedDigraph Atom) (parent : graph.Node) :
    ¬ graph.child parent graph.root := by
  intro hedge
  have := graph.child_depth hedge
  rw [graph.root_depth] at this
  omega

theorem ancestorPath_image {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right) {node : left.Node}
    {path : List (Option Atom)} (h : AncestorPath left node path) :
    AncestorPath right (relabel.toEquiv node) (path.map (Option.map perm)) := by
  induction h with
  | root =>
      have hatom : Option.map perm (left.label left.root).atom? =
          (right.label right.root).atom? := by
        have hlabel := relabel.map_label left.root
        rw [relabel.map_root] at hlabel
        simpa [mapNodeLabel] using congrArg NodeLabel.atom? hlabel
      rw [relabel.map_root]
      simpa [List.map_singleton, hatom] using (AncestorPath.root (graph := right))
  | @step parent node path hchild _ ih =>
      have hatom : Option.map perm (left.label node).atom? =
          (right.label (relabel.toEquiv node)).atom? := by
        simpa [mapNodeLabel] using congrArg NodeLabel.atom? (relabel.map_label node)
      simpa [List.map_append, hatom] using
        AncestorPath.step ((relabel.map_child parent node).1 hchild) ih

theorem ancestorChain_image {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right) {node : left.Node}
    {chain : List left.Node} (h : AncestorChain left node chain) :
    AncestorChain right (relabel.toEquiv node) (chain.map relabel.toEquiv) := by
  induction h with
  | root =>
      simpa [List.map_cons, List.map_nil, relabel.map_root] using
        (AncestorChain.root (graph := right))
  | @step parent node chain hchild _ ih =>
      simpa [List.map_append] using
        AncestorChain.step ((relabel.map_child parent node).1 hchild) ih

theorem ancestorChain_unique (graph : RootedDigraph Atom)
    (parentUnique : ∀ a b n, graph.child a n → graph.child b n → a = b)
    {node : graph.Node} {first second : List graph.Node}
    (hfirst : AncestorChain graph node first) (hsecond : AncestorChain graph node second) :
    first = second := by
  induction hfirst generalizing second with
  | root =>
      cases hsecond with
      | root => rfl
      | step hedge _ => exact (no_parent_root graph _ hedge).elim
  | step hedge _ ih =>
      cases hsecond with
      | root => exact (no_parent_root graph _ hedge).elim
      | step hedge' hchain' =>
          have hparent := parentUnique _ _ _ hedge hedge'
          subst hparent
          rw [ih hchain']

theorem ancestorPath_relabel_eq {perm : Equiv.Perm Atom}
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (relabel : RootedDigraph.Relabel perm left right) (node : left.Node) :
    ancestorPath right (relabel.toEquiv node) =
      (ancestorPath left node).map (List.map (Option.map perm)) := by
  obtain ⟨path, hpath⟩ := exists_ancestorPath left node
  have hunique : ∀ other, AncestorPath left node other → other = path :=
    fun other hother => ancestorPath_unique_of_parent_unique (no_parent_root left)
      (fun hfirst hsecond => parentUnique _ _ _ hfirst hsecond) hother hpath
  have himage := ancestorPath_image relabel hpath
  have huniqueR : ∀ other, AncestorPath right (relabel.toEquiv node) other →
      other = path.map (Option.map perm) := by
    intro other hother
    have hback := ancestorPath_image relabel.symm hother
    have hbackNode : relabel.symm.toEquiv (relabel.toEquiv node) = node :=
      Equiv.symm_apply_apply relabel.toEquiv node
    rw [hbackNode] at hback
    have hsource : other.map (Option.map perm.symm) = path := hunique _ hback
    simpa [List.map_map, Option.map_map, Equiv.apply_symm_apply] using
      congrArg (List.map (Option.map perm)) hsource
  have hex : ∃! p, AncestorPath left node p := ⟨path, hpath, hunique⟩
  have hexR : ∃! p, AncestorPath right (relabel.toEquiv node) p :=
    ⟨path.map (Option.map perm), himage, huniqueR⟩
  rw [ancestorPath, ancestorPath, dif_pos hex, dif_pos hexR]
  exact congrArg some
    ((huniqueR _ (Classical.choose_spec hexR.exists)).trans
      (congrArg (List.map (Option.map perm))
        (hunique _ (Classical.choose_spec hex.exists)).symm))

theorem ancestorChain_relabel_eq {perm : Equiv.Perm Atom}
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (relabel : RootedDigraph.Relabel perm left right) (node : left.Node) :
    ancestorChain right (relabel.toEquiv node) =
      (ancestorChain left node).map relabel.toEquiv := by
  obtain ⟨chain, hchain⟩ := exists_ancestorChain left node
  have hunique : ∀ other, AncestorChain left node other → other = chain :=
    fun other hother => ancestorChain_unique left parentUnique hother hchain
  have himage := ancestorChain_image relabel hchain
  have huniqueR : ∀ other, AncestorChain right (relabel.toEquiv node) other →
      other = chain.map relabel.toEquiv := by
    intro other hother
    have hback := ancestorChain_image relabel.symm hother
    have hbackNode : relabel.symm.toEquiv (relabel.toEquiv node) = node :=
      Equiv.symm_apply_apply relabel.toEquiv node
    rw [hbackNode] at hback
    have hsource : other.map relabel.toEquiv.symm = chain := hunique _ hback
    simpa [List.map_map, Equiv.apply_symm_apply] using
      congrArg (List.map relabel.toEquiv) hsource
  have hex : ∃! c, AncestorChain left node c := ⟨chain, hchain, hunique⟩
  have hexR : ∃! c, AncestorChain right (relabel.toEquiv node) c :=
    ⟨chain.map relabel.toEquiv, himage, huniqueR⟩
  rw [ancestorChain, ancestorChain, dif_pos hex, dif_pos hexR]
  exact (huniqueR _ (Classical.choose_spec hexR.exists)).trans
    (congrArg (List.map relabel.toEquiv)
      (hunique _ (Classical.choose_spec hex.exists)).symm)

theorem mapM_optionMap (perm : Equiv.Perm Atom) :
    ∀ path : List (Option Atom),
      (path.map (Option.map perm)).mapM id = (path.mapM id).map (List.map perm)
  | [] => by simp
  | none :: tail => by simp [List.mapM_cons, mapM_optionMap perm tail]
  | some atom :: tail => by
      simp only [List.map_cons, Option.map_some, List.mapM_cons, mapM_optionMap perm tail]
      cases tail.mapM id <;> simp

theorem ancestorAtoms_relabel {perm : Equiv.Perm Atom}
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (relabel : RootedDigraph.Relabel perm left right) (node : left.Node) :
    ancestorAtoms right (relabel.toEquiv node) =
      (ancestorAtoms left node).map (List.map perm) := by
  rw [ancestorAtoms, ancestorAtoms, ancestorPath_relabel_eq parentUnique relabel node]
  cases hpath : ancestorPath left node with
  | none => simp
  | some path => simpa [hpath] using mapM_optionMap perm path

end Ancestors

section OccurrenceMap

variable (molecule : MoleculeGraph Atom)

theorem neighbor_card_aut (e : molecule.Aut) (atom : Atom) :
    (molecule.neighborFinset ((e : Equiv.Perm Atom) atom)).card =
      (molecule.neighborFinset atom).card := by
  let perm := (e : Equiv.Perm Atom)
  symm
  apply Finset.card_bij (fun u (_ : u ∈ molecule.neighborFinset atom) => perm u)
  · intro u hu
    rw [MoleculeGraph.mem_neighborFinset]
    exact (MoleculeGraph.Aut.adj_iff molecule e atom u).2
      ((MoleculeGraph.mem_neighborFinset molecule atom u).1 hu)
  · intro u _ v _ huv
    exact Equiv.injective perm huv
  · intro v hv
    refine ⟨perm.symm v, ?_, Equiv.apply_symm_apply _ _⟩
    rw [MoleculeGraph.mem_neighborFinset]
    have hvAdj := (MoleculeGraph.mem_neighborFinset molecule (perm atom) v).1 hv
    have hvAdj' : molecule.Adj ((e : Equiv.Perm Atom) atom)
        ((e : Equiv.Perm Atom) (perm.symm v)) := by
      simpa [perm, Equiv.apply_symm_apply] using hvAdj
    exact (MoleculeGraph.Aut.adj_iff molecule e atom (perm.symm v)).1 hvAdj'

theorem detectedCenter_aut_iff (e : molecule.Aut) (atom : Atom) :
    IsDetectedCenter molecule ((e : Equiv.Perm Atom) atom) ↔ IsDetectedCenter molecule atom := by
  simp only [IsDetectedCenter, neighbor_card_aut molecule e atom]

def mapOccurrence (perm : Equiv.Perm Atom) (unit : OccurrenceUnit Atom) : OccurrenceUnit Atom where
  root := perm unit.root
  path := unit.path.map perm

theorem mapOccurrence_atom (perm : Equiv.Perm Atom) (unit : OccurrenceUnit Atom) :
    (mapOccurrence perm unit).atom = perm unit.atom := by
  simp only [mapOccurrence, OccurrenceUnit.atom, getLast?_map]
  cases unit.path.getLast? <;> simp

def mapDetected (e : molecule.Aut) (occ : DetectedOccurrence molecule) :
    DetectedOccurrence molecule :=
  ⟨mapOccurrence (e : Equiv.Perm Atom) occ.1, by
      rw [IsDetectedCenter, mapOccurrence_atom, neighbor_card_aut molecule e occ.1.atom]
      exact occ.2⟩

@[simp] theorem mapDetected_root (e : molecule.Aut) (occ : DetectedOccurrence molecule) :
    (mapDetected molecule e occ).1.root = (e : Equiv.Perm Atom) occ.1.root := rfl

@[simp] theorem mapDetected_path (e : molecule.Aut) (occ : DetectedOccurrence molecule) :
    (mapDetected molecule e occ).1.path = occ.1.path.map (e : Equiv.Perm Atom) := rfl

theorem incomingAtom?_map (perm : Equiv.Perm Atom) (root : Atom) (path : List Atom) :
    incomingAtom? (perm root) (path.map perm) = (incomingAtom? root path).map perm := by
  cases h : path.reverse with
  | nil => simp [incomingAtom?, reverse_map perm path, h]
  | cons x xs =>
      cases xs with
      | nil => simp [incomingAtom?, reverse_map perm path, h]
      | cons y ys => simp [incomingAtom?, reverse_map perm path, h]

theorem rerootStep_map (perm : Equiv.Perm Atom) (root : Atom) (path : List Atom) (next : Atom) :
    rerootStep (perm root) (path.map perm) (perm next) =
      (rerootStep root path next).map perm := by
  simp only [rerootStep]
  by_cases h : incomingAtom? root path = some next
  · rw [if_pos h]
    have himage : incomingAtom? (perm root) (path.map perm) = some (perm next) := by
      simpa [incomingAtom?_map, h]
    rw [if_pos himage]
    exact dropLast_map perm path
  · rw [if_neg h]
    have himage : incomingAtom? (perm root) (path.map perm) ≠ some (perm next) := by
      intro hbad
      apply h
      have hmap := incomingAtom?_map perm root path
      cases hsrc : incomingAtom? root path with
      | none => simp [hsrc, hmap] at hbad
      | some a =>
          simp [hsrc, hmap] at hbad
          exact congrArg some hbad
    rw [if_neg himage]
    simp [List.map_append]

theorem rerootWalk_map (perm : Equiv.Perm Atom) (root : Atom) (start steps : List Atom) :
    rerootWalk (perm root) (start.map perm) (steps.map perm) =
      (rerootWalk root start steps).map perm := by
  induction steps generalizing start with
  | nil => simp [rerootWalk]
  | cons step rest ih =>
      simp only [rerootWalk, List.map_cons, List.foldl_cons]
      rw [rerootStep_map]
      exact ih (rerootStep root start step)

theorem contextOccurrence_map (e : molecule.Aut) (unit : DetectedOccurrence molecule)
    (steps : List Atom) :
    contextOccurrence molecule (mapDetected molecule e unit) (steps.map (e : Equiv.Perm Atom)) =
      (contextOccurrence molecule unit steps).map (mapDetected molecule e) := by
  let perm := (e : Equiv.Perm Atom)
  have hwalk := rerootWalk_map perm unit.1.root unit.1.path steps
  unfold contextOccurrence
  dsimp only [mapDetected_root, mapDetected_path]
  by_cases hcond : unit.1.path.length < (rerootWalk unit.1.root unit.1.path steps).length ∧
      IsDetectedCenter molecule
        (⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩ : OccurrenceUnit Atom).atom
  · have hcond' : (unit.1.path.map perm).length <
        (rerootWalk (perm unit.1.root) (unit.1.path.map perm) (steps.map perm)).length ∧
        IsDetectedCenter molecule
          (⟨perm unit.1.root,
            rerootWalk (perm unit.1.root) (unit.1.path.map perm) (steps.map perm)⟩ :
            OccurrenceUnit Atom).atom := by
      refine ⟨by rw [List.length_map, hwalk, List.length_map]; exact hcond.1, ?_⟩
      have hatom :
          (⟨perm unit.1.root,
            rerootWalk (perm unit.1.root) (unit.1.path.map perm) (steps.map perm)⟩ :
            OccurrenceUnit Atom).atom =
            perm (⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩ :
              OccurrenceUnit Atom).atom := by
        rw [hwalk]
        simpa [mapOccurrence] using mapOccurrence_atom perm
          ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩
      rw [IsDetectedCenter, hatom, neighbor_card_aut molecule e]
      exact hcond.2
    rw [dif_pos hcond, dif_pos hcond']
    apply congrArg some
    apply Subtype.ext
    simp only [mapDetected, mapOccurrence, OccurrenceUnit.mk.injEq]
    exact ⟨trivial, hwalk⟩
  · have hcond' : ¬ ((unit.1.path.map perm).length <
        (rerootWalk (perm unit.1.root) (unit.1.path.map perm) (steps.map perm)).length ∧
        IsDetectedCenter molecule
          (⟨perm unit.1.root,
            rerootWalk (perm unit.1.root) (unit.1.path.map perm) (steps.map perm)⟩ :
            OccurrenceUnit Atom).atom) := by
      intro hp
      apply hcond
      refine ⟨?_, ?_⟩
      · calc
          unit.1.path.length = (unit.1.path.map perm).length := by simp [List.length_map]
          _ < (rerootWalk (perm unit.1.root) (unit.1.path.map perm) (steps.map perm)).length :=
            hp.1
          _ = (rerootWalk unit.1.root unit.1.path steps).length := by
            rw [hwalk]
            simp [List.length_map]
      have hatom :
          (⟨perm unit.1.root,
            rerootWalk (perm unit.1.root) (unit.1.path.map perm) (steps.map perm)⟩ :
            OccurrenceUnit Atom).atom =
            perm (⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩ :
              OccurrenceUnit Atom).atom := by
        rw [hwalk]
        simpa [mapOccurrence] using mapOccurrence_atom perm
          ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩
      rw [IsDetectedCenter] at hp ⊢
      rw [← neighbor_card_aut molecule e, ← hatom]
      exact hp.2
    rw [dif_neg hcond, dif_neg hcond']
    rfl

end OccurrenceMap

section RetainedContext

variable (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}
  (unit : DetectedOccurrence molecule)

local instance relabelRetainedNode (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem retainedContextRuleValue_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right)
    (rule : ConstitutionalRule) (node : left.Node) :
    retainedContextRuleValue molecule right (mapDetected molecule e unit) rule
        (relabel.toEquiv node) =
      retainedContextRuleValue molecule left unit rule node := by
  let perm := (e : Equiv.Perm Atom)
  cases rule with
  | rule1aAtomicNumber =>
      simp only [retainedContextRuleValue]
      rw [← relabel.map_depth node, ← relabel.map_label node]
      exact ruleValue_mapLabel molecule e .rule1aAtomicNumber _ _
  | rule2AtomicMass =>
      simp only [retainedContextRuleValue]
      rw [← relabel.map_depth node, ← relabel.map_label node]
      exact ruleValue_mapLabel molecule e .rule2AtomicMass _ _
  | rule1bDuplicateNodeProximity =>
      simp only [retainedContextRuleValue]
      rw [← relabel.map_label node, retainedOccurrenceSteps_eq_ancestorAtoms,
        retainedOccurrenceSteps_eq_ancestorAtoms,
        ancestorAtoms_relabel parentUnique relabel node]
      cases hlabel : left.label node with
      | mk atom? provenance =>
          cases atom? with
          | none =>
              rw [← relabel.map_depth node]
              simp [ruleValue, nodeRule1bRootDistance, mapNodeLabel]
          | some atom =>
              cases provenance with
              | realAtom =>
                  cases hanc : ancestorAtoms left node with
                  | none =>
                      rw [← relabel.map_depth node]
                      simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                        .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                        ⟨some atom, .realAtom⟩
                  | some steps =>
                      have hlen :
                          (rerootWalk ((e : Equiv.Perm Atom) unit.1.root)
                            (unit.1.path.map (e : Equiv.Perm Atom))
                            (steps.map (e : Equiv.Perm Atom))).length =
                            (rerootWalk unit.1.root unit.1.path steps).length := by
                        rw [rerootWalk_map, List.length_map]
                      simp [mapDetected_root, mapDetected_path, mapNodeLabel, hlen]
              | multipleBondDuplicate distance =>
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .multipleBondDuplicate distance⟩
              | ringDuplicate distance =>
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .ringDuplicate distance⟩
              | phantom distance =>
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .phantom distance⟩
              | lonePair distance =>
                  rw [← relabel.map_depth node]
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .lonePair distance⟩
              | auxiliary distance =>
                  rw [← relabel.map_depth node]
                  simpa [mapNodeLabel] using ruleValue_mapLabel molecule e
                    .rule1bDuplicateNodeProximity (List.replicate (left.depth node) 0)
                    ⟨some atom, .auxiliary distance⟩

theorem retainedContextNodeObservation_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right)
    (rule : ConstitutionalRule) (node : left.Node) :
    retainedContextNodeObservation molecule right (mapDetected molecule e unit) rule
        (relabel.toEquiv node) =
      retainedContextNodeObservation molecule left unit rule node := by
  simp [retainedContextNodeObservation,
    retainedContextRuleValue_relabel molecule unit e parentUnique relabel]

theorem retainedContextRuleKey_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    ∀ node : left.Node,
      retainedContextRuleKey molecule right (mapDetected molecule e unit) W D
          (relabel.toEquiv node) =
        retainedContextRuleKey molecule left unit W D node := by
  intro node
  unfold retainedContextRuleKey
  exact ruleKeyWithObservations_relabel relabel
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right (mapDetected molecule e unit)) W D
    (fun rule current => retainedContextNodeObservation_relabel molecule unit e parentUnique
      relabel rule current) node

end RetainedContext

section Readings

variable (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}

/-- Per reached real read: the image map at the transported context occurrence equals the source
map at that occurrence. Not a global map identity, a selected reference, or a key comparison. -/
def ReadsAgree (e : molecule.Aut)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) : Prop :=
  ∀ node steps occ,
    (graph.label node).provenance = NodeProvenance.realAtom →
    ancestorAtoms graph node = some steps →
    contextOccurrence molecule unit steps = some occ →
    imageMap (mapDetected molecule e occ) = sourceMap occ

variable (unit : DetectedOccurrence molecule)

local instance relabelReadingNode (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem readContext_relabel (e : molecule.Aut)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    {node : left.Node} {steps : List Atom}
    (hreal : (left.label node).provenance = .realAtom)
    (hsteps : ancestorAtoms left node = some steps) :
    readContext molecule imageMap (mapDetected molecule e unit)
        (steps.map (e : Equiv.Perm Atom)) =
      readContext molecule sourceMap unit steps := by
  have hocc := contextOccurrence_map molecule e unit steps
  cases hsource : contextOccurrence molecule unit steps with
  | none => simp [readContext, hocc, hsource]
  | some occ =>
      have hagree := reads node steps occ hreal hsteps hsource
      cases hvalue : sourceMap occ with
      | none => simp [readContext, hocc, hsource, hvalue, hagree]
      | some value => simp [readContext, hocc, hsource, hvalue, hagree]

theorem occurrenceReading_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    occurrenceReading molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      occurrenceReading molecule sourceMap unit left node := by
  have hprov : (right.label (relabel.toEquiv node)).provenance =
      (left.label node).provenance := by
    have h := congrArg NodeLabel.provenance (relabel.map_label node)
    simp only [mapNodeLabel] at h
    exact h.symm
  cases hcase : (left.label node).provenance with
  | realAtom =>
      rw [occurrenceReading, occurrenceReading, hprov, hcase]
      cases hsteps : ancestorAtoms left node with
      | none =>
          simp [ancestorAtoms_relabel parentUnique relabel node, hsteps]
      | some steps =>
          rw [ancestorAtoms_relabel parentUnique relabel node, hsteps]
          simpa using readContext_relabel molecule unit e imageMap sourceMap reads
            (node := node) (steps := steps) hcase hsteps
  | multipleBondDuplicate _ => simp [occurrenceReading, hprov, hcase]
  | ringDuplicate _ => simp [occurrenceReading, hprov, hcase]
  | phantom _ => simp [occurrenceReading, hprov, hcase]
  | lonePair _ => simp [occurrenceReading, hprov, hcase]
  | auxiliary _ => simp [occurrenceReading, hprov, hcase]

theorem hasMultipleBond_mapLabel (e : molecule.Aut) (label : NodeLabel Atom) :
    HasMultipleBond molecule (mapNodeLabel (e : Equiv.Perm Atom) label) ↔
      HasMultipleBond molecule label := by
  let perm := (e : Equiv.Perm Atom)
  constructor
  · rintro ⟨atom, other, hatom, hbond⟩
    cases label with
    | mk atom? _ =>
        cases atom? with
        | none => simp [mapNodeLabel] at hatom
        | some source =>
            simp [mapNodeLabel] at hatom
            subst hatom
            refine ⟨source, perm.symm other, rfl, ?_⟩
            have hb := MoleculeGraph.Aut.bond_eq molecule e source (perm.symm other)
            rw [Equiv.apply_symm_apply] at hb
            exact hb ▸ hbond
  · rintro ⟨atom, other, hatom, hbond⟩
    refine ⟨perm atom, perm other, ?_, ?_⟩
    · simp [mapNodeLabel, hatom, perm]
    · have hb := MoleculeGraph.Aut.bond_eq molecule e atom other
      dsimp [perm] at hb ⊢
      exact hb.symm ▸ hbond

theorem hasMultipleBond_relabel_iff (e : molecule.Aut)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    HasMultipleBond molecule (right.label (relabel.toEquiv node)) ↔
      HasMultipleBond molecule (left.label node) := by
  rw [← relabel.map_label node]
  exact hasMultipleBond_mapLabel molecule e (left.label node)

theorem rule3Observation_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    rule3Observation molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      rule3Observation molecule sourceMap unit left node := by
  rw [rule3Observation, rule3Observation]
  by_cases hb : HasMultipleBond molecule (left.label node)
  · have hb' := (hasMultipleBond_relabel_iff molecule e relabel node).2 hb
    rw [if_pos hb', if_pos hb,
      occurrenceReading_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node]
  · have hb' : ¬ HasMultipleBond molecule (right.label (relabel.toEquiv node)) := by
      intro h
      exact hb ((hasMultipleBond_relabel_iff molecule e relabel node).1 h)
    rw [if_neg hb', if_neg hb]

theorem rule4aObservation_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    rule4aObservation molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      rule4aObservation molecule sourceMap unit left node := by
  simp only [rule4aObservation,
    occurrenceReading_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node]

theorem rule4cObservation_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    rule4cObservation molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      rule4cObservation molecule sourceMap unit left node := by
  simp only [rule4cObservation,
    occurrenceReading_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node]

theorem rule5Observation_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    rule5Observation molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      rule5Observation molecule sourceMap unit left node := by
  simp only [rule5Observation,
    occurrenceReading_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node]

theorem eligibleSense_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    eligibleSense molecule imageMap (mapDetected molecule e unit) right (relabel.toEquiv node) =
      eligibleSense molecule sourceMap unit left node := by
  simp only [eligibleSense,
    occurrenceReading_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node]

private theorem label_provenance_relabel {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right) (node : left.Node) :
    (right.label (relabel.toEquiv node)).provenance = (left.label node).provenance := by
  have h := congrArg NodeLabel.provenance (relabel.map_label node)
  simp only [mapNodeLabel] at h
  exact h.symm

theorem retainedRule4aObservation_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    retainedRule4aObservation molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      retainedRule4aObservation molecule sourceMap unit left node := by
  simp only [retainedRule4aObservation, neutralizeRingDuplicate, label_provenance_relabel relabel]
  cases hprov : (left.label node).provenance with
  | ringDuplicate _ => rfl
  | realAtom =>
      simpa [hprov] using rule4aObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | multipleBondDuplicate _ =>
      simpa [hprov] using rule4aObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | phantom _ =>
      simpa [hprov] using rule4aObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | lonePair _ =>
      simpa [hprov] using rule4aObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | auxiliary _ =>
      simpa [hprov] using rule4aObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node

theorem retainedRule4cObservation_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    retainedRule4cObservation molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      retainedRule4cObservation molecule sourceMap unit left node := by
  simp only [retainedRule4cObservation, neutralizeRingDuplicate, label_provenance_relabel relabel]
  cases hprov : (left.label node).provenance with
  | ringDuplicate _ => rfl
  | realAtom =>
      simpa [hprov] using rule4cObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | multipleBondDuplicate _ =>
      simpa [hprov] using rule4cObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | phantom _ =>
      simpa [hprov] using rule4cObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | lonePair _ =>
      simpa [hprov] using rule4cObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node
  | auxiliary _ =>
      simpa [hprov] using rule4cObservation_relabel molecule unit e parentUnique imageMap
        sourceMap reads relabel node

private theorem stereoObservation_eq_of_fields {a b : StereochemicalObservation}
    (h3 : a.rule3 = b.rule3) (h4a : a.rule4a = b.rule4a) (h4b : a.rule4b = b.rule4b)
    (h4c : a.rule4c = b.rule4c) (h5 : a.rule5 = b.rule5) : a = b := by
  cases a
  cases b
  subst h3 h4a h4b h4c h5
  rfl

theorem retainedRankEvidence_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    retainedRankEvidence molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      retainedRankEvidence molecule sourceMap unit left node := by
  apply stereoObservation_eq_of_fields
  · simpa [retainedRankEvidence] using rule3Observation_relabel molecule unit e parentUnique
      imageMap sourceMap reads relabel node
  · simpa [retainedRankEvidence] using retainedRule4aObservation_relabel molecule unit e
      parentUnique imageMap sourceMap reads relabel node
  · simp [retainedRankEvidence]
  · simp [retainedRankEvidence]
  · simp [retainedRankEvidence]

theorem retainedReadingEvidence_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right)
    (reference : DescriptorSense) (node : left.Node) :
    retainedReadingEvidence molecule imageMap (mapDetected molecule e unit) right reference
        (relabel.toEquiv node) =
      retainedReadingEvidence molecule sourceMap unit left reference node := by
  apply stereoObservation_eq_of_fields
  · simpa [retainedReadingEvidence] using rule3Observation_relabel molecule unit e parentUnique
      imageMap sourceMap reads relabel node
  · simpa [retainedReadingEvidence] using retainedRule4aObservation_relabel molecule unit e
      parentUnique imageMap sourceMap reads relabel node
  · simp [retainedReadingEvidence, eligibleSense_relabel molecule unit e parentUnique imageMap
      sourceMap reads relabel node]
  · simp [retainedReadingEvidence]
  · simp [retainedReadingEvidence]

theorem retainedReadingEvidence4c_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right)
    (reference : DescriptorSense) (node : left.Node) :
    retainedReadingEvidence4c molecule imageMap (mapDetected molecule e unit) right reference
        (relabel.toEquiv node) =
      retainedReadingEvidence4c molecule sourceMap unit left reference node := by
  apply stereoObservation_eq_of_fields
  · simpa [retainedReadingEvidence4c, retainedReadingEvidence] using
      rule3Observation_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node
  · simpa [retainedReadingEvidence4c, retainedReadingEvidence] using
      retainedRule4aObservation_relabel molecule unit e parentUnique imageMap sourceMap reads
        relabel node
  · simp [retainedReadingEvidence4c, retainedReadingEvidence,
      eligibleSense_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node]
  · simpa [retainedReadingEvidence4c] using retainedRule4cObservation_relabel molecule unit e
      parentUnique imageMap sourceMap reads relabel node
  · simp [retainedReadingEvidence4c]

theorem retainedNoReferenceEvidence4c_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    retainedNoReferenceEvidence4c molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      retainedNoReferenceEvidence4c molecule sourceMap unit left node := by
  apply stereoObservation_eq_of_fields
  · simpa [retainedNoReferenceEvidence4c, retainedRankEvidence] using
      rule3Observation_relabel molecule unit e parentUnique imageMap sourceMap reads relabel node
  · simpa [retainedNoReferenceEvidence4c, retainedRankEvidence] using
      retainedRule4aObservation_relabel molecule unit e parentUnique imageMap sourceMap reads
        relabel node
  · simp [retainedNoReferenceEvidence4c, retainedRankEvidence]
  · simpa [retainedNoReferenceEvidence4c] using retainedRule4cObservation_relabel molecule unit e
      parentUnique imageMap sourceMap reads relabel node
  · simp [retainedNoReferenceEvidence4c]

end Readings

section Ordinary

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  {left right : RootedDigraph Atom}

local instance relabelOrdinaryNode (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem ordinaryKeyWithObservations_relabel {perm : Equiv.Perm Atom}
    (relabel : RootedDigraph.Relabel perm left right)
    (leftObserve : ConstitutionalRule → left.Node → ℤ)
    (rightObserve : ConstitutionalRule → right.Node → ℤ)
    (leftEvidence : StereochemicalEvidence left) (rightEvidence : StereochemicalEvidence right)
    (observeEq : ∀ rule node, rightObserve rule (relabel.toEquiv node) = leftObserve rule node)
    (evidenceEq : ∀ node, rightEvidence (relabel.toEquiv node) = leftEvidence node)
    (W D : ℕ) :
    ∀ node : left.Node,
      ordinaryKeyWithObservations right rightObserve rightEvidence W D (relabel.toEquiv node) =
        ordinaryKeyWithObservations left leftObserve leftEvidence W D node := by
  refine node_induction left ?_
  intro node ih
  have hranked : rankedOrdinaryKeysWithObservations right rightObserve rightEvidence W D
      (relabel.toEquiv node) =
      rankedOrdinaryKeysWithObservations left leftObserve leftEvidence W D node := by
    unfold rankedOrdinaryKeysWithObservations
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm
      ((childList_relabel_perm relabel node).map
        (ordinaryKeyWithObservations right rightObserve rightEvidence W D)), List.map_map]
    congr 1
    exact List.map_congr_left fun child hchild => ih child ((left.mem_childList).1 hchild)
  rw [ordinaryKeyWithObservations_eq, ordinaryKeyWithObservations_eq, hranked]
  simp only [ruleComponentWithObservations, stereoComponent, stereoLabel, observeEq, evidenceEq]

end Ordinary

section Complete

variable (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}
  (unit : DetectedOccurrence molecule)

local instance relabelCompleteNode (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem retainedRankKey_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    retainedRankKey molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      retainedRankKey molecule sourceMap unit left node := by
  have hw := width_eq_of_relabel relabel
  have hh := height_eq_of_relabel relabel
  simp only [retainedRankKey, hw, hh]
  exact ordinaryKeyWithObservations_relabel relabel
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
    (retainedRankEvidence molecule sourceMap unit left)
    (retainedRankEvidence molecule imageMap (mapDetected molecule e unit) right)
    (fun rule current => retainedContextNodeObservation_relabel molecule unit e parentUnique
      relabel rule current)
    (fun current => retainedRankEvidence_relabel molecule unit e parentUnique imageMap sourceMap
      reads relabel current) right.width right.height node

theorem retainedRankPath_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    retainedRankPath molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) =
      retainedRankPath molecule sourceMap unit left node := by
  unfold retainedRankPath
  rw [ancestorChain_relabel_eq parentUnique relabel node, List.map_map]
  refine List.map_congr_left ?_
  intro current _
  exact retainedRankKey_relabel molecule unit e parentUnique imageMap sourceMap reads relabel
    current

theorem eligible_relabel_iff (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    Eligible molecule imageMap (mapDetected molecule e unit) right (relabel.toEquiv node) ↔
      Eligible molecule sourceMap unit left node := by
  simp [Eligible, eligibleSense_relabel molecule unit e parentUnique imageMap sourceMap reads
    relabel node]

theorem nearestEligible_relabel_iff (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    NearestEligible molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) ↔
      NearestEligible molecule sourceMap unit left node := by
  constructor
  · intro h
    refine ⟨(eligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
      relabel node).1 h.1, ?_⟩
    intro other hother
    have hother' := (eligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
      relabel other).2 hother
    have hdepth := h.2 _ hother'
    simpa [relabel.map_depth node, relabel.map_depth other] using hdepth
  · intro h
    refine ⟨(eligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
      relabel node).2 h.1, ?_⟩
    intro other hother
    have hsource := (eligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
      relabel (relabel.toEquiv.symm other)).1 (by simpa using hother)
    have hdepth := h.2 _ hsource
    have hotherDepth := relabel.map_depth (relabel.toEquiv.symm other)
    simp only [Equiv.apply_symm_apply] at hotherDepth
    simpa [relabel.map_depth node, hotherDepth] using hdepth

theorem retainedInReferenceClass_relabel_iff (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (node : left.Node) :
    RetainedInReferenceClass molecule imageMap (mapDetected molecule e unit) right
        (relabel.toEquiv node) ↔
      RetainedInReferenceClass molecule sourceMap unit left node := by
  constructor
  · intro h
    refine ⟨(nearestEligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
      relabel node).1 h.1, ?_⟩
    intro other hother
    have himage := h.2 (relabel.toEquiv other)
      ((nearestEligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
        relabel other).2 hother)
    simpa [retainedRankPath_relabel molecule unit e parentUnique imageMap sourceMap reads
      relabel other, retainedRankPath_relabel molecule unit e parentUnique imageMap sourceMap
      reads relabel node] using himage
  · intro h
    refine ⟨(nearestEligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
      relabel node).2 h.1, ?_⟩
    intro other hother
    have hsource := (nearestEligible_relabel_iff molecule unit e parentUnique imageMap sourceMap
      reads relabel (relabel.toEquiv.symm other)).1 (by simpa using hother)
    have hpath := h.2 _ hsource
    have hotherPath := retainedRankPath_relabel molecule unit e parentUnique imageMap sourceMap
      reads relabel (relabel.toEquiv.symm other)
    have hnodePath := retainedRankPath_relabel molecule unit e parentUnique imageMap sourceMap
      reads relabel node
    simp only [Equiv.apply_symm_apply] at hotherPath
    rw [hotherPath, hnodePath]
    exact hpath

private def seniorMembers (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (graph : RootedDigraph Atom) : Finset graph.Node :=
  Finset.univ.filter fun node =>
    RetainedInReferenceClass molecule descriptorMap unit graph node ∧
      eligibleSense molecule descriptorMap unit graph node = some .senior

private def juniorMembers (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (graph : RootedDigraph Atom) : Finset graph.Node :=
  Finset.univ.filter fun node =>
    RetainedInReferenceClass molecule descriptorMap unit graph node ∧
      eligibleSense molecule descriptorMap unit graph node = some .junior

private theorem seniorCount_eq_card (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (graph : RootedDigraph Atom) :
    retainedSeniorCount molecule descriptorMap unit graph =
      (seniorMembers molecule unit descriptorMap graph).card := by
  simp [retainedSeniorCount, retainedReferenceClass, seniorMembers, Finset.filter_filter]

private theorem juniorCount_eq_card (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (graph : RootedDigraph Atom) :
    retainedJuniorCount molecule descriptorMap unit graph =
      (juniorMembers molecule unit descriptorMap graph).card := by
  simp [retainedJuniorCount, retainedReferenceClass, juniorMembers, Finset.filter_filter]

theorem retainedSeniorCount_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) :
    retainedSeniorCount molecule imageMap (mapDetected molecule e unit) right =
      retainedSeniorCount molecule sourceMap unit left := by
  rw [seniorCount_eq_card, seniorCount_eq_card]
  symm
  refine Finset.card_bij
    (fun node (_ : node ∈ seniorMembers molecule unit sourceMap left) => relabel.toEquiv node)
    ?_ ?_ ?_
  · intro node hmem
    simp only [seniorMembers, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    refine ⟨?_, ?_⟩
    · exact (retainedInReferenceClass_relabel_iff molecule unit e parentUnique imageMap
        sourceMap reads relabel node).2 hmem.1
    · rw [eligibleSense_relabel molecule unit e parentUnique imageMap sourceMap reads relabel
        node, hmem.2]
  · intro a _ b _ hab
    exact relabel.toEquiv.injective hab
  · intro node hmem
    refine ⟨relabel.toEquiv.symm node, ?_, by simp⟩
    simp only [seniorMembers, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    refine ⟨?_, ?_⟩
    · exact (retainedInReferenceClass_relabel_iff molecule unit e parentUnique imageMap
        sourceMap reads relabel (relabel.toEquiv.symm node)).1 (by simpa using hmem.1)
    · have hsense := eligibleSense_relabel molecule unit e parentUnique imageMap sourceMap reads
        relabel (relabel.toEquiv.symm node)
      simp only [Equiv.apply_symm_apply] at hsense
      rw [← hsense]
      exact hmem.2

theorem retainedJuniorCount_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) :
    retainedJuniorCount molecule imageMap (mapDetected molecule e unit) right =
      retainedJuniorCount molecule sourceMap unit left := by
  rw [juniorCount_eq_card, juniorCount_eq_card]
  symm
  refine Finset.card_bij
    (fun node (_ : node ∈ juniorMembers molecule unit sourceMap left) => relabel.toEquiv node)
    ?_ ?_ ?_
  · intro node hmem
    simp only [juniorMembers, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    refine ⟨?_, ?_⟩
    · exact (retainedInReferenceClass_relabel_iff molecule unit e parentUnique imageMap
        sourceMap reads relabel node).2 hmem.1
    · rw [eligibleSense_relabel molecule unit e parentUnique imageMap sourceMap reads relabel
        node, hmem.2]
  · intro a _ b _ hab
    exact relabel.toEquiv.injective hab
  · intro node hmem
    refine ⟨relabel.toEquiv.symm node, ?_, by simp⟩
    simp only [juniorMembers, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    refine ⟨?_, ?_⟩
    · exact (retainedInReferenceClass_relabel_iff molecule unit e parentUnique imageMap
        sourceMap reads relabel (relabel.toEquiv.symm node)).1 (by simpa using hmem.1)
    · have hsense := eligibleSense_relabel molecule unit e parentUnique imageMap sourceMap reads
        relabel (relabel.toEquiv.symm node)
      simp only [Equiv.apply_symm_apply] at hsense
      rw [← hsense]
      exact hmem.2

theorem exists_eligible_relabel_iff (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) :
    (∃ node : right.Node, Eligible molecule imageMap (mapDetected molecule e unit) right node) ↔
      (∃ node : left.Node, Eligible molecule sourceMap unit left node) := by
  constructor
  · rintro ⟨node, hnode⟩
    refine ⟨relabel.toEquiv.symm node, ?_⟩
    exact (eligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads relabel
      (relabel.toEquiv.symm node)).1 (by simpa using hnode)
  · rintro ⟨node, hnode⟩
    exact ⟨relabel.toEquiv node, (eligible_relabel_iff molecule unit e parentUnique imageMap
      sourceMap reads relabel node).2 hnode⟩

theorem retainedReferenceSelection_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) :
    retainedReferenceSelection molecule imageMap (mapDetected molecule e unit) right =
      retainedReferenceSelection molecule sourceMap unit left := by
  unfold retainedReferenceSelection
  rw [retainedJuniorCount_relabel molecule unit e parentUnique imageMap sourceMap reads relabel,
    retainedSeniorCount_relabel molecule unit e parentUnique imageMap sourceMap reads relabel]
  by_cases h : ∃ node, Eligible molecule sourceMap unit left node
  · have h' : ∃ node, Eligible molecule imageMap (mapDetected molecule e unit) right node :=
      (exists_eligible_relabel_iff molecule unit e parentUnique imageMap sourceMap reads
        relabel).2 h
    rw [if_neg (not_not_intro h'), if_neg (not_not_intro h)]
  · have h' : ¬ ∃ node, Eligible molecule imageMap (mapDetected molecule e unit) right node := by
      intro hex
      exact h ((exists_eligible_relabel_iff molecule unit e parentUnique imageMap sourceMap
        reads relabel).1 hex)
    rw [if_pos h', if_pos h]

private theorem ordinary_reading_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right)
    (reference : DescriptorSense) (W D : ℕ) (node : left.Node) :
    ordinaryKeyWithObservations right
        (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
        (retainedReadingEvidence molecule imageMap (mapDetected molecule e unit) right reference)
        W D (relabel.toEquiv node) =
      ordinaryKeyWithObservations left
        (retainedContextNodeObservation molecule left unit)
        (retainedReadingEvidence molecule sourceMap unit left reference) W D node :=
  ordinaryKeyWithObservations_relabel relabel
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
    (retainedReadingEvidence molecule sourceMap unit left reference)
    (retainedReadingEvidence molecule imageMap (mapDetected molecule e unit) right reference)
    (fun rule current => retainedContextNodeObservation_relabel molecule unit e parentUnique
      relabel rule current)
    (fun current => retainedReadingEvidence_relabel molecule unit e parentUnique imageMap
      sourceMap reads relabel reference current) W D node

private theorem ordinary_reading4c_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right)
    (reference : DescriptorSense) (W D : ℕ) (node : left.Node) :
    ordinaryKeyWithObservations right
        (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
        (retainedReadingEvidence4c molecule imageMap (mapDetected molecule e unit) right
          reference) W D (relabel.toEquiv node) =
      ordinaryKeyWithObservations left
        (retainedContextNodeObservation molecule left unit)
        (retainedReadingEvidence4c molecule sourceMap unit left reference) W D node :=
  ordinaryKeyWithObservations_relabel relabel
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
    (retainedReadingEvidence4c molecule sourceMap unit left reference)
    (retainedReadingEvidence4c molecule imageMap (mapDetected molecule e unit) right reference)
    (fun rule current => retainedContextNodeObservation_relabel molecule unit e parentUnique
      relabel rule current)
    (fun current => retainedReadingEvidence4c_relabel molecule unit e parentUnique imageMap
      sourceMap reads relabel reference current) W D node

private theorem ordinary_noReference_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ)
    (node : left.Node) :
    ordinaryKeyWithObservations right
        (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
        (retainedNoReferenceEvidence4c molecule imageMap (mapDetected molecule e unit) right)
        W D (relabel.toEquiv node) =
      ordinaryKeyWithObservations left
        (retainedContextNodeObservation molecule left unit)
        (retainedNoReferenceEvidence4c molecule sourceMap unit left) W D node :=
  ordinaryKeyWithObservations_relabel relabel
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
    (retainedNoReferenceEvidence4c molecule sourceMap unit left)
    (retainedNoReferenceEvidence4c molecule imageMap (mapDetected molecule e unit) right)
    (fun rule current => retainedContextNodeObservation_relabel molecule unit e parentUnique
      relabel rule current)
    (fun current => retainedNoReferenceEvidence4c_relabel molecule unit e parentUnique imageMap
      sourceMap reads relabel current) W D node

theorem retainedCompleteReadingAt_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ)
    (reference : Option DescriptorSense) :
    retainedCompleteReadingAt molecule imageMap (mapDetected molecule e unit) right W D
        reference =
      retainedCompleteReadingAt molecule sourceMap unit left W D reference := by
  cases reference with
  | none =>
      have h := ordinary_noReference_relabel molecule unit e parentUnique imageMap sourceMap reads
        relabel W D left.root
      simp only [retainedCompleteReadingAt, observedRule4cComponent, ← relabel.map_root, h]
  | some sense =>
      have h4b := ordinary_reading_relabel molecule unit e parentUnique imageMap sourceMap reads
        relabel sense W D left.root
      have h4c := ordinary_reading4c_relabel molecule unit e parentUnique imageMap sourceMap reads
        relabel sense W D left.root
      simp only [retainedCompleteReadingAt, observedRule4bComponent, observedRule4cComponent,
        ← relabel.map_root, h4b, h4c]

theorem retainedCompleteReadingsAt_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    retainedCompleteReadingsAt molecule imageMap (mapDetected molecule e unit) right W D =
      retainedCompleteReadingsAt molecule sourceMap unit left W D := by
  unfold retainedCompleteReadingsAt
  rw [retainedReferenceSelection_relabel molecule unit e parentUnique imageMap sourceMap reads
    relabel]
  cases retainedReferenceSelection molecule sourceMap unit left with
  | empty =>
      simp [retainedCompleteReadingAt_relabel molecule unit e parentUnique imageMap sourceMap
        reads relabel]
  | one sense =>
      simp [retainedCompleteReadingAt_relabel molecule unit e parentUnique imageMap sourceMap
        reads relabel]
  | both =>
      simp [retainedCompleteReadingAt_relabel molecule unit e parentUnique imageMap sourceMap
        reads relabel]

theorem retainedCompletePriorSignatureAt_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    retainedCompletePriorSignatureAt molecule imageMap (mapDetected molecule e unit) right W D =
      retainedCompletePriorSignatureAt molecule sourceMap unit left W D := by
  simp [retainedCompletePriorSignatureAt,
    retainedReferenceSelection_relabel molecule unit e parentUnique imageMap sourceMap reads
      relabel,
    retainedCompleteReadingsAt_relabel molecule unit e parentUnique imageMap sourceMap reads
      relabel]

theorem retainedMolecularRankPairAt_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    retainedMolecularRankPairAt molecule imageMap (mapDetected molecule e unit) right W D =
      retainedMolecularRankPairAt molecule sourceMap unit left W D := by
  unfold retainedMolecularRankPairAt observedPairKey observedRule4aComponent
  have hkey := ordinaryKeyWithObservations_relabel relabel
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right (mapDetected molecule e unit))
    (retainedRankEvidence molecule sourceMap unit left)
    (retainedRankEvidence molecule imageMap (mapDetected molecule e unit) right)
    (fun rule current => retainedContextNodeObservation_relabel molecule unit e parentUnique
      relabel rule current)
    (fun current => retainedRankEvidence_relabel molecule unit e parentUnique imageMap sourceMap
      reads relabel current) W D left.root
  have hrule := ruleKeyWithObservations_relabel relabel
    (retainedContextNodeObservation molecule left unit)
    (retainedContextNodeObservation molecule right (mapDetected molecule e unit)) W D
    (fun rule current => retainedContextNodeObservation_relabel molecule unit e parentUnique
      relabel rule current) left.root
  simp [← relabel.map_root, hkey, hrule]

theorem retainedCompleteLigandPriorKeyAt_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    retainedCompleteLigandPriorKeyAt molecule imageMap (mapDetected molecule e unit) right W D =
      retainedCompleteLigandPriorKeyAt molecule sourceMap unit left W D := by
  simp [retainedCompleteLigandPriorKeyAt,
    retainedMolecularRankPairAt_relabel molecule unit e parentUnique imageMap sourceMap reads
      relabel,
    retainedCompletePriorSignatureAt_relabel molecule unit e parentUnique imageMap sourceMap
      reads relabel]

theorem retainedCompleteRule5ReadingsAt_relabel (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ)
    (common : DescriptorSense) :
    retainedCompleteRule5ReadingsAt molecule imageMap (mapDetected molecule e unit) right W D
        common =
      retainedCompleteRule5ReadingsAt molecule sourceMap unit left W D common := by
  unfold retainedCompleteRule5ReadingsAt retainedTaggedAlternativeReferencesAt
    retainedCompleteRule5ReadingAt
  rw [retainedReferenceSelection_relabel molecule unit e parentUnique imageMap sourceMap reads
    relabel]
  cases retainedReferenceSelection molecule sourceMap unit left with
  | empty =>
      simp [retainedCompleteReadingAt_relabel molecule unit e parentUnique imageMap sourceMap
        reads relabel]
  | one sense =>
      simp [retainedCompleteReadingAt_relabel molecule unit e parentUnique imageMap sourceMap
        reads relabel]
  | both =>
      simp [retainedCompleteReadingAt_relabel molecule unit e parentUnique imageMap sourceMap
        reads relabel]

theorem retainedMolecularRankPairAt_mirror (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap.reflect unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    retainedMolecularRankPairAt molecule imageMap (mapDetected molecule e unit) right W D =
      retainedMolecularRankPairAt molecule sourceMap unit left W D := by
  calc
    _ = retainedMolecularRankPairAt molecule sourceMap.reflect unit left W D :=
      retainedMolecularRankPairAt_relabel molecule unit e parentUnique imageMap
        sourceMap.reflect reads relabel W D
    _ = retainedMolecularRankPairAt molecule sourceMap unit left W D :=
      retainedMolecularRankPairAt_reflect molecule sourceMap unit left W D

theorem retainedCompleteLigandPriorKeyAt_mirror (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap.reflect unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ) :
    retainedCompleteLigandPriorKeyAt molecule imageMap (mapDetected molecule e unit) right W D =
      retainedCompleteLigandPriorKeyAt molecule sourceMap unit left W D := by
  calc
    _ = retainedCompleteLigandPriorKeyAt molecule sourceMap.reflect unit left W D :=
      retainedCompleteLigandPriorKeyAt_relabel molecule unit e parentUnique imageMap
        sourceMap.reflect reads relabel W D
    _ = retainedCompleteLigandPriorKeyAt molecule sourceMap unit left W D :=
      retainedCompleteLigandPriorKeyAt_reflect molecule sourceMap unit left W D

theorem retainedCompleteRule5ReadingsAt_mirror (e : molecule.Aut)
    (parentUnique : ∀ a b n, left.child a n → left.child b n → a = b)
    (imageMap sourceMap : DescriptorMap (DetectedOccurrence molecule))
    (reads : ReadsAgree molecule e imageMap sourceMap.reflect unit left)
    (relabel : RootedDigraph.Relabel (e : Equiv.Perm Atom) left right) (W D : ℕ)
    (common : DescriptorSense) :
    retainedCompleteRule5ReadingsAt molecule imageMap (mapDetected molecule e unit) right W D
        common =
      retainedCompleteRule5ReadingsAt molecule sourceMap.reflect unit left W D common :=
  retainedCompleteRule5ReadingsAt_relabel molecule unit e parentUnique imageMap sourceMap.reflect
    reads relabel W D common

end Complete

end

end DeclarativeCIP
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.dist_aut
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.idxOf_map
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.nodeObservation_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKeyWithObservations_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleKey_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualNodeObservation_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.contextualRuleKey_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.occurrenceReading_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReferenceSelection_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandPriorKeyAt_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteRule5ReadingsAt_relabel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedMolecularRankPairAt_mirror
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteLigandPriorKeyAt_mirror
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedCompleteRule5ReadingsAt_mirror
