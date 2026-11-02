import TetraStereo.OneCenter.AuthoritativeCIPGraph
import TetraStereo.OneCenter.DeclarativeCIPRule1aExact
import TetraStereo.OneCenter.ExactOfficialRuleMajorKey
import TetraStereo.OneCenter.ProductionCIPRule1aMatchingRealization
import TetraStereo.OneCenter.ProductionCIPReachability
import TetraStereo.OneCenter.ProductionCIPReachabilityBound

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open RawMolecule

/-!
# Executable finite realization of semantic localized mancude graphs

This module gives the all-element semantic molecule representation a canonical finite candidate
edge list, bridge removal, component traversal, and matching edge lists, and proves each list
equivalent to the independent relation in `DeclarativeCIPRule1aExact`.
-/

namespace SemanticMolecule

/-- Executable count of represented written double bonds incident to one semantic atom. -/
def semanticIncidentDoubleBondCount (molecule : SemanticMolecule)
    (atom : Fin molecule.atomCount) : Nat :=
  ((List.finRange molecule.atomCount).filter fun other =>
    molecule.localizedBondOrder atom.val other.val == 2).length

theorem semanticIncidentDoubleBondCount_eq_independent
    (molecule : SemanticMolecule) (atom : Fin molecule.atomCount) :
    molecule.semanticIncidentDoubleBondCount atom =
      molecule.toLocalizedMoleculeGraph.incidentDoubleBondCount atom := by
  unfold semanticIncidentDoubleBondCount MoleculeGraph.incidentDoubleBondCount
  rw [Fin.univ_def]
  rfl

/-- Executable recognition of a vertex admitted to the localized mancude graph. -/
def semanticLocalizedMancudeVertex? (molecule : SemanticMolecule)
    (atom : Fin molecule.atomCount) : Bool :=
  decide (molecule.semanticIncidentDoubleBondCount atom = 1) ||
    (decide (molecule.semanticIncidentDoubleBondCount atom = 0) &&
      decide ((molecule.atoms.get atom).formalCharge < 0))

@[simp] theorem semanticLocalizedMancudeVertex?_eq_true_iff
    (molecule : SemanticMolecule) (atom : Fin molecule.atomCount) :
    molecule.semanticLocalizedMancudeVertex? atom = true ↔
      molecule.toLocalizedMoleculeGraph.LocalizedMancudeVertex atom := by
  simp [semanticLocalizedMancudeVertex?, MoleculeGraph.LocalizedMancudeVertex,
    molecule.semanticIncidentDoubleBondCount_eq_independent atom]

/-- Executable recognition of one pre-bridge-removal mancude candidate edge. -/
def semanticMancudeCandidateEdge? (molecule : SemanticMolecule)
    (left right : Fin molecule.atomCount) : Bool :=
  (decide (molecule.localizedBondOrder left.val right.val = 1) ||
      decide (molecule.localizedBondOrder left.val right.val = 2)) &&
    molecule.semanticLocalizedMancudeVertex? left &&
    molecule.semanticLocalizedMancudeVertex? right

@[simp] theorem semanticMancudeCandidateEdge?_eq_true_iff
    (molecule : SemanticMolecule) (left right : Fin molecule.atomCount) :
    molecule.semanticMancudeCandidateEdge? left right = true ↔
      molecule.toLocalizedMoleculeGraph.MancudeCandidateEdge left right := by
  simp [semanticMancudeCandidateEdge?, MoleculeGraph.MancudeCandidateEdge,
    SemanticMolecule.toLocalizedMoleculeGraph_bond, and_assoc]

/-- Canonical finite enumeration of the independent semantic mancude candidate-edge relation.
Only the increasing orientation is stored, so the list has exactly one occurrence per undirected
edge without relying on an input interaction order. -/
def semanticLocalizedMancudeCandidateEdges (molecule : SemanticMolecule) :
    List (Nat × Nat) :=
  (List.finRange molecule.atomCount).flatMap fun left =>
    (List.finRange molecule.atomCount).filterMap fun right =>
      if decide (left.val < right.val) &&
          molecule.semanticMancudeCandidateEdge? left right then
        some (left.val, right.val)
      else
        none

theorem pair_mem_semanticLocalizedMancudeCandidateEdges_iff
    (molecule : SemanticMolecule) (left right : Fin molecule.atomCount) :
    (left.val, right.val) ∈ molecule.semanticLocalizedMancudeCandidateEdges ↔
      left.val < right.val ∧
        molecule.toLocalizedMoleculeGraph.MancudeCandidateEdge left right := by
  simp [semanticLocalizedMancudeCandidateEdges, and_assoc]
  constructor
  · rintro ⟨sourceLeft, sourceRight, order, candidate, leftValue, rightValue⟩
    have leftIdentity : sourceLeft = left := Fin.ext leftValue
    have rightIdentity : sourceRight = right := Fin.ext rightValue
    simpa [leftIdentity, rightIdentity] using And.intro order candidate
  · rintro ⟨order, candidate⟩
    exact ⟨left, right, order, candidate, rfl, rfl⟩

theorem containsUndirectedEdge_eq_true_iff_pair_mem
    (edges : List (Nat × Nat)) (left right : Nat) :
    containsUndirectedEdge edges left right = true ↔
      (left, right) ∈ edges ∨ (right, left) ∈ edges := by
  simp only [containsUndirectedEdge, List.any_eq_true, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨edge, edgePresent, forward | reverse⟩
    · left
      have edgeIdentity : edge = (left, right) := Prod.ext forward.1 forward.2
      simpa [edgeIdentity] using edgePresent
    · right
      have edgeIdentity : edge = (right, left) := Prod.ext reverse.1 reverse.2
      simpa [edgeIdentity] using edgePresent
  · rintro (forward | reverse)
    · exact ⟨(left, right), forward, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(right, left), reverse, Or.inr ⟨rfl, rfl⟩⟩

/-- Exact orientation-free realization of the canonically enumerated semantic candidate edges. -/
theorem containsUndirectedEdge_semanticLocalizedMancudeCandidateEdges_iff
    (molecule : SemanticMolecule) (left right : Fin molecule.atomCount) :
    containsUndirectedEdge molecule.semanticLocalizedMancudeCandidateEdges
        left.val right.val = true ↔
      molecule.toLocalizedMoleculeGraph.MancudeCandidateEdge left right := by
  rw [containsUndirectedEdge_eq_true_iff_pair_mem]
  constructor
  · rintro (forward | reverse)
    · exact (molecule.pair_mem_semanticLocalizedMancudeCandidateEdges_iff left right).mp
        forward |>.2
    · exact (molecule.toLocalizedMoleculeGraph.mancudeCandidateEdge_symm).mpr
        ((molecule.pair_mem_semanticLocalizedMancudeCandidateEdges_iff right left).mp
          reverse |>.2)
  · intro candidate
    have distinct : left ≠ right := by
      intro identity
      subst right
      have self := molecule.toLocalizedMoleculeGraph.bond_self left
      rcases candidate.1 with order | order
      · have impossible : (1 : Nat) = 0 := order.symm.trans self
        simp at impossible
      · have impossible : (2 : Nat) = 0 := order.symm.trans self
        simp at impossible
    rcases lt_or_gt_of_ne (fun valueIdentity => distinct (Fin.ext valueIdentity)) with
      forwardOrder | reverseOrder
    · exact Or.inl
        ((molecule.pair_mem_semanticLocalizedMancudeCandidateEdges_iff left right).mpr
          ⟨forwardOrder, candidate⟩)
    · exact Or.inr
        ((molecule.pair_mem_semanticLocalizedMancudeCandidateEdges_iff right left).mpr
          ⟨reverseOrder,
            (molecule.toLocalizedMoleculeGraph.mancudeCandidateEdge_symm).mp candidate⟩)

private theorem unblockedListEdge_of_semanticMancudeStepWithout
    (molecule : SemanticMolecule)
    {blockedLeft blockedRight left right : Fin molecule.atomCount}
    (step : molecule.toLocalizedMoleculeGraph.MancudeStepWithout
      blockedLeft blockedRight left right) :
    UnblockedListEdge (blockedLeft.val, blockedRight.val)
      molecule.semanticLocalizedMancudeCandidateEdges left.val right.val := by
  have candidatePresent :
      containsUndirectedEdge molecule.semanticLocalizedMancudeCandidateEdges
        left.val right.val = true :=
    (molecule.containsUndirectedEdge_semanticLocalizedMancudeCandidateEdges_iff
      left right).mpr step.1
  rw [containsUndirectedEdge_eq_true_iff_pair_mem] at candidatePresent
  have unblockedValues : ¬
      ((left.val = blockedLeft.val ∧ right.val = blockedRight.val) ∨
       (left.val = blockedRight.val ∧ right.val = blockedLeft.val)) := by
    intro blocked
    apply step.2
    rcases blocked with blocked | blocked
    · exact Or.inl ⟨Fin.ext blocked.1, Fin.ext blocked.2⟩
    · exact Or.inr ⟨Fin.ext blocked.1, Fin.ext blocked.2⟩
  rw [unblockedListEdge_iff]
  rcases candidatePresent with forward | reverse
  · exact ⟨(left.val, right.val), forward, unblockedValues,
      Or.inl ⟨rfl, rfl⟩⟩
  · refine ⟨(right.val, left.val), reverse, ?_, Or.inr ⟨rfl, rfl⟩⟩
    intro blocked
    apply unblockedValues
    rcases blocked with blocked | blocked
    · exact Or.inr ⟨blocked.2, blocked.1⟩
    · exact Or.inl ⟨blocked.2, blocked.1⟩

private theorem endpoints_lt_of_mem_semanticLocalizedMancudeCandidateEdges
    (molecule : SemanticMolecule) {edge : Nat × Nat}
    (present : edge ∈ molecule.semanticLocalizedMancudeCandidateEdges) :
    edge.1 < molecule.atomCount ∧ edge.2 < molecule.atomCount := by
  classical
  unfold semanticLocalizedMancudeCandidateEdges at present
  rw [List.mem_flatMap] at present
  obtain ⟨left, _leftPresent, rightPresent⟩ := present
  rw [List.mem_filterMap] at rightPresent
  obtain ⟨right, _rightPresent, output⟩ := rightPresent
  split at output
  · have identity : (left.val, right.val) = edge := Option.some.inj output
    simp [← identity]
  · simp at output

/-- Exact localized conjugated ring graph.  Removing every bridge prevents an acyclic or
inter-component single bond from being treated as a resonance edge. -/
def semanticLocalizedMancudeEdges (molecule : SemanticMolecule) : List (Nat × Nat) :=
  let candidates := molecule.semanticLocalizedMancudeCandidateEdges
  candidates.filter fun edge =>
    (reachableWithoutEdge edge (candidates.length + 1) candidates [edge.1] [edge.1]).contains
      edge.2

/-- Canonical list membership realizes exactly the independent non-bridge relation, in the
single stored increasing orientation. -/
theorem pair_mem_semanticLocalizedMancudeEdges_iff
    (molecule : SemanticMolecule) (left right : Fin molecule.atomCount) :
    (left.val, right.val) ∈ molecule.semanticLocalizedMancudeEdges ↔
      left.val < right.val ∧
        molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right := by
  constructor
  · intro present
    unfold semanticLocalizedMancudeEdges at present
    simp only [List.mem_filter] at present
    have candidateFacts :=
      (molecule.pair_mem_semanticLocalizedMancudeCandidateEdges_iff left right).mp present.1
    refine ⟨candidateFacts.1, candidateFacts.2, ?_⟩
    have reached : right.val ∈
        reachableWithoutEdge (left.val, right.val)
          (molecule.semanticLocalizedMancudeCandidateEdges.length + 1)
          molecule.semanticLocalizedMancudeCandidateEdges [left.val] [left.val] := by
      simpa using present.2
    have rawPath := reachableWithoutEdge_from_singleton_sound
      (left.val, right.val)
      (molecule.semanticLocalizedMancudeCandidateEdges.length + 1)
      molecule.semanticLocalizedMancudeCandidateEdges reached
    have convertPath : ∀ atom,
        Relation.ReflTransGen
            (UnblockedListEdge (left.val, right.val)
              molecule.semanticLocalizedMancudeCandidateEdges)
            left.val atom →
          ∃ bound : atom < molecule.atomCount,
            Relation.ReflTransGen
              (molecule.toLocalizedMoleculeGraph.MancudeStepWithout left right)
              left ⟨atom, bound⟩ := by
      intro atom path
      induction path with
      | refl => exact ⟨left.isLt, Relation.ReflTransGen.refl⟩
      | @tail parent atom hprefix step inductionHypothesis =>
          obtain ⟨parentBound, independentPrefix⟩ := inductionHypothesis
          rw [unblockedListEdge_iff] at step
          obtain ⟨edge, edgePresent, edgeUnblocked, orientation⟩ := step
          have orientedMembership :
              (parent, atom) ∈ molecule.semanticLocalizedMancudeCandidateEdges ∨
                (atom, parent) ∈ molecule.semanticLocalizedMancudeCandidateEdges := by
            rcases orientation with ⟨edgeLeft, edgeRight⟩ | ⟨edgeRight, edgeLeft⟩
            · left
              have edgeIdentity : edge = (parent, atom) := Prod.ext edgeLeft edgeRight
              simpa [edgeIdentity] using edgePresent
            · right
              have edgeIdentity : edge = (atom, parent) := Prod.ext edgeLeft edgeRight
              simpa [edgeIdentity] using edgePresent
          have atomBound : atom < molecule.atomCount := by
            rcases orientedMembership with forward | reverse
            · exact (molecule.endpoints_lt_of_mem_semanticLocalizedMancudeCandidateEdges
                forward).2
            · exact (molecule.endpoints_lt_of_mem_semanticLocalizedMancudeCandidateEdges
                reverse).1
          let parentFin : Fin molecule.atomCount := ⟨parent, parentBound⟩
          let atomFin : Fin molecule.atomCount := ⟨atom, atomBound⟩
          have candidateStep :
              molecule.toLocalizedMoleculeGraph.MancudeCandidateEdge parentFin atomFin := by
            apply (molecule.containsUndirectedEdge_semanticLocalizedMancudeCandidateEdges_iff
              parentFin atomFin).mp
            rw [containsUndirectedEdge_eq_true_iff_pair_mem]
            exact orientedMembership
          have unblocked : ¬
              ((parentFin = left ∧ atomFin = right) ∨
               (parentFin = right ∧ atomFin = left)) := by
            intro blocked
            apply edgeUnblocked
            have blockedValues :
                ((parent = left.val ∧ atom = right.val) ∨
                 (parent = right.val ∧ atom = left.val)) := by
              rcases blocked with blocked | blocked
              · exact Or.inl ⟨congrArg Fin.val blocked.1, congrArg Fin.val blocked.2⟩
              · exact Or.inr ⟨congrArg Fin.val blocked.1, congrArg Fin.val blocked.2⟩
            rcases orientation with ⟨edgeLeft, edgeRight⟩ | ⟨edgeRight, edgeLeft⟩
            · have edgeIdentity : edge = (parent, atom) := Prod.ext edgeLeft edgeRight
              simpa [edgeIdentity] using blockedValues
            · have edgeIdentity : edge = (atom, parent) := Prod.ext edgeLeft edgeRight
              rcases blockedValues with blockedValues | blockedValues
              · simpa [edgeIdentity] using Or.inr ⟨blockedValues.2, blockedValues.1⟩
              · simpa [edgeIdentity] using Or.inl ⟨blockedValues.2, blockedValues.1⟩
          exact ⟨atomBound, independentPrefix.tail ⟨candidateStep, unblocked⟩⟩
    obtain ⟨rightBound, independentPath⟩ := convertPath right.val rawPath
    have rightIdentity : (⟨right.val, rightBound⟩ : Fin molecule.atomCount) = right :=
      Fin.ext rfl
    simpa [rightIdentity] using independentPath
  · rintro ⟨order, localized⟩
    unfold semanticLocalizedMancudeEdges
    simp only [List.mem_filter]
    have candidatePresent :
        (left.val, right.val) ∈ molecule.semanticLocalizedMancudeCandidateEdges :=
      (molecule.pair_mem_semanticLocalizedMancudeCandidateEdges_iff left right).mpr
        ⟨order, localized.1⟩
    refine ⟨candidatePresent, ?_⟩
    have rawPath : Relation.ReflTransGen
        (UnblockedListEdge (left.val, right.val)
          molecule.semanticLocalizedMancudeCandidateEdges)
        left.val right.val :=
      localized.2.lift Fin.val fun _ _ step =>
        molecule.unblockedListEdge_of_semanticMancudeStepWithout step
    have reached := reachableWithoutEdge_complete_of_reflTransGen
      (left.val, right.val) molecule.semanticLocalizedMancudeCandidateEdges rawPath
    simpa using reached

private theorem mancudeStepWithout_swapBlocked {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom] (molecule : MoleculeGraph Atom)
    {blockedLeft blockedRight left right : Atom}
    (step : molecule.MancudeStepWithout blockedLeft blockedRight left right) :
    molecule.MancudeStepWithout blockedRight blockedLeft left right := by
  exact ⟨step.1, fun blocked => step.2 (blocked.elim Or.inr Or.inl)⟩

private theorem mancudeStepWithout_symm {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom] (molecule : MoleculeGraph Atom)
    {blockedLeft blockedRight left right : Atom}
    (step : molecule.MancudeStepWithout blockedLeft blockedRight left right) :
    molecule.MancudeStepWithout blockedLeft blockedRight right left := by
  refine ⟨(molecule.mancudeCandidateEdge_symm).mpr step.1, ?_⟩
  intro blocked
  apply step.2
  rcases blocked with blocked | blocked
  · exact Or.inr ⟨blocked.2, blocked.1⟩
  · exact Or.inl ⟨blocked.2, blocked.1⟩

private theorem reflTransGen_reverse {α : Type*} {relation : α → α → Prop}
    (symmetric : Symmetric relation) {left right : α}
    (path : Relation.ReflTransGen relation left right) :
    Relation.ReflTransGen relation right left := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix step inductionHypothesis =>
      exact (Relation.ReflTransGen.single (symmetric step)).trans inductionHypothesis

theorem localizedMancudeEdge_reverse {Atom : Type*} [Fintype Atom]
    [DecidableEq Atom] (molecule : MoleculeGraph Atom)
    {left right : Atom} (edge : molecule.LocalizedMancudeEdge left right) :
    molecule.LocalizedMancudeEdge right left := by
  refine ⟨(molecule.mancudeCandidateEdge_symm).mpr edge.1, ?_⟩
  have swapped : Relation.ReflTransGen
      (molecule.MancudeStepWithout right left) left right :=
    edge.2.mono fun _ _ step => mancudeStepWithout_swapBlocked molecule step
  exact reflTransGen_reverse
    (fun _ _ step => mancudeStepWithout_symm molecule step) swapped

/-- Exact orientation-free realization of the bridge-free semantic mancude list against the
independent molecule-graph relation. -/
theorem containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
    (molecule : SemanticMolecule) (left right : Fin molecule.atomCount) :
    containsUndirectedEdge molecule.semanticLocalizedMancudeEdges left.val right.val = true ↔
      molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right := by
  rw [containsUndirectedEdge_eq_true_iff_pair_mem]
  constructor
  · rintro (forward | reverse)
    · exact (molecule.pair_mem_semanticLocalizedMancudeEdges_iff left right).mp forward |>.2
    · exact localizedMancudeEdge_reverse molecule.toLocalizedMoleculeGraph
        ((molecule.pair_mem_semanticLocalizedMancudeEdges_iff right left).mp reverse |>.2)
  · intro localized
    have distinct : left ≠ right := by
      intro identity
      subst right
      have self := molecule.toLocalizedMoleculeGraph.bond_self left
      rcases localized.1.1 with order | order
      · have impossible : (1 : Nat) = 0 := order.symm.trans self
        simp at impossible
      · have impossible : (2 : Nat) = 0 := order.symm.trans self
        simp at impossible
    rcases lt_or_gt_of_ne (fun valueIdentity => distinct (Fin.ext valueIdentity)) with
      forwardOrder | reverseOrder
    · exact Or.inl
        ((molecule.pair_mem_semanticLocalizedMancudeEdges_iff left right).mpr
          ⟨forwardOrder, localized⟩)
    · exact Or.inr
        ((molecule.pair_mem_semanticLocalizedMancudeEdges_iff right left).mpr
          ⟨reverseOrder,
            localizedMancudeEdge_reverse molecule.toLocalizedMoleculeGraph localized⟩)

theorem endpoints_lt_of_mem_semanticLocalizedMancudeEdges
    (molecule : SemanticMolecule) {edge : Nat × Nat}
    (present : edge ∈ molecule.semanticLocalizedMancudeEdges) :
    edge.1 < molecule.atomCount ∧ edge.2 < molecule.atomCount := by
  unfold semanticLocalizedMancudeEdges at present
  exact molecule.endpoints_lt_of_mem_semanticLocalizedMancudeCandidateEdges
    (List.mem_filter.mp present).1

/-- Every accepted semantic mancude edge has a return walk between its endpoints after that edge
is removed.  This is the mathematical non-bridge property used to reject aromatic chains. -/
theorem semanticLocalizedMancudeEdge_reconnects_without_edge
    (molecule : SemanticMolecule) (edge : Nat × Nat)
    (present : edge ∈ molecule.semanticLocalizedMancudeEdges) :
    Relation.ReflTransGen
      (UnblockedListEdge edge molecule.semanticLocalizedMancudeCandidateEdges)
      edge.1 edge.2 := by
  unfold semanticLocalizedMancudeEdges at present
  simp only [List.mem_filter] at present
  have reached : edge.2 ∈
      reachableWithoutEdge edge
        (molecule.semanticLocalizedMancudeCandidateEdges.length + 1)
        molecule.semanticLocalizedMancudeCandidateEdges [edge.1] [edge.1] := by
    simpa using present.2
  exact reachableWithoutEdge_from_singleton_sound edge
    (molecule.semanticLocalizedMancudeCandidateEdges.length + 1)
    molecule.semanticLocalizedMancudeCandidateEdges reached

def semanticLocalizedMancudeComponentVertices (molecule : SemanticMolecule) (attached : Nat) :
    List Nat :=
  edgeComponent molecule.semanticLocalizedMancudeEdges
    (molecule.semanticLocalizedMancudeEdges.length + 1) [attached] [attached]

private theorem edgeComponent_eq_reachableWithoutEdge_sentinel
    (edges : List (Nat × Nat)) (bound : Nat)
    (bounded : ∀ edge ∈ edges, edge.1 < bound ∧ edge.2 < bound) :
    ∀ fuel frontier seen,
      edgeComponent edges fuel frontier seen =
        reachableWithoutEdge (bound, bound) fuel edges frontier seen := by
  intro fuel
  induction fuel with
  | zero => intro frontier seen; rfl
  | succ fuel inductionHypothesis =>
      intro frontier seen
      cases frontier with
      | nil => rfl
      | cons first rest =>
          have filterMapIdentity : ∀ atom,
              edges.filterMap (fun edge =>
                let blocked :=
                  (edge.1 == bound && edge.2 == bound) ||
                    (edge.1 == bound && edge.2 == bound)
                if blocked then none
                else if edge.1 == atom then some edge.2
                else if edge.2 == atom then some edge.1
                else none) =
                edges.filterMap (fun edge =>
                  if edge.1 == atom then some edge.2
                  else if edge.2 == atom then some edge.1
                  else none) := by
            intro atom
            apply List.filterMap_congr
            intro edge edgePresent
            have notBound : edge.1 ≠ bound := Nat.ne_of_lt (bounded edge edgePresent).1
            simp [notBound]
          have nextIdentity :
              (List.flatMap
                (fun atom => edges.filterMap fun edge =>
                  let blocked :=
                    (edge.1 == bound && edge.2 == bound) ||
                      (edge.1 == bound && edge.2 == bound)
                  if blocked then none
                  else if edge.1 == atom then some edge.2
                  else if edge.2 == atom then some edge.1
                  else none) (first :: rest)).filter
                    (fun atom => !seen.contains atom) =
              (List.flatMap
                (fun atom => edges.filterMap fun edge =>
                  if edge.1 == atom then some edge.2
                  else if edge.2 == atom then some edge.1
                  else none) (first :: rest)).filter
                    (fun atom => !seen.contains atom) := by
            congr 1
            apply List.flatMap_congr
            intro atom _
            exact filterMapIdentity atom
          simp only [edgeComponent, reachableWithoutEdge]
          rw [nextIdentity]
          exact inductionHypothesis _ _

private theorem unblockedSentinelEdge_of_semanticLocalizedMancudeEdge
    (molecule : SemanticMolecule) {left right : Fin molecule.atomCount}
    (edge : molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right) :
    UnblockedListEdge (molecule.atomCount, molecule.atomCount)
      molecule.semanticLocalizedMancudeEdges left.val right.val := by
  have contained : containsUndirectedEdge molecule.semanticLocalizedMancudeEdges
      left.val right.val = true :=
    (molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff left right).mpr edge
  rw [containsUndirectedEdge_eq_true_iff_pair_mem] at contained
  rw [unblockedListEdge_iff]
  rcases contained with forward | reverse
  · refine ⟨(left.val, right.val), forward, ?_, Or.inl ⟨rfl, rfl⟩⟩
    have notBound : left.val ≠ molecule.atomCount := Nat.ne_of_lt left.isLt
    simp [notBound]
  · refine ⟨(right.val, left.val), reverse, ?_, Or.inr ⟨rfl, rfl⟩⟩
    have notBound : right.val ≠ molecule.atomCount := Nat.ne_of_lt right.isLt
    simp [notBound]

/-- The executable semantic component traversal is exactly independent relational connectivity
in the localized mancude graph. -/
theorem mem_semanticLocalizedMancudeComponentVertices_iff
    (molecule : SemanticMolecule) (attached atom : Fin molecule.atomCount) :
    atom.val ∈ molecule.semanticLocalizedMancudeComponentVertices attached.val ↔
      molecule.toLocalizedMoleculeGraph.InMancudeComponent attached atom := by
  have bounded : ∀ edge ∈ molecule.semanticLocalizedMancudeEdges,
      edge.1 < molecule.atomCount ∧ edge.2 < molecule.atomCount :=
    fun edge edgePresent => molecule.endpoints_lt_of_mem_semanticLocalizedMancudeEdges
      edgePresent
  unfold semanticLocalizedMancudeComponentVertices
  rw [edgeComponent_eq_reachableWithoutEdge_sentinel
    molecule.semanticLocalizedMancudeEdges molecule.atomCount bounded]
  constructor
  · intro present
    have rawPath : Relation.ReflTransGen
        (UnblockedListEdge (molecule.atomCount, molecule.atomCount)
          molecule.semanticLocalizedMancudeEdges)
        attached.val atom.val := by
      apply reachableWithoutEdge_sound (molecule.atomCount, molecule.atomCount)
        molecule.semanticLocalizedMancudeEdges attached.val
        (molecule.semanticLocalizedMancudeEdges.length + 1)
        [attached.val] [attached.val]
      · intro current currentPresent
        simp only [List.mem_singleton] at currentPresent
        subst current
        exact Relation.ReflTransGen.refl
      · intro current currentPresent
        simp only [List.mem_singleton] at currentPresent
        subst current
        exact Relation.ReflTransGen.refl
      · exact present
    have convertPath : ∀ current,
        Relation.ReflTransGen
            (UnblockedListEdge (molecule.atomCount, molecule.atomCount)
              molecule.semanticLocalizedMancudeEdges)
            attached.val current →
          ∃ currentBound : current < molecule.atomCount,
            Relation.ReflTransGen molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge
              attached ⟨current, currentBound⟩ := by
      intro current path
      induction path with
      | refl => exact ⟨attached.isLt, Relation.ReflTransGen.refl⟩
      | @tail parent current hprefix step inductionHypothesis =>
          obtain ⟨parentBound, independentPrefix⟩ := inductionHypothesis
          rw [unblockedListEdge_iff] at step
          obtain ⟨edge, edgePresent, _edgeUnblocked, orientation⟩ := step
          have orientedMembership :
              (parent, current) ∈ molecule.semanticLocalizedMancudeEdges ∨
                (current, parent) ∈ molecule.semanticLocalizedMancudeEdges := by
            rcases orientation with ⟨edgeLeft, edgeRight⟩ | ⟨edgeRight, edgeLeft⟩
            · have edgeIdentity : edge = (parent, current) := Prod.ext edgeLeft edgeRight
              exact Or.inl (by simpa [edgeIdentity] using edgePresent)
            · have edgeIdentity : edge = (current, parent) := Prod.ext edgeLeft edgeRight
              exact Or.inr (by simpa [edgeIdentity] using edgePresent)
          have currentBound : current < molecule.atomCount := by
            rcases orientedMembership with forward | reverse
            · exact (molecule.endpoints_lt_of_mem_semanticLocalizedMancudeEdges forward).2
            · exact (molecule.endpoints_lt_of_mem_semanticLocalizedMancudeEdges reverse).1
          let parentFin : Fin molecule.atomCount := ⟨parent, parentBound⟩
          let currentFin : Fin molecule.atomCount := ⟨current, currentBound⟩
          have localized :
              molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge parentFin currentFin := by
            apply (molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
              parentFin currentFin).mp
            rw [containsUndirectedEdge_eq_true_iff_pair_mem]
            exact orientedMembership
          exact ⟨currentBound, independentPrefix.tail localized⟩
    obtain ⟨atomBound, independentPath⟩ := convertPath atom.val rawPath
    have atomIdentity : (⟨atom.val, atomBound⟩ : Fin molecule.atomCount) = atom := Fin.ext rfl
    simpa [MoleculeGraph.InMancudeComponent, atomIdentity] using independentPath
  · intro component
    have rawPath : Relation.ReflTransGen
        (UnblockedListEdge (molecule.atomCount, molecule.atomCount)
          molecule.semanticLocalizedMancudeEdges)
        attached.val atom.val :=
      component.lift Fin.val fun _ _ edge =>
        molecule.unblockedSentinelEdge_of_semanticLocalizedMancudeEdge edge
    exact reachableWithoutEdge_complete_from_start_of_reflTransGen
      (molecule.atomCount, molecule.atomCount)
      molecule.semanticLocalizedMancudeEdges attached.val rawPath

def semanticLocalizedMancudeComponentEdges (molecule : SemanticMolecule) (attached : Nat) :
    List (Nat × Nat) :=
  molecule.semanticLocalizedMancudeEdges.filter fun edge =>
    (molecule.semanticLocalizedMancudeComponentVertices attached).contains edge.1 &&
      (molecule.semanticLocalizedMancudeComponentVertices attached).contains edge.2

def semanticLocalizedMancudeWrittenEdges (molecule : SemanticMolecule) (attached : Nat) :
    List (Nat × Nat) :=
  (molecule.semanticLocalizedMancudeComponentEdges attached).filter fun edge =>
    molecule.localizedBondOrder edge.1 edge.2 == 2

/-- The component-filtered executable list realizes exactly the independent localized component
at `attached`. -/
theorem natEdgeMatchedBy_semanticLocalizedMancudeComponentEdges_iff
    (molecule : SemanticMolecule) (attached left right : Fin molecule.atomCount) :
    NatEdgeMatchedBy (molecule.semanticLocalizedMancudeComponentEdges attached.val)
        left right ↔
      molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right ∧
        molecule.toLocalizedMoleculeGraph.InMancudeComponent attached left := by
  constructor
  · rintro ⟨edge, edgePresent, incident⟩
    unfold semanticLocalizedMancudeComponentEdges at edgePresent
    rw [List.mem_filter] at edgePresent
    have localizedPresent := edgePresent.1
    have componentChecks :
        (molecule.semanticLocalizedMancudeComponentVertices attached.val).contains edge.1 = true ∧
          (molecule.semanticLocalizedMancudeComponentVertices attached.val).contains edge.2 = true := by
      simpa only [Bool.and_eq_true] using edgePresent.2
    simp only [List.contains_eq_mem] at componentChecks
    have contained : containsUndirectedEdge molecule.semanticLocalizedMancudeEdges
        left.val right.val = true := by
      rw [containsUndirectedEdge_eq_true_iff_pair_mem]
      rcases incident with forward | reverse
      · exact Or.inl (by simpa [forward] using localizedPresent)
      · exact Or.inr (by simpa [reverse] using localizedPresent)
    refine ⟨(molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
      left right).mp contained, ?_⟩
    rcases incident with forward | reverse
    · have edgeFirst : edge.1 = left.val := congrArg Prod.fst forward
      exact (molecule.mem_semanticLocalizedMancudeComponentVertices_iff attached left).mp
        (by simpa [edgeFirst] using componentChecks.1)
    · have edgeSecond : edge.2 = left.val := congrArg Prod.snd reverse
      exact (molecule.mem_semanticLocalizedMancudeComponentVertices_iff attached left).mp
        (by simpa [edgeSecond] using componentChecks.2)
  · rintro ⟨localized, leftComponent⟩
    have rightComponent :
        molecule.toLocalizedMoleculeGraph.InMancudeComponent attached right :=
      leftComponent.tail localized
    have leftPresent : left.val ∈
        molecule.semanticLocalizedMancudeComponentVertices attached.val :=
      (molecule.mem_semanticLocalizedMancudeComponentVertices_iff attached left).mpr
        leftComponent
    have rightPresent : right.val ∈
        molecule.semanticLocalizedMancudeComponentVertices attached.val :=
      (molecule.mem_semanticLocalizedMancudeComponentVertices_iff attached right).mpr
        rightComponent
    have contained :
        (left.val, right.val) ∈ molecule.semanticLocalizedMancudeEdges ∨
          (right.val, left.val) ∈ molecule.semanticLocalizedMancudeEdges := by
      rw [← containsUndirectedEdge_eq_true_iff_pair_mem]
      exact (molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
        left right).mpr localized
    rcases contained with forward | reverse
    · refine ⟨(left.val, right.val), ?_, Or.inl rfl⟩
      unfold semanticLocalizedMancudeComponentEdges
      rw [List.mem_filter]
      exact ⟨forward, by simp [leftPresent, rightPresent]⟩
    · refine ⟨(right.val, left.val), ?_, Or.inr rfl⟩
      unfold semanticLocalizedMancudeComponentEdges
      rw [List.mem_filter]
      exact ⟨reverse, by simp [leftPresent, rightPresent]⟩

/-- The written subset represents exactly localized component edges whose normalized semantic
bond order is two. -/
theorem natEdgeMatchedBy_semanticLocalizedMancudeWrittenEdges_iff
    (molecule : SemanticMolecule) (attached left right : Fin molecule.atomCount) :
    NatEdgeMatchedBy (molecule.semanticLocalizedMancudeWrittenEdges attached.val)
        left right ↔
      molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right ∧
        molecule.toLocalizedMoleculeGraph.InMancudeComponent attached left ∧
          molecule.toLocalizedMoleculeGraph.bond left right = 2 := by
  constructor
  · rintro ⟨edge, edgePresent, incident⟩
    unfold semanticLocalizedMancudeWrittenEdges at edgePresent
    rw [List.mem_filter] at edgePresent
    have componentMatched :
        NatEdgeMatchedBy (molecule.semanticLocalizedMancudeComponentEdges attached.val)
          left right := ⟨edge, edgePresent.1, incident⟩
    have componentFacts :=
      (molecule.natEdgeMatchedBy_semanticLocalizedMancudeComponentEdges_iff
        attached left right).mp componentMatched
    refine ⟨componentFacts.1, componentFacts.2, ?_⟩
    simp only [beq_iff_eq] at edgePresent
    rcases incident with forward | reverse
    · have leftValue : edge.1 = left.val := congrArg Prod.fst forward
      have rightValue : edge.2 = right.val := congrArg Prod.snd forward
      simpa [SemanticMolecule.toLocalizedMoleculeGraph_bond, leftValue, rightValue] using
        edgePresent.2
    · have leftValue : edge.2 = left.val := congrArg Prod.snd reverse
      have rightValue : edge.1 = right.val := congrArg Prod.fst reverse
      rw [molecule.toLocalizedMoleculeGraph.bond_symm left right]
      simpa [SemanticMolecule.toLocalizedMoleculeGraph_bond, leftValue, rightValue] using
        edgePresent.2
  · rintro ⟨localized, component, doubleOrder⟩
    obtain ⟨edge, edgePresent, incident⟩ :=
      (molecule.natEdgeMatchedBy_semanticLocalizedMancudeComponentEdges_iff
        attached left right).mpr ⟨localized, component⟩
    refine ⟨edge, ?_, incident⟩
    unfold semanticLocalizedMancudeWrittenEdges
    rw [List.mem_filter]
    refine ⟨edgePresent, ?_⟩
    simp only [beq_iff_eq]
    rcases incident with forward | reverse
    · have leftValue : edge.1 = left.val := congrArg Prod.fst forward
      have rightValue : edge.2 = right.val := congrArg Prod.snd forward
      simpa [SemanticMolecule.toLocalizedMoleculeGraph_bond, leftValue, rightValue] using
        doubleOrder
    · have leftValue : edge.2 = left.val := congrArg Prod.snd reverse
      have rightValue : edge.1 = right.val := congrArg Prod.fst reverse
      have reverseOrder := molecule.toLocalizedMoleculeGraph.bond_symm left right |>.symm.trans
        doubleOrder
      simpa [SemanticMolecule.toLocalizedMoleculeGraph_bond, leftValue, rightValue] using
        reverseOrder

end SemanticMolecule

end

namespace SemanticMolecule

open RawMolecule

/-! ## Exhaustive executable partner-function realization

Everything below is deliberately outside the file's `noncomputable section`.  This makes Lean
reject any accidental classical implementation dependency instead of silently erasing runtime
code from the authoritative executable observation.
-/

/-- Boolean finite test of the independent partner-function matching clauses. -/
def semanticMancudeMatching? (molecule : SemanticMolecule)
    (attached : Fin molecule.atomCount)
    (partner : Fin molecule.atomCount → Option (Fin molecule.atomCount)) : Bool :=
  ((List.finRange molecule.atomCount).all fun atom =>
      (molecule.semanticLocalizedMancudeComponentVertices attached.val).contains atom.val ||
        decide (partner atom = none)) &&
  ((List.finRange molecule.atomCount).all fun left =>
    (List.finRange molecule.atomCount).all fun right =>
      decide (partner left = some right) ==
        (decide (partner right = some left) &&
          containsUndirectedEdge molecule.semanticLocalizedMancudeEdges
            left.val right.val))

@[simp] theorem semanticMancudeMatching?_eq_true_iff
    (molecule : SemanticMolecule) (attached : Fin molecule.atomCount)
    (partner : Fin molecule.atomCount → Option (Fin molecule.atomCount)) :
    molecule.semanticMancudeMatching? attached partner = true ↔
      molecule.toLocalizedMoleculeGraph.IsMancudeMatching attached partner := by
  unfold semanticMancudeMatching?
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨outsideChecked, pairedChecked⟩
    constructor
    · intro atom outside
      have checked := (List.all_eq_true.mp outsideChecked) atom
        (by simp)
      rw [Bool.or_eq_true] at checked
      rcases checked with componentPresent | noneObserved
      · have component :=
          (molecule.mem_semanticLocalizedMancudeComponentVertices_iff attached atom).mp
            (List.contains_iff_mem.mp componentPresent)
        exact (outside component).elim
      · exact of_decide_eq_true noneObserved
    · intro left right
      have checked := (List.all_eq_true.mp
        ((List.all_eq_true.mp pairedChecked) left
          (by simp))) right (by simp)
      simp only [beq_iff_eq] at checked
      constructor
      · intro leftPartner
        have rightFacts :
            decide (partner right = some left) = true ∧
              containsUndirectedEdge molecule.semanticLocalizedMancudeEdges
                left.val right.val = true := by
          simpa [leftPartner] using checked.symm
        exact ⟨of_decide_eq_true rightFacts.1,
          (molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
            left right).mp rightFacts.2⟩
      · rintro ⟨rightPartner, localized⟩
        have edgeChecked : containsUndirectedEdge molecule.semanticLocalizedMancudeEdges
            left.val right.val = true :=
          (molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
            left right).mpr localized
        have : decide (partner left = some right) = true := by
          rw [checked]
          simp [rightPartner, edgeChecked]
        exact of_decide_eq_true this
  · rintro ⟨outside, paired⟩
    constructor
    · apply List.all_eq_true.mpr
      intro atom _present
      by_cases componentPresent : atom.val ∈
          molecule.semanticLocalizedMancudeComponentVertices attached.val
      · rw [Bool.or_eq_true]
        exact Or.inl (List.contains_iff_mem.mpr componentPresent)
      · rw [Bool.or_eq_true]
        have noneObserved : partner atom = none := outside atom (by
          intro component
          exact componentPresent
            ((molecule.mem_semanticLocalizedMancudeComponentVertices_iff
              attached atom).mpr component))
        exact Or.inr (decide_eq_true noneObserved)
    · apply List.all_eq_true.mpr
      intro left _leftPresent
      apply List.all_eq_true.mpr
      intro right _rightPresent
      simp only [beq_iff_eq]
      by_cases leftPartner : partner left = some right
      · have facts := (paired left right).mp leftPartner
        rw [decide_eq_true leftPartner, decide_eq_true facts.1,
          (molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
            left right).mpr facts.2]
        rfl
      · have notBoth : ¬ (partner right = some left ∧
            molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right) := by
          intro facts
          exact leftPartner ((paired left right).mpr facts)
        rw [decide_eq_false leftPartner]
        by_cases rightPartner : partner right = some left
        · have notLocalized :
              ¬ molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge left right :=
            fun localized => notBoth ⟨rightPartner, localized⟩
          rw [decide_eq_true rightPartner, Bool.true_and]
          symm
          exact Bool.eq_false_iff.mpr fun edgeChecked => notLocalized
              ((molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
                left right).mp edgeChecked)
        · simp [rightPartner]

/-! ### Computable enumeration of every finite partner function

`Finset.toList` intentionally has no executable implementation because a `Finset` does not carry
an ordering.  The exhaustive search therefore enumerates function tables directly: every row has
one `Option (Fin n)` entry per atom, then the row is read as a partner function. -/

/-- Every possible value of one entry in a partner-function table. -/
def semanticPartnerValues (atomCount : Nat) : List (Option (Fin atomCount)) :=
  none :: (List.finRange atomCount).map some

@[simp] theorem mem_semanticPartnerValues (atomCount : Nat)
    (value : Option (Fin atomCount)) :
    value ∈ semanticPartnerValues atomCount := by
  cases value <;> simp [semanticPartnerValues]

/-- All rows of a requested length over the finite partner-value alphabet. -/
def semanticPartnerRows (atomCount : Nat) : Nat → List (List (Option (Fin atomCount)))
  | 0 => [[]]
  | remaining + 1 =>
      (semanticPartnerValues atomCount).flatMap fun value =>
        (semanticPartnerRows atomCount remaining).map (value :: ·)

@[simp] theorem mem_semanticPartnerRows_iff (atomCount remaining : Nat)
    (row : List (Option (Fin atomCount))) :
    row ∈ semanticPartnerRows atomCount remaining ↔ row.length = remaining := by
  induction remaining generalizing row with
  | zero => simp [semanticPartnerRows]
  | succ remaining ih =>
      cases row with
      | nil => simp [semanticPartnerRows]
      | cons value tail => simp [semanticPartnerRows, ih]

/-- Interpret a finite row as a total partner function; generated rows have exactly the required
length, so the default is unreachable on the exhaustive family. -/
def semanticPartnerFunctionOfRow (atomCount : Nat)
    (row : List (Option (Fin atomCount))) :
    Fin atomCount → Option (Fin atomCount) :=
  fun atom => (row[atom.val]?).getD none

/-- Canonical explicit list covering every partner function on `Fin atomCount`. -/
def semanticPartnerFunctions (atomCount : Nat) :
    List (Fin atomCount → Option (Fin atomCount)) :=
  (semanticPartnerRows atomCount atomCount).map
    (semanticPartnerFunctionOfRow atomCount)

theorem mem_semanticPartnerFunctions (atomCount : Nat)
    (partner : Fin atomCount → Option (Fin atomCount)) :
    partner ∈ semanticPartnerFunctions atomCount := by
  rw [semanticPartnerFunctions, List.mem_map]
  refine ⟨List.ofFn partner, ?_, ?_⟩
  · simp
  · funext atom
    simp [semanticPartnerFunctionOfRow]

theorem semanticPartnerFunctions_toFinset (atomCount : Nat) :
    (semanticPartnerFunctions atomCount).toFinset =
      (Finset.univ : Finset (Fin atomCount → Option (Fin atomCount))) := by
  letI : DecidableEq (Fin atomCount → Option (Fin atomCount)) :=
    Fintype.decidablePiFintype
  ext partner
  simp [mem_semanticPartnerFunctions]

/-- Exhaustive finite maximum family, computed by enumerating every partner function. -/
def semanticMaximumMancudeMatchings (molecule : SemanticMolecule)
    (attached : Fin molecule.atomCount) :
    Finset (Fin molecule.atomCount → Option (Fin molecule.atomCount)) := by
  /- Force the finite extensional equality procedure for partner functions.  In this file's
  noncomputable proof section, an unconstrained synthesis can otherwise select classical
  function equality and erase the executable code for the exhaustive search. -/
  letI : DecidableEq
      (Fin molecule.atomCount → Option (Fin molecule.atomCount)) :=
    Fintype.decidablePiFintype
  let partners := semanticPartnerFunctions molecule.atomCount
  exact partners.toFinset.filter fun partner =>
    molecule.semanticMancudeMatching? attached partner &&
      partners.all fun other =>
        !molecule.semanticMancudeMatching? attached other ||
          decide (MoleculeGraph.mancudeSaturation other ≤
            MoleculeGraph.mancudeSaturation partner)

/-- The executable exhaustive maximum family is extensionally the independent finite family. -/
theorem semanticMaximumMancudeMatchings_eq_independent
    (molecule : SemanticMolecule) (attached : Fin molecule.atomCount) :
    molecule.semanticMaximumMancudeMatchings attached =
      molecule.toLocalizedMoleculeGraph.maximumMancudeMatchings attached := by
  classical
  ext partner
  simp only [semanticMaximumMancudeMatchings, Finset.mem_filter,
    semanticPartnerFunctions_toFinset, Finset.mem_univ, true_and, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, semanticMancudeMatching?_eq_true_iff,
    MoleculeGraph.maximumMancudeMatchings]
  constructor
  · rintro ⟨matching, greatest⟩
    exact ⟨matching, fun other otherMatching => by
      rcases greatest other (mem_semanticPartnerFunctions _ other) with
          notMatching | bounded
      · have testFalse : molecule.semanticMancudeMatching? attached other = false := by
          simpa using notMatching
        have testTrue := (molecule.semanticMancudeMatching?_eq_true_iff
          attached other).mpr otherMatching
        rw [testFalse] at testTrue
        contradiction
      · exact bounded⟩
  · rintro ⟨matching, greatest⟩
    exact ⟨matching, fun other _present => by
      by_cases otherMatching :
          molecule.toLocalizedMoleculeGraph.IsMancudeMatching attached other
      · exact Or.inr (greatest other otherMatching)
      · have testFalse : molecule.semanticMancudeMatching? attached other = false := by
          apply Bool.eq_false_iff.mpr
          intro testTrue
          exact otherMatching ((molecule.semanticMancudeMatching?_eq_true_iff
            attached other).mp testTrue)
        exact Or.inl (by simp [testFalse])⟩

/-- Executable exact mean over the exhaustive maximum partner family. -/
def semanticExactMancudeAverage (molecule : SemanticMolecule)
    (attached : Fin molecule.atomCount) : DeclarativeCIP.ExactAtomicNumber where
  numerator := (molecule.semanticMaximumMancudeMatchings attached).sum
    (molecule.toLocalizedMoleculeGraph.mancudePartnerAtomicNumber attached)
  denominator := (molecule.semanticMaximumMancudeMatchings attached).card
  denominator_pos := by
    rw [molecule.semanticMaximumMancudeMatchings_eq_independent attached]
    exact Finset.card_pos.mpr
      (molecule.toLocalizedMoleculeGraph.maximumMancudeMatchings_nonempty attached)

/-- The executable all-function enumeration computes exactly the independent Rule-1a mean. -/
theorem semanticExactMancudeAverage_eq_independent
    (molecule : SemanticMolecule) (attached : Fin molecule.atomCount) :
    molecule.semanticExactMancudeAverage attached =
      molecule.toLocalizedMoleculeGraph.exactMancudeAverage attached := by
  apply DeclarativeCIP.ExactAtomicNumber.ext
  · unfold MoleculeGraph.exactMancudeAverage
    change (molecule.semanticMaximumMancudeMatchings attached).sum _ = _
    rw [molecule.semanticMaximumMancudeMatchings_eq_independent attached]
  · unfold MoleculeGraph.exactMancudeAverage
    change (molecule.semanticMaximumMancudeMatchings attached).card = _
    rw [molecule.semanticMaximumMancudeMatchings_eq_independent attached]

/-- Executable exact Rule-1a observation for one represented multiple-bond duplicate. -/
def semanticExactRule1aMultipleBond (molecule : SemanticMolecule)
    (attached duplicated : Fin molecule.atomCount) : DeclarativeCIP.ExactAtomicNumber :=
  if containsUndirectedEdge molecule.semanticLocalizedMancudeEdges
      attached.val duplicated.val then
    molecule.semanticExactMancudeAverage attached
  else
    .ofNat (molecule.toLocalizedMoleculeGraph.atomZ duplicated)

theorem semanticExactRule1aMultipleBond_eq_independent
    (molecule : SemanticMolecule) (attached duplicated : Fin molecule.atomCount) :
    molecule.semanticExactRule1aMultipleBond attached duplicated =
      molecule.toLocalizedMoleculeGraph.exactRule1aMultipleBond attached duplicated := by
  unfold semanticExactRule1aMultipleBond MoleculeGraph.exactRule1aMultipleBond
  by_cases localized :
      molecule.toLocalizedMoleculeGraph.LocalizedMancudeEdge attached duplicated
  · rw [(molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
      attached duplicated).mpr localized]
    simp [localized, molecule.semanticExactMancudeAverage_eq_independent attached]
  · have absent : containsUndirectedEdge molecule.semanticLocalizedMancudeEdges
        attached.val duplicated.val = false := by
      exact Bool.eq_false_iff.mpr fun present => localized
        ((molecule.containsUndirectedEdge_semanticLocalizedMancudeEdges_iff
          attached duplicated).mp present)
    simp [absent, localized]

/-- Executable exact observation for an official provenance node. -/
def semanticExactOfficialRule1aObservation (molecule : SemanticMolecule)
    (node : OfficialCIPNode (Fin molecule.atomCount)) :
    DeclarativeCIP.ExactAtomicNumber :=
  match node.current? with
  | none => .zero
  | some atom =>
      match node.provenance with
      | .multipleBondDuplicate _ =>
          match node.parent? with
          | none => .ofNat (molecule.toLocalizedMoleculeGraph.atomZ atom)
          | some attached => molecule.semanticExactRule1aMultipleBond attached atom
      | _ => .ofNat (molecule.toLocalizedMoleculeGraph.atomZ atom)

/-- The executable node observation equals the independent graph-theoretic observation. -/
theorem semanticExactOfficialRule1aObservation_eq_independent
    (molecule : SemanticMolecule) (node : OfficialCIPNode (Fin molecule.atomCount)) :
    molecule.semanticExactOfficialRule1aObservation node =
      molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node := by
  unfold semanticExactOfficialRule1aObservation MoleculeGraph.exactOfficialRule1aObservation
  cases currentObserved : node.current? with
  | none => rfl
  | some current =>
      cases provenanceObserved : node.provenance with
      | realAtom => rfl
      | ringDuplicate distance => rfl
      | placeholder kind distance => rfl
      | multipleBondDuplicate distance =>
          cases parentObserved : node.parent? with
          | none => rfl
          | some attached =>
              exact molecule.semanticExactRule1aMultipleBond_eq_independent attached current


end SemanticMolecule

end TetraStereo.OneCenter
