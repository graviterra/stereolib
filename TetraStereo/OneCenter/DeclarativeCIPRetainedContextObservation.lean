import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutionalIso
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Retained-path constitutional observer

Real Rule 1b in the proposed retained outer-digraph profile is the length of the original
occurrence path.  The occurrence steps are the rooted digraph's unique root-first atom walk
(`ancestorAtoms`): the ligand atom at the graph root is the first step, and `occurrenceReading`
already feeds that list to `rerootWalk`.  There is no separate `occurrenceSteps` definition.

The resulting length is not `SimpleGraph.dist` and not `OfficialCIPNode.depth`.  On an acyclic
molecule those quantities agree with the retained path; a simple retained branch around a ring
can be strictly longer than the physical distance.  This module does not erase that difference,
does not claim fresh-root semantics, and does not claim normative-2013 approval.

Rules 1a and 2, and every non-real Rule 1b row, use the existing declarative observations.
A ring, multiple-bond, or phantom duplicate therefore contributes its stored provenance distance.
The canonical key is `ruleKeyWithObservations` at this observer.  No second solver is introduced.
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key sortDesc)

noncomputable section
open scoped Classical

universe u

section Steps

variable {Atom : Type u}

/-- Occurrence steps of one rooted-digraph node.  This is the unique root-first atom walk,
including the ligand atom at the graph root.  It is `none` when that walk is not unique or some
node on it has no atom. -/
def retainedOccurrenceSteps (graph : RootedDigraph Atom) (node : graph.Node) :
    Option (List Atom) :=
  ancestorAtoms graph node

theorem retainedOccurrenceSteps_eq_ancestorAtoms (graph : RootedDigraph Atom) (node : graph.Node) :
    retainedOccurrenceSteps graph node = ancestorAtoms graph node := rfl

private theorem ancestorPath_of_eq_some {graph : RootedDigraph Atom} {node : graph.Node}
    {path : List (Option Atom)} (h : ancestorPath graph node = some path) :
    AncestorPath graph node path ∧
      ∀ other, AncestorPath graph node other → other = path := by
  simp only [ancestorPath] at h
  by_cases hex : ∃! p, AncestorPath graph node p
  · rw [dif_pos hex] at h
    cases h
    refine ⟨Classical.choose_spec hex.exists, ?_⟩
    intro other hother
    exact hex.unique hother (Classical.choose_spec hex.exists)
  · rw [dif_neg hex] at h
    cases h

/-- A root-first ancestor label path has one entry for the ligand root plus one per digraph edge. -/
theorem ancestorPath_length_eq_depth_succ {graph : RootedDigraph Atom} {node : graph.Node}
    {path : List (Option Atom)} (h : AncestorPath graph node path) :
    path.length = graph.depth node + 1 := by
  induction h with
  | root => simp [graph.root_depth]
  | step hedge _ ih =>
      simp only [List.length_append, List.length_singleton, ih, graph.child_depth hedge]

private theorem mapM_id_length {path : List (Option Atom)} {steps : List Atom}
    (h : path.mapM id = some steps) : steps.length = path.length := by
  induction path generalizing steps with
  | nil =>
      simp at h
      cases h
      rfl
  | cons head tail ih =>
      cases head with
      | none =>
          simp [List.mapM_cons] at h
      | some atom =>
          rw [List.mapM_cons] at h
          cases htail : tail.mapM id with
          | none =>
              simp [htail] at h
          | some tailSteps =>
              have hsteps : atom :: tailSteps = steps := by
                simpa [htail] using h
              rw [← hsteps]
              simp [ih htail]

private theorem mapM_id_append_some {path : List (Option Atom)} {steps : List Atom} {atom : Atom}
    (h : path.mapM id = some steps) :
    (path ++ [some atom]).mapM id = some (steps ++ [atom]) := by
  simp [List.mapM_append, h, List.mapM_cons, List.mapM_nil]

theorem retainedOccurrenceSteps_length_eq_depth_succ {graph : RootedDigraph Atom}
    {node : graph.Node} {steps : List Atom}
    (h : retainedOccurrenceSteps graph node = some steps) :
    steps.length = graph.depth node + 1 := by
  unfold retainedOccurrenceSteps ancestorAtoms at h
  cases hpath : ancestorPath graph node with
  | none =>
      rw [hpath] at h
      cases h
  | some path =>
      rw [hpath] at h
      exact (mapM_id_length h).trans (ancestorPath_length_eq_depth_succ
        (ancestorPath_of_eq_some hpath).1)

/-- The ligand root is itself an occurrence step.  Its step list is the singleton ligand atom,
not the empty tail of a walk that starts below the root. -/
theorem retainedOccurrenceSteps_root {graph : RootedDigraph Atom} {leaf : Atom}
    (rootLabel : graph.label graph.root = ⟨some leaf, .realAtom⟩) :
    retainedOccurrenceSteps graph graph.root = some [leaf] := by
  have hpath : AncestorPath graph graph.root [some leaf] := by
    simpa [rootLabel] using (AncestorPath.root (graph := graph))
  have hrootNoParent : ∀ parent, ¬ graph.child parent graph.root := by
    intro parent hedge
    have hdepth := graph.child_depth hedge
    rw [graph.root_depth] at hdepth
    omega
  have hunique : ∀ other, AncestorPath graph graph.root other → other = [some leaf] := by
    intro other hother
    cases hother with
    | root => simp [rootLabel]
    | step hedge _ => exact (hrootNoParent _ hedge).elim
  unfold retainedOccurrenceSteps ancestorAtoms
  rw [ancestorPath_eq_some hpath hunique]
  rfl

/-- Under a parent-preserving addressing, one child extends the occurrence steps by that child's
atom.  The parent list already contains the ligand root. -/
theorem retainedOccurrenceSteps_child {graph : RootedDigraph Atom}
    (addressing : graph.Addressing) {parent node : graph.Node}
    (hchild : graph.child parent node) {parentSteps : List Atom}
    (hparent : retainedOccurrenceSteps graph parent = some parentSteps) {atom : Atom}
    (hatom : (graph.label node).atom? = some atom) :
    retainedOccurrenceSteps graph node = some (parentSteps ++ [atom]) := by
  unfold retainedOccurrenceSteps ancestorAtoms at hparent ⊢
  cases hparentPath : ancestorPath graph parent with
  | none =>
      rw [hparentPath] at hparent
      cases hparent
  | some parentPath =>
      rw [hparentPath] at hparent
      have hrel : AncestorPath graph parent parentPath :=
        (ancestorPath_of_eq_some hparentPath).1
      have hchildRel : AncestorPath graph node (parentPath ++ [some atom]) := by
        simpa [hatom] using (AncestorPath.step hchild hrel)
      have hunique : ∀ other, AncestorPath graph node other →
          other = parentPath ++ [some atom] :=
        fun other hother => ancestorPath_unique_of_addressing addressing hother hchildRel
      rw [ancestorPath_eq_some hchildRel hunique]
      exact mapM_id_append_some hparent

section Walk

variable [DecidableEq Atom]

omit [DecidableEq Atom] in
private theorem incomingAtom?_mem (root : Atom) (path : List Atom) {atom : Atom}
    (h : incomingAtom? root path = some atom) : atom ∈ root :: path := by
  rw [incomingAtom?] at h
  split at h
  · simp at h
  · cases h
    exact List.mem_cons_self
  · rename_i _ _ _ hreverse
    cases h
    have : atom ∈ path.reverse := by rw [hreverse]; simp
    exact List.mem_cons_of_mem _ (List.mem_reverse.1 this)

theorem retainedOccurrenceWalk_singleton (root : Atom) (path : List Atom) (next : Atom) :
    rerootWalk root path [next] = rerootStep root path next := by
  simp [rerootWalk]

/-- An outward simple walk does not pop.  From a start path whose atoms, together with the root
and the new steps, are duplicate-free, `rerootWalk` is ordinary append. -/
theorem retainedOccurrenceWalk_eq_append_of_nodup (root : Atom) :
    ∀ (rest start : List Atom), (root :: (start ++ rest)).Nodup →
      rerootWalk root start rest = start ++ rest
  | [], start, _ => by simp [rerootWalk]
  | next :: rest, start, h => by
      have hdisjoint : (root :: start).Disjoint (next :: rest) :=
        List.disjoint_of_nodup_append (show ((root :: start) ++ (next :: rest)).Nodup from h)
      have hnext : next ∉ root :: start := fun hmem => hdisjoint hmem List.mem_cons_self
      have hstep : rerootStep root start next = start ++ [next] := by
        unfold rerootStep
        rw [if_neg]
        intro hincoming
        exact hnext (incomingAtom?_mem root start hincoming)
      show rerootWalk root (rerootStep root start next) rest = start ++ next :: rest
      rw [hstep, retainedOccurrenceWalk_eq_append_of_nodup root rest (start ++ [next])
        (by simpa using h)]
      simp

/-- Each atom of the occurrence-step list, the ligand root included, is one `rerootStep` of the
original occurrence path. -/
theorem retainedOccurrenceWalk_child (root : Atom) (path parentSteps : List Atom) (atom : Atom) :
    rerootWalk root path (parentSteps ++ [atom]) =
      rerootStep root (rerootWalk root path parentSteps) atom := by
  rw [rerootWalk_append, retainedOccurrenceWalk_singleton]

end Walk

private theorem retainedAncestorPath_transport {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) {node : left.Node} {path : List (Option Atom)}
    (h : AncestorPath left node path) : AncestorPath right (iso.toEquiv node) path := by
  induction h with
  | root =>
      rw [iso.map_label left.root, iso.map_root]
      exact AncestorPath.root
  | step hedge _ ih =>
      rw [iso.map_label]
      exact AncestorPath.step ((iso.map_child _ _).1 hedge) ih

private theorem retainedAncestorPath_iso_iff {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (node : left.Node) (path : List (Option Atom)) :
    AncestorPath left node path ↔ AncestorPath right (iso.toEquiv node) path := by
  refine ⟨retainedAncestorPath_transport iso, fun h => ?_⟩
  have hback := retainedAncestorPath_transport iso.symm h
  rwa [show iso.symm.toEquiv (iso.toEquiv node) = node from iso.toEquiv.symm_apply_apply node]
    at hback

private theorem retainedAncestorPath_iso {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (node : left.Node) :
    ancestorPath left node = ancestorPath right (iso.toEquiv node) := by
  have h := retainedAncestorPath_iso_iff iso node
  unfold ancestorPath
  by_cases hleft : ∃! path, AncestorPath left node path
  · have hright : ∃! path, AncestorPath right (iso.toEquiv node) path :=
      (existsUnique_congr h).1 hleft
    rw [dif_pos hleft, dif_pos hright]
    exact congrArg some (hright.unique ((h _).1 (Classical.choose_spec hleft.exists))
      (Classical.choose_spec hright.exists))
  · have hright : ¬ ∃! path, AncestorPath right (iso.toEquiv node) path :=
      fun hright => hleft ((existsUnique_congr h).2 hright)
    rw [dif_neg hleft, dif_neg hright]

theorem retainedOccurrenceSteps_iso {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (node : left.Node) :
    retainedOccurrenceSteps left node = retainedOccurrenceSteps right (iso.toEquiv node) := by
  unfold retainedOccurrenceSteps ancestorAtoms
  rw [retainedAncestorPath_iso iso]

end Steps

section Observation

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
  (unit : DetectedOccurrence molecule)

local instance retainedObservationNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- Retained-context natural observation.

* Rules 1a and 2 are the established observations.
* A real atom with occurrence steps `steps` contributes
  `(rerootWalk unit.root unit.path steps).length`, the original occurrence-path length.
  `steps` begins with the ligand root.
* A real atom with no unique atom walk falls back to the existing positional Rule 1b value.
  That fallback is not claimed to be an occurrence depth.
* Every other provenance uses the existing Rule 1b value, so a ring duplicate contributes its
  stored distance. -/
def retainedContextRuleValue : ConstitutionalRule → graph.Node → ℕ
  | .rule1aAtomicNumber, node =>
      ruleValue molecule .rule1aAtomicNumber
        (List.replicate (graph.depth node) 0) (some (graph.label node))
  | .rule1bDuplicateNodeProximity, node =>
      match graph.label node, retainedOccurrenceSteps graph node with
      | ⟨some _, .realAtom⟩, some steps =>
          (rerootWalk unit.1.root unit.1.path steps).length
      | _, _ =>
          ruleValue molecule .rule1bDuplicateNodeProximity
            (List.replicate (graph.depth node) 0) (some (graph.label node))
  | .rule2AtomicMass, node =>
      ruleValue molecule .rule2AtomicMass
        (List.replicate (graph.depth node) 0) (some (graph.label node))

def retainedContextNodeObservation (rule : ConstitutionalRule) (node : graph.Node) : ℤ :=
  priorityValue rule (retainedContextRuleValue molecule graph unit rule node)

noncomputable def retainedContextRuleKey (W D : ℕ) (node : graph.Node) : List (Key ℤ) :=
  ruleKeyWithObservations graph W D (retainedContextNodeObservation molecule graph unit) node

theorem retainedContextRuleValue_rule1b_real {node : graph.Node} {atom : Atom} {steps : List Atom}
    (label : graph.label node = ⟨some atom, .realAtom⟩)
    (stepsEq : retainedOccurrenceSteps graph node = some steps) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node =
      (rerootWalk unit.1.root unit.1.path steps).length := by
  simp [retainedContextRuleValue, label, stepsEq]

theorem retainedContextRuleValue_rule1b_real_no_steps {node : graph.Node} {atom : Atom}
    (label : graph.label node = ⟨some atom, .realAtom⟩)
    (noSteps : retainedOccurrenceSteps graph node = none) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node =
      ruleValue molecule .rule1bDuplicateNodeProximity
        (List.replicate (graph.depth node) 0) (some (graph.label node)) := by
  simp [retainedContextRuleValue, label, noSteps]

theorem retainedContextRuleValue_rule1b_eq_ruleValue_of_not_realAtom {node : graph.Node}
    (hnot : (graph.label node).provenance ≠ .realAtom) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node =
      ruleValue molecule .rule1bDuplicateNodeProximity
        (List.replicate (graph.depth node) 0) (some (graph.label node)) := by
  cases hlabel : graph.label node with
  | mk atom? provenance =>
      cases provenance with
      | realAtom =>
          rw [hlabel] at hnot
          exact (hnot rfl).elim
      | multipleBondDuplicate _ =>
          simp [retainedContextRuleValue, hlabel]
      | ringDuplicate _ =>
          simp [retainedContextRuleValue, hlabel]
      | phantom _ =>
          simp [retainedContextRuleValue, hlabel]
      | lonePair _ =>
          simp [retainedContextRuleValue, hlabel]
      | auxiliary _ =>
          simp [retainedContextRuleValue, hlabel]

theorem retainedContextRuleValue_rule1b_ring {node : graph.Node} {atom : Atom} {distance : ℕ}
    (label : graph.label node = ⟨some atom, .ringDuplicate distance⟩) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node = distance := by
  simp [retainedContextRuleValue, ruleValue, nodeRule1bRootDistance, label]

theorem retainedContextRuleValue_rule1b_multipleBond {node : graph.Node} {atom : Atom}
    {distance : ℕ} (label : graph.label node = ⟨some atom, .multipleBondDuplicate distance⟩) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node = distance := by
  simp [retainedContextRuleValue, ruleValue, nodeRule1bRootDistance, label]

theorem retainedContextRuleValue_rule1b_phantom {node : graph.Node} {atom : Atom} {distance : ℕ}
    (label : graph.label node = ⟨some atom, .phantom distance⟩) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node = distance := by
  simp [retainedContextRuleValue, ruleValue, nodeRule1bRootDistance, label]

theorem retainedContextRuleValue_rule1b_root {leaf : Atom}
    (rootLabel : graph.label graph.root = ⟨some leaf, .realAtom⟩) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity graph.root =
      (rerootStep unit.1.root unit.1.path leaf).length := by
  simp [retainedContextRuleValue, rootLabel, retainedOccurrenceSteps_root rootLabel,
    retainedOccurrenceWalk_singleton]

/-- At an empty-path occurrence the ligand root has retained Rule 1b value `1`: the walk step is
the ligand atom itself.  This is the sphere of a ligand root, not digraph depth `0`. -/
theorem retainedContextRuleValue_rule1b_root_top {leaf : Atom}
    (rootPath : unit.1.path = [])
    (rootLabel : graph.label graph.root = ⟨some leaf, .realAtom⟩) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity graph.root = 1 := by
  rw [retainedContextRuleValue_rule1b_root molecule graph unit rootLabel, rootPath, rerootStep_nil]
  simp

theorem retainedContextRuleValue_rule1b_real_child (addressing : graph.Addressing)
    {parent node : graph.Node} {parentSteps : List Atom} {atom : Atom}
    (hchild : graph.child parent node)
    (parentStepsEq : retainedOccurrenceSteps graph parent = some parentSteps)
    (childLabel : graph.label node = ⟨some atom, .realAtom⟩) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node =
      (rerootStep unit.1.root (rerootWalk unit.1.root unit.1.path parentSteps) atom).length := by
  have hchildSteps := retainedOccurrenceSteps_child addressing hchild parentStepsEq
    (by rw [childLabel])
  simp [retainedContextRuleValue, childLabel, hchildSteps, retainedOccurrenceWalk_child]

/-- Intermediate path law.  If an external path is the reconstructed retained walk, real Rule 1b
reads its length.  This does not identify an actual carrier node and is not the completed ring
readback. -/
theorem retainedContextRuleValue_rule1b_of_pathIdentity {node : graph.Node} {atom : Atom}
    {steps path : List Atom} (label : graph.label node = ⟨some atom, .realAtom⟩)
    (stepsEq : retainedOccurrenceSteps graph node = some steps)
    (pathIdentity : path = rerootWalk unit.1.root unit.1.path steps) :
    retainedContextRuleValue molecule graph unit .rule1bDuplicateNodeProximity node =
      path.length := by
  simp [retainedContextRuleValue, label, stepsEq, pathIdentity]

theorem retainedContextNodeObservation_rule1a (node : graph.Node) :
    retainedContextNodeObservation molecule graph unit .rule1aAtomicNumber node =
      nodeObservation molecule graph .rule1aAtomicNumber node := rfl

theorem retainedContextNodeObservation_rule2 (node : graph.Node) :
    retainedContextNodeObservation molecule graph unit .rule2AtomicMass node =
      nodeObservation molecule graph .rule2AtomicMass node := rfl

theorem retainedContextNodeObservation_rule1b_real {node : graph.Node} {atom : Atom}
    {steps : List Atom} (label : graph.label node = ⟨some atom, .realAtom⟩)
    (stepsEq : retainedOccurrenceSteps graph node = some steps) :
    retainedContextNodeObservation molecule graph unit .rule1bDuplicateNodeProximity node =
      -((rerootWalk unit.1.root unit.1.path steps).length : ℤ) := by
  simp [retainedContextNodeObservation, retainedContextRuleValue, priorityValue, label, stepsEq]

theorem retainedContextNodeObservation_rule1b_of_not_realAtom {node : graph.Node}
    (hnot : (graph.label node).provenance ≠ .realAtom) :
    retainedContextNodeObservation molecule graph unit .rule1bDuplicateNodeProximity node =
      nodeObservation molecule graph .rule1bDuplicateNodeProximity node := by
  simp [retainedContextNodeObservation, nodeObservation,
    retainedContextRuleValue_rule1b_eq_ruleValue_of_not_realAtom molecule graph unit hnot]

theorem retainedContextNodeObservation_rule1b_of_pathIdentity {node : graph.Node} {atom : Atom}
    {steps path : List Atom} (label : graph.label node = ⟨some atom, .realAtom⟩)
    (stepsEq : retainedOccurrenceSteps graph node = some steps)
    (pathIdentity : path = rerootWalk unit.1.root unit.1.path steps) :
    retainedContextNodeObservation molecule graph unit .rule1bDuplicateNodeProximity node =
      -(path.length : ℤ) := by
  simp [retainedContextNodeObservation, retainedContextRuleValue, priorityValue, label, stepsEq,
    pathIdentity]

theorem retainedContextNodeObservation_eq_nodeObservation_of_pathLength
    (pathLength : ∀ (node : graph.Node) (atom : Atom) (steps : List Atom),
      graph.label node = ⟨some atom, .realAtom⟩ →
        retainedOccurrenceSteps graph node = some steps →
          (rerootWalk unit.1.root unit.1.path steps).length = graph.depth node + 1) :
    ∀ rule node, retainedContextNodeObservation molecule graph unit rule node =
      nodeObservation molecule graph rule node := by
  intro rule node
  cases rule with
  | rule1aAtomicNumber => rfl
  | rule2AtomicMass => rfl
  | rule1bDuplicateNodeProximity =>
      cases hlabel : graph.label node with
      | mk atom? provenance =>
          cases atom? with
          | none =>
              simp [retainedContextNodeObservation, nodeObservation, retainedContextRuleValue,
                ruleValue, nodeRule1bRootDistance, hlabel]
          | some atom =>
              cases provenance with
              | realAtom =>
                  cases hsteps : retainedOccurrenceSteps graph node with
                  | none =>
                      simp [retainedContextNodeObservation, nodeObservation,
                        retainedContextRuleValue, ruleValue, nodeRule1bRootDistance, hlabel,
                        hsteps]
                  | some steps =>
                      have hlen := pathLength node atom steps hlabel hsteps
                      simp only [retainedContextNodeObservation, nodeObservation,
                        retainedContextRuleValue, hlabel, hsteps]
                      rw [hlen]
                      simp [priorityValue, ruleValue, nodeRule1bRootDistance,
                        List.length_replicate]
              | multipleBondDuplicate _ =>
                  simp [retainedContextNodeObservation, nodeObservation, retainedContextRuleValue,
                    ruleValue, nodeRule1bRootDistance, hlabel]
              | ringDuplicate _ =>
                  simp [retainedContextNodeObservation, nodeObservation, retainedContextRuleValue,
                    ruleValue, nodeRule1bRootDistance, hlabel]
              | phantom _ =>
                  simp [retainedContextNodeObservation, nodeObservation, retainedContextRuleValue,
                    ruleValue, nodeRule1bRootDistance, hlabel]
              | lonePair _ =>
                  simp [retainedContextNodeObservation, nodeObservation, retainedContextRuleValue,
                    ruleValue, nodeRule1bRootDistance, hlabel]
              | auxiliary _ =>
                  simp [retainedContextNodeObservation, nodeObservation, retainedContextRuleValue,
                    ruleValue, nodeRule1bRootDistance, hlabel]

/-- On an empty-path occurrence, a duplicate-free occurrence-step list makes retained observations
agree with the positional canonical observations.  The value is the retained branch length
`depth + 1`.  It is not identified with physical distance. -/
theorem retainedContextNodeObservation_eq_nodeObservation_of_top_simple
    (rootPath : unit.1.path = [])
    (simple : ∀ (node : graph.Node) (atom : Atom) (steps : List Atom),
      graph.label node = ⟨some atom, .realAtom⟩ →
        retainedOccurrenceSteps graph node = some steps →
          (unit.1.root :: steps).Nodup) :
    ∀ rule node, retainedContextNodeObservation molecule graph unit rule node =
      nodeObservation molecule graph rule node :=
  retainedContextNodeObservation_eq_nodeObservation_of_pathLength molecule graph unit
    (fun node atom steps hlabel hsteps => by
      have hnodup := simple node atom steps hlabel hsteps
      have hwalk := retainedOccurrenceWalk_eq_append_of_nodup unit.1.root steps [] hnodup
      calc
        (rerootWalk unit.1.root unit.1.path steps).length
            = (rerootWalk unit.1.root [] steps).length := by rw [rootPath]
        _ = steps.length := by rw [hwalk]; simp
        _ = graph.depth node + 1 := retainedOccurrenceSteps_length_eq_depth_succ hsteps)

theorem retainedContextRuleKey_eq (W D : ℕ) (node : graph.Node) :
    retainedContextRuleKey molecule graph unit W D node =
      ruleKeyWithObservations graph W D
        (retainedContextNodeObservation molecule graph unit) node := rfl

theorem retainedContextRuleKey_getD (W D : ℕ) (rule : ConstitutionalRule) (node : graph.Node) :
    (retainedContextRuleKey molecule graph unit W D node).getD (ruleIndex rule) [] =
      ruleComponentWithObservations graph W D
        (retainedContextNodeObservation molecule graph unit) rule node
        (sortDesc ((graph.childList node).map
          (ruleKeyWithObservations graph W D
            (retainedContextNodeObservation molecule graph unit)))) :=
  ruleKeyWithObservations_getD graph W D
    (retainedContextNodeObservation molecule graph unit) rule node

theorem retainedContextRuleKey_wellShaped (W D : ℕ) (rule : ConstitutionalRule) :
    ∀ node, Certificate.CanonicalSphereKey.WellShaped W D
      ((retainedContextRuleKey molecule graph unit W D node).getD (ruleIndex rule) []) :=
  ruleKeyWithObservations_wellShaped graph W D
    (retainedContextNodeObservation molecule graph unit) rule

theorem retainedContextRuleKey_eq_ruleKey_of_pathLength (W D : ℕ)
    (pathLength : ∀ (node : graph.Node) (atom : Atom) (steps : List Atom),
      graph.label node = ⟨some atom, .realAtom⟩ →
        retainedOccurrenceSteps graph node = some steps →
          (rerootWalk unit.1.root unit.1.path steps).length = graph.depth node + 1)
    (node : graph.Node) :
    retainedContextRuleKey molecule graph unit W D node =
      ruleKey molecule graph W D node := by
  simpa [retainedContextRuleKey] using
    (ruleKeyWithObservations_congr graph W D
      (retainedContextNodeObservation molecule graph unit)
      (nodeObservation molecule graph)
      (retainedContextNodeObservation_eq_nodeObservation_of_pathLength molecule graph unit
        pathLength) node).trans
      (ruleKeyWithObservations_eq_ruleKey graph molecule W D node)

theorem retainedContextRuleKey_eq_ruleKey_of_top_simple (W D : ℕ)
    (rootPath : unit.1.path = [])
    (simple : ∀ (node : graph.Node) (atom : Atom) (steps : List Atom),
      graph.label node = ⟨some atom, .realAtom⟩ →
        retainedOccurrenceSteps graph node = some steps →
          (unit.1.root :: steps).Nodup)
    (node : graph.Node) :
    retainedContextRuleKey molecule graph unit W D node =
      ruleKey molecule graph W D node := by
  simpa [retainedContextRuleKey] using
    (ruleKeyWithObservations_congr graph W D
      (retainedContextNodeObservation molecule graph unit)
      (nodeObservation molecule graph)
      (retainedContextNodeObservation_eq_nodeObservation_of_top_simple molecule graph unit
        rootPath simple) node).trans
      (ruleKeyWithObservations_eq_ruleKey graph molecule W D node)

/-- Retained and physical contextual observations agree only under an explicit distance alignment.
The hypothesis is the regime in which physical distance equals the retained path length.  It is
not proved for cyclic molecules: a simple retained branch can be longer than a physical chord.
This is not normative-2013 approval and not a fresh-root theorem. -/
theorem retainedContextNodeObservation_eq_contextualNodeObservation_of_distance
    (outerRoot : Atom)
    (aligned : ∀ node atom, graph.label node = ⟨some atom, .realAtom⟩ →
      molecule.underlyingSimpleGraph.dist outerRoot atom =
        match retainedOccurrenceSteps graph node with
        | some steps => (rerootWalk unit.1.root unit.1.path steps).length
        | none => graph.depth node + 1) :
    ∀ rule node, retainedContextNodeObservation molecule graph unit rule node =
      contextualNodeObservation molecule graph outerRoot rule node := by
  intro rule node
  cases rule with
  | rule1aAtomicNumber => rfl
  | rule2AtomicMass => rfl
  | rule1bDuplicateNodeProximity =>
      cases hlabel : graph.label node with
      | mk atom? provenance =>
          cases atom? with
          | none =>
              simp [retainedContextNodeObservation, contextualNodeObservation,
                retainedContextRuleValue, contextualRuleValue, hlabel]
          | some atom =>
              cases provenance with
              | realAtom =>
                  cases hsteps : retainedOccurrenceSteps graph node with
                  | some steps =>
                      have hdist := aligned node atom hlabel
                      rw [hsteps] at hdist
                      simp only [retainedContextNodeObservation, contextualNodeObservation,
                        retainedContextRuleValue, contextualRuleValue, priorityValue, hlabel,
                        hsteps]
                      rw [hdist]
                  | none =>
                      have hdist := aligned node atom hlabel
                      rw [hsteps] at hdist
                      simp [retainedContextNodeObservation, contextualNodeObservation,
                        retainedContextRuleValue, contextualRuleValue, priorityValue, ruleValue,
                        nodeRule1bRootDistance, List.length_replicate, hlabel, hsteps, hdist]
              | multipleBondDuplicate _ =>
                  simp [retainedContextNodeObservation, contextualNodeObservation,
                    retainedContextRuleValue, contextualRuleValue, hlabel]
              | ringDuplicate _ =>
                  simp [retainedContextNodeObservation, contextualNodeObservation,
                    retainedContextRuleValue, contextualRuleValue, hlabel]
              | phantom _ =>
                  simp [retainedContextNodeObservation, contextualNodeObservation,
                    retainedContextRuleValue, contextualRuleValue, hlabel]
              | lonePair _ =>
                  simp [retainedContextNodeObservation, contextualNodeObservation,
                    retainedContextRuleValue, contextualRuleValue, hlabel]
              | auxiliary _ =>
                  simp [retainedContextNodeObservation, contextualNodeObservation,
                    retainedContextRuleValue, contextualRuleValue, hlabel]

theorem retainedContextRuleKey_eq_contextualRuleKey_of_distance (outerRoot : Atom)
    (aligned : ∀ node atom, graph.label node = ⟨some atom, .realAtom⟩ →
      molecule.underlyingSimpleGraph.dist outerRoot atom =
        match retainedOccurrenceSteps graph node with
        | some steps => (rerootWalk unit.1.root unit.1.path steps).length
        | none => graph.depth node + 1)
    (W D : ℕ) (node : graph.Node) :
    retainedContextRuleKey molecule graph unit W D node =
      contextualRuleKey molecule graph outerRoot W D node := by
  simpa [retainedContextRuleKey, contextualRuleKey] using
    ruleKeyWithObservations_congr graph W D
      (retainedContextNodeObservation molecule graph unit)
      (contextualNodeObservation molecule graph outerRoot)
      (retainedContextNodeObservation_eq_contextualNodeObservation_of_distance molecule graph unit
        outerRoot aligned) node

end Observation

section Iso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (unit : DetectedOccurrence molecule)
  {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)

local instance retainedLeftNodeFintype : Fintype left.Node := left.nodeFintype
local instance retainedRightNodeFintype : Fintype right.Node := right.nodeFintype

theorem retainedContextNodeObservation_iso (rule : ConstitutionalRule) (node : left.Node) :
    retainedContextNodeObservation molecule right unit rule (iso.toEquiv node) =
      retainedContextNodeObservation molecule left unit rule node := by
  cases rule <;>
    simp [retainedContextNodeObservation, retainedContextRuleValue, priorityValue,
      ← iso.map_label node, ← iso.map_depth node, retainedOccurrenceSteps_iso iso node]

theorem retainedContextRuleKey_iso (W D : ℕ) :
    ∀ node : left.Node,
      retainedContextRuleKey molecule right unit W D (iso.toEquiv node) =
        retainedContextRuleKey molecule left unit W D node := by
  intro node
  simpa [retainedContextRuleKey] using
    ruleKeyWithObservations_iso iso
      (retainedContextNodeObservation molecule left unit)
      (retainedContextNodeObservation molecule right unit) W D
      (fun rule current => retainedContextNodeObservation_iso molecule unit iso rule current) node

end Iso

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceSteps_eq_ancestorAtoms
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorPath_length_eq_depth_succ
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceSteps_length_eq_depth_succ
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceSteps_root
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceSteps_child
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceWalk_singleton
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceWalk_eq_append_of_nodup
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceWalk_child
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedOccurrenceSteps_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_real
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_real_no_steps
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_eq_ruleValue_of_not_realAtom
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_ring
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_multipleBond
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_phantom
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_root
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_root_top
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_real_child
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleValue_rule1b_of_pathIdentity
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_rule1a
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_rule2
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_rule1b_real
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_rule1b_of_not_realAtom
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_rule1b_of_pathIdentity
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_eq_nodeObservation_of_pathLength
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_eq_nodeObservation_of_top_simple
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_getD
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_wellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_eq_ruleKey_of_pathLength
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_eq_ruleKey_of_top_simple
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_eq_contextualNodeObservation_of_distance
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_eq_contextualRuleKey_of_distance
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextNodeObservation_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedContextRuleKey_iso
