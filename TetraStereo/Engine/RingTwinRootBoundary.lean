import TetraStereo.Engine.RingTerminalTwinRefusal

/-! Structural boundary for visits whose original root is a terminal ligand.
These results identify the parent occurrence and its first-rule atomic observation.
They do not yet establish equality of the inward/outward full-path marked keys. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingTwinRootBoundary
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingGraphPaths (Path Represents)
open RingHydrogenLeafGeometry (SupportedLeaf)

private theorem root_or_parent {i : Input} {leaf parent current : i.certified.Atom}
    {history : List i.certified.Atom} (support : SupportedLeaf i leaf parent)
    (path : Path i leaf history current) :
    (history = [leaf] ∧ current = leaf) ∨ parent ∈ history := by
  induction path with
  | origin => exact Or.inl ⟨rfl,rfl⟩
  | @step history current next prior bond fresh ih =>
    apply Or.inr
    rcases ih with ⟨rfl,rfl⟩ | old
    · have same : next = parent := (support next).mp bond
      simp [same]
    · exact List.mem_cons_of_mem _ old

/-- A real visit from a terminal root to its own parent has exactly one edge.
In particular, cycles elsewhere cannot produce a second real visit to this parent. -/
theorem terminal_parent_history {i : Input} {leaf parent : i.certified.Atom}
    {history : List i.certified.Atom} (support : SupportedLeaf i leaf parent)
    (different : leaf ≠ parent) (path : Path i leaf history parent) :
    history = [parent,leaf] := by
  cases path with
  | origin => exact (different rfl).elim
  | @step history current next prior bond fresh =>
    rcases root_or_parent support prior with ⟨rfl,rfl⟩ | old
    · rfl
    · exact (fresh old).elim

/-- All real parent occurrences at this terminal root have the same retained address. -/
theorem terminal_parent_unique {i : Input} {leaf parent : i.certified.Atom}
    (support : SupportedLeaf i leaf parent) (different : leaf ≠ parent)
    (q t : Site i) (qr : q.val.root = leaf) (tr : t.val.root = leaf)
    (qreal : q.val.node.provenance = .realAtom) (treal : t.val.node.provenance = .realAtom)
    (qc : q.val.node.current? = some parent) (tc : t.val.node.current? = some parent) : q = t := by
  obtain ⟨a,ha,pa⟩ := RingGraphPaths.site_path q qreal
  obtain ⟨b,hb,pb⟩ := RingGraphPaths.site_path t treal
  have ap : a = parent := Option.some.inj (ha.symm.trans qc)
  have bp : b = parent := Option.some.inj (hb.symm.trans tc)
  subst a
  subst b
  rw [qr] at pa
  rw [tr] at pb
  exact RingGraphPaths.unique_site
    ⟨qr,terminal_parent_history support different pa,qreal,qc⟩
    ⟨tr,terminal_parent_history support different pb,treal,tc⟩

/-- Real atom observations ignore root direction, history length and leaf status.
Identical records therefore give identical first-rule observations even when one
cursor is the original root and the other is an outward terminal occurrence. -/
theorem real_observation_eq {i : Input} {d : Nat}
    (q t : LocalizedRerootCursor i.certified d) (a b : i.certified.Atom)
    (qa : q.occurrence.val.node.current? = some a)
    (tb : t.occurrence.val.node.current? = some b)
    (qr : q.occurrence.val.node.provenance = .realAtom)
    (tr : t.occurrence.val.node.provenance = .realAtom)
    (records : i.molecule.atoms[a.val]? = i.molecule.atoms[b.val]?) (x y : Bool) :
    RingRetainedChemicalTrace.observation? i q x =
      RingRetainedChemicalTrace.observation? i t y := by
  simp [RingRetainedChemicalTrace.observation?,qa,tb,records,qr,tr]

end TetraStereo.Engine.RingTwinRootBoundary
assert_kernel_only TetraStereo.Engine.RingTwinRootBoundary.terminal_parent_history
assert_kernel_only TetraStereo.Engine.RingTwinRootBoundary.terminal_parent_unique
assert_kernel_only TetraStereo.Engine.RingTwinRootBoundary.real_observation_eq
