import TetraStereo.Engine.RingAtomicNeighborOrder
import TetraStereo.Engine.RingAtomicFramePriority
import TetraStereo.Engine.RingPhosphorusAtomicFrame

/-! The public ring evaluator agrees with a graph-only atomic-number calculation
on every request covered by the independent first-shell and terminal-twin tests. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingAtomicNeighborOrder
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Labels)
open RingWrittenPHReadings RingSpatialTransport RingHydrogenSpelling RingHydrogenCompletion
open RingGroupedReport (Report origin)

private theorem tetra_state (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (a : i.certified.Atom) (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (four : (neighbors i.molecule a.val).length = 4)
    (distinct : separated i.molecule a.val = true) :
    RingChemicalGraphProof.state i q = some ((Decision.ranked (neighbors i.molecule a.val)).read i.spatial) := by
  let e := enumeration i a four
  have ids : [(e 0).val.val,(e 1).val.val,(e 2).val.val,(e 3).val.val] = neighbors i.molecule a.val :=
    enumeration_ids i a four
  have actual := RingAtomicFramePriority.state_strict_atomic ok q a real current e
    (fun s => record i (e s).val) (fun s => written i (e s).val) (enumeration_descending i a four distinct)
  rw [inputGeometry_eq,ids] at actual
  exact actual

private theorem phosphorus_eq (i : Input) (a : i.certified.Atom) :
    RingPyramidalPublication.phosphorus i a = (neutralPyramidal i.molecule a.val && (neighbors i.molecule a.val).length == 3) := by
  by_cases h : (neighbors i.molecule a.val).length = 3 <;>
    simp [RingPyramidalPublication.phosphorus,neutralPyramidal,RingPyramidalNitrogen.constrained,degree_eq,h]

private theorem p_state (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (a : i.certified.Atom) (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (allowed : RingPyramidalPublication.phosphorus i a = true)
    (distinct : separated i.molecule a.val = true) :
    RingChemicalGraphProof.state i q =
      some ((Decision.ranked (neighbors i.molecule a.val ++ [a.val])).read i.spatial) := by
  have h := allowed
  rw [phosphorus_eq,Bool.and_eq_true] at h
  have three := beq_iff_eq.mp h.2
  let e := enumeration i a three
  have ids : [(e 0).val.val,(e 1).val.val,(e 2).val.val] = neighbors i.molecule a.val := enumeration_ids i a three
  have actual := RingPhosphorusAtomicFrame.state_strict_atomic ok q a real current allowed e
    (fun s => record i (e s).val) (fun s => written i (e s).val) (enumeration_descending i a three distinct)
  rw [inputGeometry_eq] at actual
  unfold Decision.read
  rw [←ids]
  exact actual

/-- Every successful graph-only assignment determines the actual chemical state
at every real occurrence of this atom, including incoming rerooted ligands. -/
theorem ranked_state (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (a : i.certified.Atom) (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (points : List Nat)
    (hit : classify? i.molecule a.val = some (.ranked points)) :
    RingChemicalGraphProof.state i q = some ((Decision.ranked points).read i.spatial) := by
  have inside : a.val < i.molecule.atomCount := by
    rw [←i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]; exact a.isLt
  simp only [classify?,if_pos inside] at hit
  split at hit
  · rename_i four
    split at hit
    · cases hit
      exact tetra_state i ok q a real current four ‹_›
    · split at hit <;> cases hit
  · split at hit
    · rename_i hp
      split at hit
      · cases hit
        exact p_state i ok q a real current ((phosphorus_eq i a).trans hp) ‹_›
      · cases hit
    · cases hit

/-- Every completed graph decision gives the native root, including
ineligible atoms, terminal-twin parents and flat pyramidal P or As. -/
theorem root_of_decision (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (d : Decision) (hit : classify? i.molecule a.val = some d) :
    RingChemicalGraphProof.root i a = some (d.read i.spatial) := by
  have root : RingChemicalGraphProof.root i a = RingChemicalGraphProof.state i (origin i a) :=
    RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) a
  cases d with
  | ranked pts => exact root.trans (ranked_state i ok _ a rfl rfl pts hit)
  | refuse =>
    have inside : a.val < i.molecule.atomCount := by
      rw [←i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]; exact a.isLt
    simp only [classify?,if_pos inside] at hit
    split at hit
    · rename_i four
      split at hit
      · cases hit
      · split at hit
        · obtain ⟨p,eqn⟩ := twinPair_of_test i a four ‹_›
          exact eqn ▸ p.root_refusal ok
        · cases hit
    · rename_i notFour
      split at hit
      · split at hit <;> cases hit
      · rename_i notP
        have inactive : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (origin i a) := by
          rintro ⟨_,b,current,on⟩
          have same : a = b := Option.some.inj current
          subst b
          simp only [RingPyramidalPublication.eligible,degree_eq,decide_eq_true_eq,Bool.or_eq_true,
            phosphorus_eq,notFour,notP,false_or,Bool.false_eq_true] at on
        exact root.trans ((RingChemicalGraphProof.state_eq i _).trans (RingChemicalGraphProof.skips i _ _ inactive))

/-- Coverage is a finite test on raw atoms and bonds. Only requested atoms need
to be covered. Unresolved priorities elsewhere in the graph are unrestricted. -/
def covered (m : RawMolecule) (ids : List Nat) : Bool :=
  ids.all fun n => (classify? m n).isSome

private theorem found {m : RawMolecule} {ids : List Nat} (yes : covered m ids = true)
    {n : Nat} (mem : n ∈ ids) : ∃ d, classify? m n = some d :=
  Option.isSome_iff_exists.mp ((List.all_eq_true.mp yes) n mem)

private theorem direct_rows (m : RawMolecule) (x : SpatialConfiguration) (ids : List Nat)
    (yes : covered m ids = true) :
    directReport? m x ids = some (ids.map fun n => (n,((classify? m n).map (fun d => d.read x)).join)) := by
  induction ids with
  | nil => rfl
  | cons n ns ih =>
    obtain ⟨d,hit⟩ := found yes (List.mem_cons_self (a := n) (l := ns))
    have rest := ih (List.all_eq_true.mpr (fun a ha => List.all_eq_true.mp yes a (List.mem_cons_of_mem _ ha)))
    simp only [directReport?,List.mapM_cons,List.map_cons,hit,Option.map_some,Option.join_some]
    change (do let tail ← directReport? m x ns; pure ((n,d.read x)::tail)) = _
    rw [rest]; rfl

/-- An independent calculation from raw bonds, atom records and coordinates
returns exactly the complete public rows on any covered hydrogen-complete input. -/
theorem closed_report (i : Input) (ok : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (closed : plan i.molecule = []) (ids : List Nat) (yes : covered i.molecule ids = true) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial ids = directReport? i.molecule i.spatial ids := by
  rw [direct_rows _ _ _ yes]
  apply raw_of_root_labels i _ closed ok
  · intro n hn
    obtain ⟨d,hit⟩ := found yes hn
    by_contra off
    simp [classify?,off] at hit
  · intro a member
    obtain ⟨d,hit⟩ := found yes member
    simpa only [hit,Option.map_some,Option.join_some] using root_of_decision i ok a d hit

/-- On an admitted preparation the source API gives exactly the ordered rows
shared by all physically allowed pyramidal hydrogen placements according to the direct rule. -/
theorem source_report_iff (s i : Input)
    (gs : LocalizedChemicalRing.coordinatesAdmitted s = true)
    (prep : prepare? s.molecule s.spatial = some (i.molecule,i.spatial))
    (gi : LocalizedChemicalRing.coordinatesAdmitted i = true) (ids : List Nat)
    (bounds : ∀ n ∈ ids, n < s.molecule.atomCount) (yes : covered i.molecule ids = true) (rows : Report) :
    RingHydrogenReport.fromRaw? s.molecule s.spatial ids = some rows ↔
      ∀ x, Placement s.molecule s.spatial i.molecule i.spatial x →
        directReport? i.molecule x ids = some rows := by
  rw [fromRaw_all_placements (readmit s) gs prep ids bounds rows]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hp
  obtain ⟨j,admit,gate⟩ := placement_admission hp (prepare?_certified prep) (readmit i)
  obtain ⟨jm,jx⟩ := RingChemicalReport.admission_fields admit
  have eqn := closed_report j (gate.trans gi) (jm ▸ prepare?_closed prep) ids (jm ▸ yes)
  rw [jm,jx] at eqn
  exact (congrArg (· = some rows) eqn).to_iff

end TetraStereo.Engine.RingAtomicNeighborOrder
assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.ranked_state
assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.root_of_decision
assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.closed_report
assert_kernel_only TetraStereo.Engine.RingAtomicNeighborOrder.source_report_iff
