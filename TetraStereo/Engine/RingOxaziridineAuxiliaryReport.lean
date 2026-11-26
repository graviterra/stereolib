import TetraStereo.Engine.RingOxaziridineAuxOrder
import TetraStereo.Engine.RingPyramidalPathDecision

/-! Total path-specific public auxiliary descriptors at recognized N-alkyl
oxaziridines. The row depends on the original physical bonds and the visited
path, independently of labels previously published by other occurrences. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridineAuxiliaryReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height distance)
open RingPyramidalSource (Directions)
open RingPyramidalTwoShell (direction score)
open RingTerminalLigandOrder (rank twoRows bonus)
open RingPyramidalPathDecision (reading)
attribute [local instance] lexOrd

/-- No pair of arms of the motif can reach a tie past the terminal-origin
comparison. This includes any combination of real, inward and closure arms. -/
theorem separated {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) (d : Directions i q) :
    Function.Injective (RingTerminalPyramid.weight d) := by
  intro s t equal
  by_contra different
  change rank (direction d s) = rank (direction d t) at equal
  obtain ⟨prefixEq,tail⟩ := List.cons.inj equal
  have b : bonus (direction d s) = bonus (direction d t) := by simpa using tail
  have z : score d s = score d t := prefixEq
  obtain ⟨empty,nonreal,distinct⟩ := RingOxaziridineAuxOrder.collision real current motif d s t different z
  have es : (twoRows (direction d s))[1]? = some [] := empty
  have et : (twoRows (direction d t))[1]? = some [] := prefixEq ▸ es
  have bad := RingTerminalLigandOrder.duplicate_ne real current d s t distinct nonreal
  apply bad
  simp only [bonus,es,et,if_true] at b
  exact b

/-- The graph/path calculation always issues a decision for this real nitrogen.
Its generated hand may be absent on a degenerate pyramid. -/
theorem decision {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    RingPyramidalPathDecision.direct? i q = some (reading i q a) := by
  have selected := RingOxaziridinePublication.motif_focus real current motif
  obtain ⟨d⟩ := RingPyramidalSource.selected_framed selected
  exact RingPyramidalPathDecision.direct_of_strict selected d (separated real current motif d)

/-- Every ready local reader issues exactly the same graph/path reading. -/
theorem local_reading {i : Input} {q : Site i} {a : i.certified.Atom}
    {r : RingNestedActivePair.Reader i} (ready : RingGroupedStereo.Ready q r)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    RingPyramidalPublication.publish i q r = some (reading i q a) :=
  RingPyramidalPathDecision.local_exact ready (decision real current motif)

theorem state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    RingChemicalGraphProof.state i q = some (reading i q a) :=
  RingPyramidalPathDecision.sound geom (decision real current motif)

/-- Precisely which public auxiliary row exists at this address after any
number of complete spheres, and precisely which value the row contains. -/
theorem row_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) (v : Option RingNestedActivePair.Labels) :
    (q,some v) ∈ RingSphereStore.rows i root k ↔
      q.val.root = root ∧ a ≠ root ∧ height i < distance q + k ∧ v = reading i q a := by
  rw [RingSphereStore.row_iff_derives geom root k bound q v]
  constructor
  · rintro ⟨h,b,p,rep,other,_,committed,derived⟩
    obtain rfl := Option.some.inj (current.symm.trans rep.2.2.2)
    have len := RingGraphPaths.path_length rep
    have issued := (RingChemicalGraphProof.path_iff geom p v).mpr derived
    rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep] at issued
    exact ⟨rep.1,other,by omega,Option.some.inj (issued.symm.trans (state geom real current motif))⟩
  · rintro ⟨on,other,committed,rfl⟩
    obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    obtain rfl := Option.some.inj (hb.symm.trans current)
    let p : RingGraphPaths.Path i root q.val.node.history b := on ▸ path
    have rep : RingGraphPaths.Represents q root q.val.node.history b := ⟨on,rfl,real,hb⟩
    have len := RingGraphPaths.path_length rep
    refine ⟨_,b,p,rep,other,?_,by omega,?_⟩
    · simp [RingPyramidalPublication.eligible,RingOxaziridinePublication.motif_selected b motif]
    · apply (RingChemicalGraphProof.path_iff geom p _).mp
      rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep]
      exact state geom real hb motif

/-- Minimum bond distance among real occurrences of this physical atom from
the specified original root. Several paths can attain it. -/
def Nearest {i : Input} (q : Site i) (a : i.certified.Atom) : Prop :=
  ∀ t : Site i, RingGraphPaths.Represents t q.val.root t.val.node.history a → distance q ≤ distance t

/-- A shortest path cannot have a duplicate among its incident directions:
the physical edge to the visited ancestor would shorten that same path. -/
theorem nearest_arm_real {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (nearest : Nearest q a) (w : i.certified.Atom) (arm : RingActivePairs.Arm i)
    (mem : arm ∈ RingRetainedAuxiliary.frame i.certified q)
    (atW : arm.occurrence.val.node.current? = some w) :
    arm.occurrence.val.node.provenance = .realAtom := by
  by_contra nonreal
  obtain ⟨t,_,_,rep,_,_,_,_,shorter⟩ :=
    RingPyramidalPathProvenance.nonreal_arm_shortcut q a w real current arm mem atW nonreal
  exact (Nat.not_le_of_lt shorter) (nearest t ⟨rep.1,rfl,rep.2.2⟩)

/-- Restrict the distance comparison to paths through the same first physical
ligand of the original root. At such a minimum, the only possible incident
closure is to the root itself. This applies at every valence. -/
theorem nearest_in_ligand_closure_is_root {i : Input} {q : Site i} {a w : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (nearest : ∀ t : Site i, RingGraphPaths.Represents t q.val.root t.val.node.history a →
      t.val.node.history.reverse[1]? = q.val.node.history.reverse[1]? → distance q ≤ distance t)
    (arm : RingActivePairs.Arm i) (mem : arm ∈ RingRetainedAuxiliary.frame i.certified q)
    (atW : arm.occurrence.val.node.current? = some w)
    (closure : arm.occurrence.val.node.provenance ≠ .realAtom) : w = q.val.root := by
  by_contra off
  obtain ⟨t,skipped,retained,rep,hist,_,_,length,shorter⟩ :=
    RingPyramidalPathProvenance.nonreal_arm_shortcut q a w real current arm mem atW closure
  have bound : 1 < retained.reverse.length := by simpa using length off
  apply (Nat.not_le_of_lt shorter) (nearest t ⟨rep.1,rfl,rep.2.2⟩ ?_)
  rw [rep.2.1,hist,List.reverse_cons,List.reverse_append,
    List.getElem?_append_left bound,List.getElem?_append_left bound]

/-- At a shortest occurrence every direction has its physical second shell.
For a selected pyramid with three distinct physical signatures the public
auxiliary and root calculations therefore agree, including flat readback. -/
theorem nearest_pyramid {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom} (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (focus : RingPyramidalPublication.focusP i q = some a)
    (nearest : Nearest q a) (row : List Nat) (perm : (RingAtomicNeighborOrder.neighbors i.molecule a.val).Perm row)
    (strict : (row.map (RingSecondShellDecision.signature i.molecule a.val)).Pairwise (· > ·)) :
    RingChemicalGraphProof.state i q = RingChemicalGraphProof.root i a := by
  obtain ⟨d⟩ := RingPyramidalSource.selected_framed focus
  have scores (s : Fin 3) := nearest_arm_real real current nearest (d.atom s) (d.arm s) (d.mem s) (d.real s)
  rw [RingPyramidalTwoShell.root_of_graph_order geom a
    (RingPhysicalFrameBridge.focusP_phosphorus focus) row perm strict]
  apply RingPyramidalTwoShell.state_of_graph_order geom a focus d _ row perm strict
  intro s
  rw [RingOxaziridineAuxOrder.score_projected current d s]
  simp [scores s, RingOxaziridineAuxOrder.projected, RingSecondShellDecision.signature]

/-- Recognition discharges the entire graph-order premise at every shortest
occurrence of an N-alkyl oxaziridine nitrogen. -/
theorem nearest_state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom} (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) (nearest : Nearest q a) :
    RingChemicalGraphProof.state i q = RingChemicalGraphProof.root i a := by
  obtain ⟨o,c,k,perm,strict⟩ :=
    RingOxaziridineRootOrder.descending_row_of_constrained i.molecule a.val motif
  exact nearest_pyramid geom real current (RingOxaziridinePublication.motif_focus real current motif)
    nearest [o,c,k] perm strict

/-- The shortest occurrence publishes the atom's own root descriptor at its
scheduled sphere and retains it at every later cut. -/
theorem nearest_row_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    {q : Site i} {a : i.certified.Atom} (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a) (motif : RingOxaziridineNitrogen.constrained i a = true)
    (nearest : Nearest q a) (v : Option RingNestedActivePair.Labels) :
    (q,some v) ∈ RingSphereStore.rows i root k ↔ q.val.root = root ∧ a ≠ root ∧
      height i < distance q + k ∧ RingChemicalGraphProof.root i a = some v := by
  rw [row_iff geom root k bound real current motif, ← nearest_state geom real current motif nearest,
    state geom real current motif]
  simp only [Option.some.injEq, eq_comm (a := v)]

/-- Any reading different from the atom's own root descriptor has a strictly
nearer occurrence with the exact root descriptor on the same digraph. -/
theorem nearer_agreement_of_difference {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom} (real : q.val.node.provenance = .realAtom)
    (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true)
    (different : RingChemicalGraphProof.state i q ≠ RingChemicalGraphProof.root i a) :
    ∃ t : Site i, RingGraphPaths.Represents t q.val.root t.val.node.history a ∧
      distance t < distance q ∧ Nearest t a ∧ RingChemicalGraphProof.state i t = RingChemicalGraphProof.root i a := by
  classical
  let P := fun n => ∃ t : Site i, RingGraphPaths.Represents t q.val.root t.val.node.history a ∧ distance t = n
  have existsDepth : ∃ n, P n := ⟨_,q,⟨rfl,rfl,real,current⟩,rfl⟩
  obtain ⟨t,rep,depth⟩ := Nat.find_spec existsDepth
  have nearest : Nearest t a := by
    intro u hu
    rw [depth]
    exact Nat.find_min' existsDepth ⟨u,⟨hu.1.trans rep.1,rfl,hu.2.2⟩,rfl⟩
  have native := nearest_state geom rep.2.2.1 rep.2.2.2 motif nearest
  refine ⟨t,rep,?_,nearest,native⟩
  by_contra! back
  apply different
  apply nearest_state geom real current motif
  intro u hu
  exact back.trans (nearest u ⟨hu.1.trans rep.1.symm,rfl,hu.2.2⟩)

end TetraStereo.Engine.RingOxaziridineAuxiliaryReport
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxiliaryReport.separated
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxiliaryReport.local_reading
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxiliaryReport.row_iff
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxiliaryReport.nearest_state
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxiliaryReport.nearer_agreement_of_difference
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxiliaryReport.nearest_row_iff
assert_kernel_only TetraStereo.Engine.RingOxaziridineAuxiliaryReport.nearest_in_ligand_closure_is_root
