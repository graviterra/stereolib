import TetraStereo.Engine.RingOxaziridineNitrogen
import TetraStereo.Engine.RingAtomicNeighborOrder
import TetraStereo.Engine.RingPyramidalEarly
import TetraStereo.Engine.RingSphereStore

/-! Occurrence and public-store consequences of the narrow N-alkyl oxaziridine
motif. The molecular test supplies eligibility, not a prescribed descriptor.
Strict constitutional ligand words read the actual coordinate frame; ties and
degenerate coordinates retain the ordinary public refusal/search behavior. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridinePublication
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (height distance)
open RingPyramidalSource (Directions slots atomId)
open RingNestedActivePair (Labels)
open RingRetainedChemicalPreorder (orderWord)

private theorem atom_bound (i : Input) (a : i.certified.Atom) :
    a.val < i.molecule.atomCount := by
  rw [← i.molecule.toSemanticMolecule?_atomCount _ i.agreement.1]
  exact a.isLt

/-- The raw motif itself supplies the neutral nonaromatic nitrogen record and
the degree-three gate. Neither fact is a separate chemical assumption. -/
theorem motif_gates {i : Input} (a : i.certified.Atom)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    RingOxaziridineNitrogen.atomIs i.molecule a.val .N = true ∧
      Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
  have bound := atom_bound i a
  simp only [RingOxaziridineNitrogen.constrained,
    RingOxaziridineNitrogen.constrainedRaw, dif_pos bound,
    RingOxaziridineNitrogen.test, decide_eq_true_eq] at motif
  obtain ⟨ng,o,no,_,_,c,nc,oc,_,_,_,k,nk,ok,ck,_,_,neighbors,_,_,_,_⟩ := motif
  refine ⟨ng,?_⟩
  rw [RingAtomicNeighborOrder.degree_eq]
  have different : o.val ≠ c.val ∧ o.val ≠ k.val ∧ c.val ≠ k.val := by
    exact ⟨fun h => oc (Fin.ext h), fun h => ok (Fin.ext h), fun h => ck (Fin.ext h)⟩
  have nd : [o.val,c.val,k.val].Nodup := by simp [different.1,different.2.1,different.2.2]
  have nativeND : (RingAtomicNeighborOrder.neighbors i.molecule a.val).Nodup :=
    (RingStereoSiblingPass.legal_order (RingAtomicNeighborOrder.atomicNumber i.molecule) _).perm.nodup_iff.mpr
      ((List.nodup_range).filter _)
  have perm : (RingAtomicNeighborOrder.neighbors i.molecule a.val).Perm [o.val,c.val,k.val] := by
    apply (List.perm_ext_iff_of_nodup nativeND nd).mpr
    intro v
    rw [RingAtomicNeighborOrder.mem_neighbors]
    constructor
    · rintro ⟨hv,edge⟩
      have member := (neighbors (⟨v,hv⟩ : Fin i.molecule.atomCount)).mp edge
      simpa only [List.mem_cons,List.not_mem_nil,or_false] using
        member.imp (congrArg Fin.val) (fun h => h.imp (congrArg Fin.val) (congrArg Fin.val))
    · intro member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      · exact ⟨o.isLt,(neighbors o).mpr (Or.inl rfl)⟩
      · exact ⟨c.isLt,(neighbors c).mpr (Or.inr (Or.inl rfl))⟩
      · exact ⟨k.isLt,(neighbors k).mpr (Or.inr (Or.inr rfl))⟩
  exact perm.length_eq.trans (by rfl)

/-- Every admitted atom in this motif is selected by the public pyramidal
policy. No ligand priority or coordinate reading is assumed. -/
theorem motif_selected {i : Input} (a : i.certified.Atom)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    RingPyramidalPublication.phosphorus i a = true := by
  obtain ⟨record,degree⟩ := motif_gates a motif
  cases written : i.molecule.atoms[a.val]? with
  | none => simp [RingOxaziridineNitrogen.atomIs,written] at record
  | some atom =>
    have fields : (atom.element = .N ∧ atom.charge = 0) ∧ atom.aromatic = false := by
      simpa [RingOxaziridineNitrogen.atomIs,written] using record
    have raw : RingOxaziridineNitrogen.constrainedRaw i.molecule a.val = true := motif
    simp [RingPyramidalPublication.phosphorus,written,fields.1.1,fields.1.2,fields.2,degree,
      RingPyramidalNitrogen.constrained,RingPyramidalNitrogen.constrainedRaw,raw]

theorem motif_focus {i : Input} {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    RingPyramidalPublication.focusP i q = some a := by
  simp [RingPyramidalPublication.focusP,real,current,motif_selected a motif]

/-- At every real occurrence, including an auxiliary occurrence with its
incoming ligand, the public state has an independent two-geometry derivation.
The optional value can be a completed refusal. -/
theorem occurrence {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true) :
    ∃ v : Option Labels, RingChemicalGraphProof.state i q = some v ∧
      RingPyramidalSource.Framed i q
        (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) q) a v := by
  obtain ⟨v,issued,_,_⟩ := RingChemicalGraphProof.total geom q
  refine ⟨v,issued,?_⟩
  have derived := (RingChemicalGraphProof.local_iff geom q v).mpr issued
  simpa only [RingChemicalGraphProof.Local,motif_focus real current motif] using derived

/-- Every committed nonroot occurrence occupies its own addressed row in the
actual public sphere store. Other occurrences of the same atom are not merged. -/
theorem stored {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true)
    (on : q.val.root = root) (other : a ≠ root) (committed : height i < distance q + k) :
    ∃ v : Option Labels, (q,some v) ∈ RingSphereStore.rows i root k ∧
      RingPyramidalSource.Framed i q
        (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) q) a v := by
  obtain ⟨v,issued,source⟩ := occurrence geom real current motif
  refine ⟨v,?_,source⟩
  obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
  obtain rfl := Option.some.inj (hb.symm.trans current)
  let p : RingGraphPaths.Path i root q.val.node.history b := on ▸ path
  have rep : RingGraphPaths.Represents q root q.val.node.history b := ⟨on,rfl,real,hb⟩
  have len := RingGraphPaths.path_length rep
  apply (RingSphereStore.row_iff_derives geom root k bound q v).mpr
  refine ⟨_,b,p,rep,other,?_,by omega,?_⟩
  · simp [RingPyramidalPublication.eligible,motif_selected b motif]
  · apply (RingChemicalGraphProof.path_iff geom p v).mp
    rw [RingGraphPaths.unique_site (RingGraphPaths.represents_site p) rep]
    exact issued

/-- A strict complete constitutional order at an oxaziridine nitrogen yields
the actual physical hand and its opposite. All three keys come from the
molecular digraph; no comparison with the public evaluator is a hypothesis.
A zero determinant remains `some none`. -/
theorem strict_state {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true)
    (d : Directions i q) (cs : Fin 3 → RingRetainedChemicalTrace.Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s))
    (strict : Function.Injective (fun s => orderWord (cs s))) :
    RingChemicalGraphProof.state i q = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        ((RingStereoSiblingPass.order (fun s => orderWord (cs s)) slots).map (atomId d) ++ [a.val])).map
        fun h => (.chiral h,.chiral h.swap)) :=
  RingPyramidalEarly.early_state geom
    (RingPyramidalEarly.early_of (motif_focus real current motif) d cs native strict)

/-- The same physical readback is the root evaluator's result. Root atoms are
read as roots rather than inserted as auxiliary rows in their own store. -/
theorem strict_root {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) (motif : RingOxaziridineNitrogen.constrained i a = true)
    (d : Directions i (RingGroupedReport.origin i a)) (cs : Fin 3 → RingRetainedChemicalTrace.Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s))
    (strict : Function.Injective (fun s => orderWord (cs s))) :
    RingChemicalGraphProof.root i a = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        ((RingStereoSiblingPass.order (fun s => orderWord (cs s)) slots).map (atomId d) ++ [a.val])).map
        fun h => (.chiral h,.chiral h.swap)) := by
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i)]
  exact strict_state geom rfl rfl motif d cs native strict

/-- A strict constitution fixes the value of the addressed public row at
every committed batch prefix, including a nondegenerate hand/opposite pair. -/
theorem strict_stored {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1)
    {q : Site i} {a : i.certified.Atom}
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a)
    (motif : RingOxaziridineNitrogen.constrained i a = true)
    (on : q.val.root = root) (other : a ≠ root) (committed : height i < distance q + k)
    (d : Directions i q) (cs : Fin 3 → RingRetainedChemicalTrace.Key)
    (native : ∀ s, RingRetainedChemicalTrace.key? i (d.arm s) = some (cs s))
    (strict : Function.Injective (fun s => orderWord (cs s))) :
    (q,some ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        ((RingStereoSiblingPass.order (fun s => orderWord (cs s)) slots).map (atomId d) ++ [a.val])).map
        fun h => (.chiral h,.chiral h.swap))) ∈ RingSphereStore.rows i root k := by
  obtain ⟨v,row,source⟩ := stored geom root k bound real current motif on other committed
  have law : RingChemicalGraphProof.Local i q
      (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) q) v := by
    simpa only [RingChemicalGraphProof.Local,motif_focus real current motif] using source
  have issued := (RingChemicalGraphProof.local_iff geom q v).mp law
  have same := Option.some.inj (issued.symm.trans (strict_state geom real current motif d cs native strict))
  simpa only [same] using row

end TetraStereo.Engine.RingOxaziridinePublication
assert_kernel_only TetraStereo.Engine.RingOxaziridinePublication.motif_gates
assert_kernel_only TetraStereo.Engine.RingOxaziridinePublication.motif_selected
assert_kernel_only TetraStereo.Engine.RingOxaziridinePublication.occurrence
assert_kernel_only TetraStereo.Engine.RingOxaziridinePublication.stored
assert_kernel_only TetraStereo.Engine.RingOxaziridinePublication.strict_state
assert_kernel_only TetraStereo.Engine.RingOxaziridinePublication.strict_root
assert_kernel_only TetraStereo.Engine.RingOxaziridinePublication.strict_stored
