import TetraStereo.Engine.RingAtomicSecondShell
import TetraStereo.Engine.RingAtomicNeighborOrder
import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.OneCenter.LocalizedContextCyclicReaderBridge

/-! Physical second-shell incidence for actual incoming-cut cursors. -/
set_option autoImplicit false
noncomputable section
namespace TetraStereo.Engine.RingSecondShellIncidence
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingAtomicSecondShell (LocalGuard)

/-- The atom projection is total on every real carrier node. -/
def atomOf (i : Input) (q : Arm i) : i.certified.Atom :=
  q.occurrence.val.node.current?.getD q.occurrence.val.root

private theorem observed (i : Input)
    (single : i.certified.moleculeGraph.SimpleBonded)
    (acyclic : i.certified.moleculeGraph.Acyclic) (q : Arm i) :
    q.occurrence.val.node.current? = some (atomOf i q) := by
  obtain ⟨a,p,h,_⟩ := i.certified.carrierOccurrence_realPath single acyclic q.occurrence
  simp [atomOf,h]

/-- In an acyclic single-bond graph, every actual incoming-cut arm has exactly
one child for each physical neighbor except the incoming atom. The incoming
coordinate may be rootward or outward in the original carrier. -/
def acyclicGuard (i : Input)
    (single : i.certified.moleculeGraph.SimpleBonded)
    (acyclic : i.certified.moleculeGraph.Acyclic)
    (q : Arm i) (previous : Site i)
    (incoming : q.previous? = some previous)
    (sameRoot : q.occurrence.val.root = previous.val.root)
    (focus atom : i.certified.Atom)
    (current : q.occurrence.val.node.current? = some atom)
    (parent : previous.val.node.current? = some focus) : LocalGuard i q focus atom := by
  classical
  let children := i.certified.executableLocalizedRerootChildren q
  have computed := i.certified.localizedRerootChildren?_eq_some_executable q
  have incidence := i.certified.localizedRerootChildren?_current_iff_adjacent_of_previous
    single acyclic (by omega) q previous incoming sameRoot current parent children computed
  have injective := i.certified.localizedRerootChildren?_current_injective
    single acyclic q children computed
  refine ⟨current,atomOf i,(fun c => RingAtomicNeighborOrder.record i (atomOf i c)),?_,?_,?_⟩
  · intro c _
    exact observed i single acyclic c
  · intro c _
    exact RingAtomicNeighborOrder.written i (atomOf i c)
  · have nodup : (children.map (atomOf i)).Nodup := by
      apply List.Nodup.map_on _ (i.certified.executableLocalizedRerootChildren_nodup q)
      intro a ha b hb eqn
      apply injective a ha b hb
      rw [observed i single acyclic a,observed i single acyclic b,eqn]
    apply (List.perm_ext_iff_of_nodup nodup (Finset.nodup_toList _)).mpr
    intro a
    simp only [List.mem_map,Finset.mem_toList,Finset.mem_erase,MoleculeGraph.mem_neighborFinset]
    constructor
    · rintro ⟨c,hc,rfl⟩
      have h := (incidence (atomOf i c)).mp ⟨c,hc,observed i single acyclic c⟩
      exact ⟨h.2,h.1⟩
    · rintro ⟨ne,adj⟩
      obtain ⟨c,hc,cur⟩ := (incidence a).mpr ⟨adj,ne⟩
      refine ⟨c,hc,?_⟩
      simp [atomOf,cur]

/-- In a ring, a real arm has the same physical guard provided its incoming
coordinate is an actual uncut carrier neighbor. Closure duplicates are retained:
the uncut neighbor equivalence counts them by represented atom, once each. -/
def realGuard (i : Input)
    (single : i.certified.moleculeGraph.SimpleBonded)
    (q : Arm i) (previous : Site i)
    (incoming : q.previous? = some previous)
    (previousNeighbor : previous.val ∈ i.certified.localizedRerootNeighborFrames
      (fuel := i.certified.certified.input.molecule.atomCount + 1) q.occurrence.val)
    (focus atom : i.certified.Atom)
    (real : q.occurrence.val.node.provenance = .realAtom)
    (current : q.occurrence.val.node.current? = some atom)
    (parent : previous.val.node.current? = some focus) : LocalGuard i q focus atom := by
  apply Classical.choice
  classical
  let root : Arm i := ⟨q.occurrence,none⟩
  let children := i.certified.executableLocalizedRerootChildren q
  have existence := i.certified.simpleBond_realAtom_rerootChildren_neighborEquiv
    single (by omega) q.occurrence atom ⟨real,current⟩
  let uncut := Classical.choose existence
  let e := Classical.choose (Classical.choose_spec existence)
  have computed := (Classical.choose_spec (Classical.choose_spec existence)).1
  have spec := (Classical.choose_spec (Classical.choose_spec existence)).2
  have frames := (i.certified.simpleBond_realCenter_childFrames q.occurrence real uncut computed).1
  have inj := i.certified.simpleBond_realAtom_rerootChildren_current_injective
    single q.occurrence atom ⟨real,current⟩ uncut computed
  have uncutCurrent (u : Arm i) (hu : u ∈ uncut) :
      u.occurrence.val.node.current? = some (atomOf i u) := by
    have h := spec ⟨u,hu⟩
    change u.occurrence.val.node.current? = some ((e ⟨u,hu⟩).val) at h
    simp only [atomOf,h,Option.getD_some]
  have embed (c : Arm i) (hc : c ∈ children) :
      ∃ u ∈ uncut, u.occurrence = c.occurrence := by
    have h := (i.certified.executableLocalizedRerootChildren_mem_iff q c).mp hc
    have neighbor := ((i.certified.mem_intendedLocalizedRerootChildFrames_iff q _).mp h.2).2.1
    rw [←frames,List.mem_map] at neighbor
    obtain ⟨u,hu,eqn⟩ := neighbor
    exact ⟨u,hu,Subtype.ext eqn⟩
  have cutCurrent (c : Arm i) (hc : c ∈ children) :
      c.occurrence.val.node.current? = some (atomOf i c) := by
    obtain ⟨u,hu,eqn⟩ := embed c hc
    simpa [atomOf,eqn] using uncutCurrent u hu
  obtain ⟨p,hp,pe⟩ : ∃ p ∈ uncut, p.occurrence = previous := by
    rw [←frames,List.mem_map] at previousNeighbor
    obtain ⟨p,hp,eqn⟩ := previousNeighbor
    exact ⟨p,hp,Subtype.ext eqn⟩
  have cut_iff (u : Arm i) (hu : u ∈ uncut) :
      u.occurrence.val.address ≠ previous.val.address ↔ atomOf i u ≠ focus := by
    constructor
    · intro different same
      have eqn := inj u hu p hp (by rw [uncutCurrent u hu,same,pe,parent])
      exact different (by rw [eqn,pe])
    · intro different same
      have roots := i.certified.localizedRerootChildren?_root_eq root uncut computed
      have eqn := i.certified.declarativeLocalizedOccurrence_functional_at_root_address
        ((i.certified.mem_localizedOccurrences_iff _ _).mp u.occurrence.property)
        ((i.certified.mem_localizedOccurrences_iff _ _).mp previous.property)
        ((roots u hu).trans ((roots p hp).symm.trans (congrArg (fun o => o.val.root) pe))) same
      have h : some (atomOf i u) = some focus := by
        rw [←uncutCurrent u hu,eqn,parent]
      exact different (Option.some.inj h)
  have lift (u : Arm i) (hu : u ∈ uncut) (off : atomOf i u ≠ focus) :
      ∃ c ∈ children, c.occurrence = u.occurrence := by
    let c : Arm i := ⟨u.occurrence,some q.occurrence⟩
    refine ⟨c,?_,rfl⟩
    apply (i.certified.executableLocalizedRerootChildren_mem_iff q c).mpr
    refine ⟨rfl,(i.certified.mem_intendedLocalizedRerootChildFrames_iff q _).mpr ?_⟩
    refine ⟨i.certified.isDuplicateLeaf_eq_false_of_provenance_real _ real,?_,?_⟩
    · rw [←frames]
      exact List.mem_map.mpr ⟨u,hu,rfl⟩
    · intro prev hprev
      have eqn : prev = previous := Option.some.inj (hprev.symm.trans incoming)
      subst prev
      exact (cut_iff u hu).mpr off
  refine ⟨⟨current,atomOf i,(fun c => RingAtomicNeighborOrder.record i (atomOf i c)),cutCurrent,?_,?_⟩⟩
  · intro c _
    exact RingAtomicNeighborOrder.written i (atomOf i c)
  · have nodup : (children.map (atomOf i)).Nodup := by
      apply List.Nodup.map_on _ (i.certified.executableLocalizedRerootChildren_nodup q)
      intro a ha b hb eqn
      obtain ⟨u,hu,ue⟩ := embed a ha
      obtain ⟨v,hv,ve⟩ := embed b hb
      have uv := inj u hu v hv (by rw [ue,ve,cutCurrent a ha,cutCurrent b hb,eqn])
      apply LocalizedRerootCursor.ext i.certified (ue.symm.trans (uv ▸ ve))
      exact (i.certified.executableLocalizedRerootChildren_previous q a ha).trans
        (i.certified.executableLocalizedRerootChildren_previous q b hb).symm
    apply (List.perm_ext_iff_of_nodup nodup (Finset.nodup_toList _)).mpr
    intro a
    simp only [List.mem_map,Finset.mem_toList,Finset.mem_erase,MoleculeGraph.mem_neighborFinset]
    constructor
    · rintro ⟨c,hc,rfl⟩
      obtain ⟨u,hu,ue⟩ := embed c hc
      have ec := spec ⟨u,hu⟩
      have same : (e ⟨u,hu⟩).val = atomOf i c :=
        Option.some.inj (ec.symm.trans (ue ▸ cutCurrent c hc))
      have h := (i.certified.executableLocalizedRerootChildren_mem_iff q c).mp hc
      have off := ((i.certified.mem_intendedLocalizedRerootChildFrames_iff q _).mp h.2).2.2 previous incoming
      have ne := (cut_iff u hu).mp (ue ▸ off)
      exact ⟨by simpa [atomOf,ue] using ne, same ▸ (e ⟨u,hu⟩).property⟩
    · rintro ⟨ne,adj⟩
      obtain ⟨⟨u,hu⟩,eu⟩ := e.surjective ⟨a,adj⟩
      have ua : atomOf i u = a := by
        have h := spec ⟨u,hu⟩
        rw [eu] at h
        change u.occurrence.val.node.current? = some a at h
        simp only [atomOf,h,Option.getD_some]
      obtain ⟨c,hc,ce⟩ := lift u hu (ua ▸ ne)
      exact ⟨c,hc,by simpa [atomOf,ce] using ua⟩

/-- A visited nonparent graph neighbor becomes a terminal closure leaf in the
actual cut second layer whenever it differs from the incoming atom. Thus the
closure is retained even though it has no descendants. -/
theorem closure_survives (i : Input) (q : Arm i) (previous : Site i)
    (incoming : q.previous? = some previous)
    (sameRoot : q.occurrence.val.root = previous.val.root)
    (center : i.certified.TetrahedralCenter)
    (real : q.occurrence.val.node.provenance = .realAtom)
    (current : q.occurrence.val.node.current? = some center.val)
    (focus w : i.certified.Atom) (parent : previous.val.node.current? = some focus)
    (adjacent : i.certified.moleculeGraph.Adj center.val w)
    (visited : w ∈ q.occurrence.val.node.history)
    (notParent : q.occurrence.val.node.parent? ≠ some w) (off : w ≠ focus) :
    ∃ c ∈ i.certified.executableLocalizedRerootChildren q,
      c.occurrence.val.node.current? = some w ∧
      c.occurrence.val.node.provenance = .ringDuplicate (q.occurrence.val.node.duplicateRootDistance w) ∧
      i.certified.executableLocalizedRerootChildren c = [] := by
  obtain ⟨uncut,u,computed,hu,cu,_,provenance,leaf,_⟩ :=
    i.certified.simpleBond_realCenter_visitedNeighbor_terminalRingDuplicate
      (by omega) q.occurrence center ⟨real,current⟩ adjacent visited notParent
  have frame := (i.certified.simpleBond_realCenter_childFrames q.occurrence real uncut computed).1
  have different : u.occurrence.val.address ≠ previous.val.address := by
    intro same
    have roots := i.certified.localizedRerootChildren?_root_eq
      (⟨q.occurrence,none⟩ : Arm i) uncut computed u hu
    have eqn := i.certified.declarativeLocalizedOccurrence_functional_at_root_address
      ((i.certified.mem_localizedOccurrences_iff _ _).mp u.occurrence.property)
      ((i.certified.mem_localizedOccurrences_iff _ _).mp previous.property)
      (roots.trans sameRoot) same
    exact off (Option.some.inj (cu.symm.trans (eqn ▸ parent)))
  let c : Arm i := ⟨u.occurrence,some q.occurrence⟩
  refine ⟨c,?_,cu,provenance,?_⟩
  · apply (i.certified.executableLocalizedRerootChildren_mem_iff q c).mpr
    refine ⟨rfl,(i.certified.mem_intendedLocalizedRerootChildFrames_iff q _).mpr ?_⟩
    refine ⟨i.certified.isDuplicateLeaf_eq_false_of_provenance_real _ real,?_,?_⟩
    · rw [←frame]
      exact List.mem_map.mpr ⟨u,hu,rfl⟩
    · intro prev hprev
      have eqn : prev = previous := Option.some.inj (hprev.symm.trans incoming)
      simpa [eqn] using different
  · simp [executableLocalizedRerootChildren,intendedLocalizedRerootChildFrames,c,leaf]

/-- Duplicate endpoints are terminal before the incoming cut is applied. -/
theorem duplicate_terminal {i : Input} (q : Arm i)
    (leaf : q.occurrence.val.node.isDuplicateLeaf = true) :
    i.certified.executableLocalizedRerootChildren q = [] := by
  simp [executableLocalizedRerootChildren,intendedLocalizedRerootChildFrames,leaf]

/-- Single-bond carrier endpoints are real atoms or terminal ring duplicates;
no placeholder or multiple-bond-copy case is left open. -/
theorem nonreal_terminal {i : Input}
    (single : i.certified.moleculeGraph.SimpleBonded) (q : Arm i)
    (nonreal : q.occurrence.val.node.provenance ≠ .realAtom) :
    i.certified.executableLocalizedRerootChildren q = [] := by
  rcases i.certified.carrierOccurrence_provenance_simple_or_ring single q.occurrence with real | ⟨d,ring⟩
  · exact (nonreal real).elim
  · apply duplicate_terminal q
    simp [OfficialCIPNode.isDuplicateLeaf,ring,OfficialCIPNodeProvenance.isDuplicateLeaf]

open RingRetainedChemicalTrace
open private source_children from TetraStereo.Engine.RingChildKeyRecovery
open private makeColumn byDescending from TetraStereo.Engine.RingRetainedChemicalTrace

/-- The shallow second row of a terminal key is the empty word. -/
theorem terminal_second_row {i : Input} {q : Arm i} {k : Key}
    (terminal : i.certified.executableLocalizedRerootChildren q = [])
    (read : key? i q = some k) : k.atomic.word[1]? = some [] := by
  obtain ⟨o,h,_,_⟩ := source_children read
  have keys : RingChildKeyRecovery.childKeys i q = [] := by
    simp [RingChildKeyRecovery.childKeys,terminal]
  rw [h,keys]
  simp [assemble,makeColumn,byDescending]

/-- Direct empty second-row formula for every non-real single-bond endpoint. -/
theorem nonreal_second_row {i : Input} {q : Arm i} {k : Key}
    (single : i.certified.moleculeGraph.SimpleBonded)
    (nonreal : q.occurrence.val.node.provenance ≠ .realAtom)
    (read : key? i q = some k) : k.atomic.word[1]? = some [] :=
  terminal_second_row (nonreal_terminal single q nonreal) read

/-- Complete second-shell word for any actual incoming-cut arm. A real endpoint
uses the physical neighbor row; a closure endpoint contributes an empty row. -/
def secondWord (i : Input) (q : Arm i) (focus atom : i.certified.Atom) : List Nat :=
  if q.occurrence.val.node.provenance = .realAtom then RingAtomicSecondShell.graphWord i focus atom else []

/-- Every actual ligand is covered, including retained inward arms and terminal
closure leaves. All correspondence is derived from the raw carrier and graph. -/
theorem all_second_row (i : Input)
    (single : i.certified.moleculeGraph.SimpleBonded)
    (q : Arm i) (previous : Site i)
    (incoming : q.previous? = some previous)
    (previousNeighbor : previous.val ∈ i.certified.localizedRerootNeighborFrames
      (fuel := i.certified.certified.input.molecule.atomCount + 1) q.occurrence.val)
    (focus atom : i.certified.Atom)
    (current : q.occurrence.val.node.current? = some atom)
    (parent : previous.val.node.current? = some focus)
    {k : Key} (read : key? i q = some k) :
    k.atomic.word[1]? = some (secondWord i q focus atom) := by
  unfold secondWord
  split
  · rename_i real
    exact RingAtomicSecondShell.second_row
      (realGuard i single q previous incoming previousNeighbor focus atom real current parent) read
  · rename_i nonreal
    exact terminal_second_row (nonreal_terminal single q nonreal) read

/-- Each surviving physical neighbor contributes one entry, including terminal
ring-closure duplicates. No extra entry is added merely for closure provenance. -/
theorem guarded_length {i : Input} {q : Arm i} {focus atom : i.certified.Atom}
    (g : LocalGuard i q focus atom) :
    (i.certified.executableLocalizedRerootChildren q).length =
      ((i.certified.moleculeGraph.neighborFinset atom).erase focus).card := by
  simpa using g.physical.length_eq

/-- In particular, a closure leaf representing a surviving neighbor contributes
exactly one occurrence to the second-shell multiset. -/
theorem guarded_count_one {i : Input} {q : Arm i} {focus atom : i.certified.Atom}
    (g : LocalGuard i q focus atom) (w : i.certified.Atom)
    (adjacent : i.certified.moleculeGraph.Adj atom w) (off : w ≠ focus) :
    ((i.certified.executableLocalizedRerootChildren q).map g.childAtom).count w = 1 := by
  classical
  apply List.count_eq_one_of_mem (g.physical.nodup_iff.mpr (Finset.nodup_toList _))
  apply g.physical.mem_iff.mpr
  simp [adjacent,off]

/-- Exact shallow atomic row, now with the physical guard derived from graph
acyclicity and the actual incoming occurrence rather than assumed. -/
theorem acyclic_second_row (i : Input)
    (single : i.certified.moleculeGraph.SimpleBonded)
    (acyclic : i.certified.moleculeGraph.Acyclic)
    (q : Arm i) (previous : Site i)
    (incoming : q.previous? = some previous)
    (sameRoot : q.occurrence.val.root = previous.val.root)
    (focus atom : i.certified.Atom)
    (current : q.occurrence.val.node.current? = some atom)
    (parent : previous.val.node.current? = some focus)
    {k : RingRetainedChemicalTrace.Key}
    (read : RingRetainedChemicalTrace.key? i q = some k) :
    k.atomic.word[1]? = some (RingAtomicSecondShell.graphWord i focus atom) :=
  RingAtomicSecondShell.second_row
    (acyclicGuard i single acyclic q previous incoming sameRoot focus atom current parent) read

end TetraStereo.Engine.RingSecondShellIncidence
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.acyclicGuard
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.acyclic_second_row
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.realGuard
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.closure_survives
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.nonreal_terminal
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.terminal_second_row
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.all_second_row
assert_kernel_only TetraStereo.Engine.RingSecondShellIncidence.nonreal_second_row
